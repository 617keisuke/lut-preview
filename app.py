"""
LUT試用サイト — メインアプリケーション
Apple Log ProRes (.mov/.mp4/.mxf) + .cube LUT → H.264 MP4
出力: 素材のアスペクト比に合わせた白フレーム付き
"""
import glob
import json
import os
import re
import shutil
import subprocess
import threading
import time
import uuid
from datetime import date
from pathlib import Path
from flask import (
    Flask, Response, abort, jsonify,
    render_template, request, send_file, stream_with_context,
)
app = Flask(__name__)

# ─── 設定 ────────────────────────────────────────────────────────────────────
LUTS_DIR       = Path("luts")
LUTS_META      = Path("luts.json")
TMP_BASE       = Path("/tmp/lut_sessions")
MAX_UPLOAD_MB  = 500
MIN_DURATION   = 1.0
MAX_DURATION   = 3.0
OUTPUT_CRF     = 18
ALLOWED_EXTS   = {".mov", ".mp4", ".mxf"}
MAX_CONCURRENT = 2
DOWNLOAD_TTL   = 300

# フレーム設定
PAD         = 20    # 上・左・右 の余白（共通）
PAD_BOT     = 90    # 下の余白（キャプションテキスト用）
MAX_CONT_H  = 610   # コンテンツ最大高さ (PAD + MAX_CONT_H + PAD_BOT = 720)
MAX_CONT_W  = 1860  # コンテンツ最大幅
EDGE_FADE   = 18    # 映像端のフェード幅（px）

# ─────────────────────────────────────────────────────────────────────────────
TMP_BASE.mkdir(parents=True, exist_ok=True)
app.config["MAX_CONTENT_LENGTH"] = MAX_UPLOAD_MB * 1024 * 1024
_semaphore = threading.Semaphore(MAX_CONCURRENT)

# ═══════════════════════════════════════════════════════════════════
# LUTメタデータ管理
# ═══════════════════════════════════════════════════════════════════
def load_luts_meta():
    if LUTS_META.exists():
        with LUTS_META.open(encoding="utf-8") as f:
            return json.load(f)
    lut_files = sorted(LUTS_DIR.glob("*.cube"))
    luts = [{"id": f.stem, "file": f.name, "name": f.stem.replace("_", " "),
              "category": "other", "description": "", "price_jpy": None, "thumbnail": None}
            for f in lut_files]
    return {"luts": luts, "categories": [{"id": "other", "label": "すべて"}]}

# ═══════════════════════════════════════════════════════════════════
# 出力サイズ計算
# ═══════════════════════════════════════════════════════════════════
def compute_dims(video_w, video_h):
    """
    素材のアスペクト比を保ちつつ MAX_CONT_H × MAX_CONT_W に収める。
    上下左右のPADを加えた最終出力サイズを返す。
    縦動画は左右PADを上部PADと視覚的に揃えるため比例縮小する。
    すべて偶数に丸める（libx264 要件）。
    """
    ar = video_w / video_h
    cont_h = MAX_CONT_H
    cont_w = int(cont_h * ar)
    if cont_w > MAX_CONT_W:
        cont_w = MAX_CONT_W
        cont_h = int(cont_w / ar)
    cont_w = cont_w & ~1          # 偶数化
    cont_h = cont_h & ~1
    # 縦動画は左右PADを上部PADと視覚的に同じ太さにする
    # pad_side / out_w ≈ PAD / out_h → pad_side ≈ PAD * cont_w / cont_h
    if cont_h > cont_w:
        pad_side = max(8, int(PAD * cont_w / cont_h)) & ~1
    else:
        pad_side = PAD
    out_w  = (cont_w + pad_side * 2) & ~1   # 出力も偶数保証
    out_h  = (cont_h + PAD + PAD_BOT) & ~1
    return cont_w, cont_h, out_w, out_h, pad_side

# ═══════════════════════════════════════════════════════════════════
# フォント検索
# ═══════════════════════════════════════════════════════════════════
def find_cjk_font(size):
    """明朝体優先で日本語フォントを検索"""
    from PIL import ImageFont
    candidates = [
        "/System/Library/Fonts/ヒラギノ明朝 ProN W3.ttc",
        "/System/Library/Fonts/ヒラギノ明朝 ProN.ttc",
        "/System/Library/Fonts/Hiragino Mincho ProN W3.ttc",
        "/Library/Fonts/ヒラギノ明朝 ProN W3.ttc",
        "/System/Library/Fonts/YuMincho.ttc",
        "/Library/Fonts/YuMincho.ttc",
        "/System/Library/Fonts/ヒラギノ角ゴシック W3.ttc",
        "/System/Library/Fonts/ヒラギノ角ゴ ProN W3.ttc",
    ]
    for pat in ["/System/Library/Fonts/ヒラギノ明朝*.ttc",
                "/Library/Fonts/ヒラギノ明朝*.ttc",
                "/System/Library/Fonts/Yu*.ttc",
                "/System/Library/Fonts/ヒラギノ*.ttc"]:
        candidates.extend(glob.glob(pat))
    for fp in candidates:
        if os.path.exists(fp):
            try:
                return ImageFont.truetype(fp, size)
            except Exception:
                continue
    return ImageFont.load_default()

def find_latin_font(size, bold=False):
    """ラテン文字フォント（キャプション用）"""
    from PIL import ImageFont
    candidates = [
        ("/System/Library/Fonts/HelveticaNeue.ttc", 1 if bold else 0),
        ("/System/Library/Fonts/Helvetica.ttc",     0),
        ("/Library/Fonts/Arial.ttf",                0),
        ("/System/Library/Fonts/Arial.ttf",         0),
    ]
    for fp, idx in candidates:
        if os.path.exists(fp):
            try:
                return ImageFont.truetype(fp, size, index=idx)
            except Exception:
                continue
    return find_cjk_font(size)

# ═══════════════════════════════════════════════════════════════════
# テキストオーバーレイ生成（Pillow）
# ═══════════════════════════════════════════════════════════════════
def create_text_overlay(overlay_path, lut_name, description="",
                        caption_type="date", shot_date="",
                        out_w=1920, out_h=1080, cont_w=1860, cont_h=950, pad_side=PAD):
    """
    out_w × out_h の透明PNG を生成。
    ・横動画: 映像エリアを左右二分割 — 左にLUT名、右に説明文
    ・縦動画: 映像エリア中央にLUT名＋説明文を2行で中央揃え
    ・下部白ストリップ：キャプション中央配置
    """
    from PIL import Image, ImageDraw

    img  = Image.new("RGBA", (out_w, out_h), (0, 0, 0, 0))

    # ── テキスト描画 ──────────────────────────────────────────────
    draw = ImageDraw.Draw(img)

    is_portrait = cont_h > cont_w

    font_name = find_cjk_font(28 if is_portrait else 42)
    font_desc = find_cjk_font(20 if is_portrait else 32)

    video_cy = PAD + cont_h // 2
    video_cx = pad_side + cont_w // 2

    def draw_with_shadow(text, font, x, y, fill=(255, 255, 255, 220)):
        draw.text((x + 1, y + 1), text, font=font, fill=(0, 0, 0, 90))
        draw.text((x,     y    ), text, font=font, fill=fill)

    if is_portrait:
        # 縦動画: LUT名と説明文を中央に2行
        bb_name = draw.textbbox((0, 0), lut_name, font=font_name)
        name_w  = bb_name[2] - bb_name[0]
        name_h  = bb_name[3] - bb_name[1]

        if description:
            bb_desc = draw.textbbox((0, 0), description, font=font_desc)
            desc_w  = bb_desc[2] - bb_desc[0]
            desc_h  = bb_desc[3] - bb_desc[1]
            gap     = 26
            total_h = name_h + gap + desc_h
            name_x  = video_cx - name_w // 2
            name_y  = video_cy - total_h // 2
            desc_x  = video_cx - desc_w // 2
            desc_y  = name_y + name_h + gap
            draw_with_shadow(lut_name,    font_name, name_x, name_y)
            draw_with_shadow(description, font_desc, desc_x, desc_y)
        else:
            name_x = video_cx - name_w // 2
            name_y = video_cy - name_h // 2
            draw_with_shadow(lut_name, font_name, name_x, name_y)

    else:
        # 横動画: 左半分にLUT名、右半分に説明文（従来通り）
        left_cx  = pad_side + cont_w // 4
        right_cx = pad_side + cont_w * 3 // 4

        bb = draw.textbbox((0, 0), lut_name, font=font_name)
        name_w = bb[2] - bb[0]
        name_h = bb[3] - bb[1]
        name_x = left_cx - name_w // 2
        name_y = video_cy - name_h // 2
        draw_with_shadow(lut_name, font_name, name_x, name_y)

        if description:
            bb = draw.textbbox((0, 0), description, font=font_desc)
            desc_w = bb[2] - bb[0]
            desc_h = bb[3] - bb[1]
            desc_x = right_cx - desc_w // 2
            desc_y = video_cy - desc_h // 2
            draw_with_shadow(description, font_desc, desc_x, desc_y)

    # ── 下部キャプション ─────────────────────────────────────────
    if caption_type == "date":
        font_c       = find_latin_font(22, bold=True)
        caption_text = shot_date or ""
    elif caption_type == "shot_on_iphone":
        font_c       = find_latin_font(22, bold=True)
        caption_text = "Shot on iPhone"
    else:
        caption_text = ""

    if caption_text:
        bb      = draw.textbbox((0, 0), caption_text, font=font_c)
        cap_w   = bb[2] - bb[0]
        # bb[1] のオフセットを考慮して視覚的に中央に揃える
        strip_center = PAD + cont_h + PAD_BOT // 2
        cap_x   = (out_w - cap_w) // 2
        cap_y   = strip_center - (bb[1] + bb[3]) // 2
        draw.text((cap_x, cap_y), caption_text, font=font_c,
                  fill=(20, 20, 20, 255))

    img.save(str(overlay_path), "PNG")
    return True

# ═══════════════════════════════════════════════════════════════════
# ユーティリティ
# ═══════════════════════════════════════════════════════════════════
def get_video_info(path):
    result = subprocess.run(
        ["ffprobe", "-v", "quiet", "-print_format", "json", "-show_streams", str(path)],
        capture_output=True, text=True, timeout=30,
    )
    data = json.loads(result.stdout)
    for stream in data.get("streams", []):
        if stream.get("codec_type") == "video":
            w = stream.get("width", 0)
            h = stream.get("height", 0)
            # iPhoneの縦動画は rotate=90/270 メタデータで縦表示される
            # → 実際の表示サイズに合わせて width/height を入れ替える
            rotate = 0
            tags = stream.get("tags", {})
            if "rotate" in tags:
                try:
                    rotate = int(tags["rotate"])
                except (ValueError, TypeError):
                    pass
            for sd in stream.get("side_data_list", []):
                if sd.get("side_data_type") == "Display Matrix":
                    r = sd.get("rotation", 0)
                    if r:
                        rotate = int(r)
            if abs(rotate) in (90, 270):
                w, h = h, w
            return {
                "duration": float(stream.get("duration", 0)),
                "width":    w,
                "height":   h,
                "codec":    stream.get("codec_name", "unknown"),
            }
    raise ValueError("動画ストリームが見つかりません")

def cleanup_session(session_dir, delay=DOWNLOAD_TTL):
    def _delete():
        time.sleep(delay)
        shutil.rmtree(session_dir, ignore_errors=True)
    threading.Thread(target=_delete, daemon=True).start()

def build_ffmpeg_cmd(input_path, output_path, lut_path, trim_sec,
                     cont_w, cont_h, out_w, out_h, pad_side=PAD, overlay_path=None, exposure=0.0):
    lut_filter = "lut3d=file={}:interp=nearest".format(str(lut_path.resolve()))

    # 露出補正フィルター（0のときはスキップ）
    ev_filter = "exposure=exposure={:.2f}".format(exposure) if abs(exposure) > 0.01 else ""

    # スケール → 露出補正 → LUT適用（フレームなし・シンプル）
    steps = [
        "scale={cw}:{ch}:force_original_aspect_ratio=decrease:force_divisible_by=2".format(
            cw=cont_w, ch=cont_h)
    ]
    if ev_filter:
        steps.append(ev_filter)
    steps.append(lut_filter)
    steps.append("fps=24")
    vf = ",".join(steps)

    return [
        "ffmpeg", "-y",
        "-i", str(input_path),
        "-t", str(trim_sec),
        "-vf", vf,
        "-c:v", "libx264", "-preset", "ultrafast", "-crf", str(OUTPUT_CRF),
        "-pix_fmt", "yuv420p", "-an", "-movflags", "+faststart",
        "-progress", "pipe:2", "-nostats",
        str(output_path),
    ]

def parse_ffmpeg_time(line):
    m = re.search(r"out_time=(\d+):(\d+):([\d.]+)", line)
    if m:
        return int(m.group(1)) * 3600 + int(m.group(2)) * 60 + float(m.group(3))
    return None

def _write_state(path, data):
    path.write_text(json.dumps(data, ensure_ascii=False), encoding="utf-8")

def _read_state(path):
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return {"status": "waiting", "progress": 0}

# ═══════════════════════════════════════════════════════════════════
# ルーティング
# ═══════════════════════════════════════════════════════════════════
@app.route("/")
def index():
    return render_template("index.html")

@app.route("/api/luts")
def api_luts():
    meta      = load_luts_meta()
    available = {f.name for f in LUTS_DIR.glob("*.cube")}
    luts      = [l for l in meta["luts"] if l["file"] in available]
    return jsonify({"luts": luts, "categories": meta.get("categories", [])})

@app.route("/api/process", methods=["POST"])
def api_process():
    if "video" not in request.files:
        return jsonify({"error": "動画ファイルが見つかりません"}), 400
    video_file   = request.files["video"]
    lut_id       = request.form.get("lut_id", "").strip()
    caption_type = request.form.get("caption_type", "date")
    try:
        exposure = float(request.form.get("exposure", "0"))
        exposure = max(-1.0, min(1.0, exposure))  # クランプ
    except ValueError:
        exposure = 0.0

    if not lut_id:
        return jsonify({"error": "LUTを選択してください"}), 400
    if not re.match(r'^[A-Za-z0-9_\-]+$', lut_id):
        return jsonify({"error": "不正なLUT IDです"}), 400
    ext = Path(video_file.filename or "").suffix.lower()
    if ext not in ALLOWED_EXTS:
        return jsonify({"error": "対応フォーマット: .mov / .mp4 / .mxf"}), 400

    meta      = load_luts_meta()
    lut_entry = next((l for l in meta["luts"] if l["id"] == lut_id), None)
    if not lut_entry:
        return jsonify({"error": "選択されたLUTが見つかりません"}), 400
    lut_path = LUTS_DIR / lut_entry["file"]
    if not lut_path.exists():
        return jsonify({"error": "選択されたLUTが見つかりません"}), 400
    if not _semaphore.acquire(blocking=False):
        return jsonify({"error": "現在サーバーが混み合っています。しばらくしてからお試しください。"}), 503

    session_id  = uuid.uuid4().hex[:14]
    session_dir = TMP_BASE / session_id
    session_dir.mkdir(parents=True)
    input_path  = session_dir / "input{}".format(ext)
    output_path = session_dir / "preview.mp4"
    state_path  = session_dir / "state.json"

    _write_state(state_path, {"status": "uploading", "progress": 0})
    video_file.save(str(input_path))
    _write_state(state_path, {"status": "analyzing", "progress": 2})

    def _run():
        try:
            info     = get_video_info(input_path)
            duration = info["duration"]
            if duration < MIN_DURATION:
                _write_state(state_path, {
                    "status": "error",
                    "error":  "動画が短すぎます（{:.1f}秒）。{}秒以上のクリップが必要です。".format(
                        duration, int(MIN_DURATION)),
                })
                return

            trim_sec   = min(duration, MAX_DURATION)
            lut_disp   = lut_entry["name"]
            lut_desc   = lut_entry.get("description", "")
            shot_date  = date.today().strftime("%Y/%m/%d")

            # 素材アスペクト比に合わせて出力サイズを計算
            cont_w, cont_h, out_w, out_h, pad_side = compute_dims(info["width"], info["height"])

            process_input = input_path

            lut_tmp = session_dir / "lut.cube"
            shutil.copy2(str(lut_path), str(lut_tmp))

            cmd = build_ffmpeg_cmd(
                process_input, output_path, lut_tmp, trim_sec,
                cont_w, cont_h, out_w, out_h, pad_side,
                exposure=exposure,
            )
            _write_state(state_path, {"status": "processing", "progress": 5, "total_sec": trim_sec})

            proc = subprocess.Popen(
                cmd, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True)
            ffmpeg_log = []
            for raw_line in proc.stderr:
                ffmpeg_log.append(raw_line.rstrip())
                t = parse_ffmpeg_time(raw_line.strip())
                if t is not None and trim_sec > 0:
                    pct = min(95, int(t / trim_sec * 90) + 5)
                    _write_state(state_path, {
                        "status": "processing", "progress": pct, "total_sec": trim_sec})
            proc.wait(timeout=300)

            if proc.returncode != 0 or not output_path.exists():
                app.logger.error("ffmpeg failed (code %s):\n%s",
                                 proc.returncode, "\n".join(ffmpeg_log[-30:]))
                _write_state(state_path, {"status": "error", "error": "動画処理中にエラーが発生しました"})
                return

            file_size_mb = round(output_path.stat().st_size / 1024 / 1024, 1)
            _write_state(state_path, {
                "status":        "done",
                "progress":      100,
                "session_id":    session_id,
                "download_url":  "/download/{}".format(session_id),
                "lut_name":      lut_disp,
                "duration_sec":  round(trim_sec, 2),
                "output_format": "H.264 {}×{} MP4".format(out_w, out_h),
                "file_size_mb":  file_size_mb,
                "source_codec":  info["codec"],
            })
            cleanup_session(session_dir, delay=DOWNLOAD_TTL)

        except subprocess.TimeoutExpired:
            _write_state(state_path, {"status": "error", "error": "処理タイムアウト（2分超過）"})
        except Exception as e:
            app.logger.exception(e)
            _write_state(state_path, {"status": "error", "error": "予期しないエラーが発生しました"})
        finally:
            _semaphore.release()
            if input_path.exists():
                input_path.unlink(missing_ok=True)

    threading.Thread(target=_run, daemon=True).start()
    return jsonify({"session_id": session_id}), 202

@app.route("/api/progress/<session_id>")
def api_progress(session_id):
    if not re.match(r'^[a-f0-9]{14}$', session_id):
        abort(400)
    state_path = TMP_BASE / session_id / "state.json"
    def _generate():
        for _ in range(300):
            state = _read_state(state_path)
            yield "data: {}\n\n".format(json.dumps(state, ensure_ascii=False))
            if state.get("status") in ("done", "error"):
                return
            time.sleep(1)
        yield "data: {}\n\n".format(json.dumps({"status": "error", "error": "タイムアウト"}))
    return Response(
        stream_with_context(_generate()),
        mimetype="text/event-stream",
        headers={"Cache-Control": "no-cache", "X-Accel-Buffering": "no"},
    )

@app.route("/download/<session_id>")
def download(session_id):
    if not re.match(r'^[a-f0-9]{14}$', session_id):
        abort(400)
    output_path = TMP_BASE / session_id / "preview.mp4"
    if not output_path.exists():
        abort(404)
    return send_file(
        str(output_path),
        mimetype="video/mp4",
        as_attachment=False,
        download_name="lut_preview_{}.mp4".format(session_id[:8]),
    )

# ═══════════════════════════════════════════════════════════════════
if __name__ == "__main__":
    app.run(debug=True, host="0.0.0.0", port=5001, threaded=True)
