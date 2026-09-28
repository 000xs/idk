import os
import sys
import uuid
import asyncio
import logging
import secrets
import aiofiles
from pathlib import Path, PurePosixPath
from urllib.parse import quote

from fastapi import (
    FastAPI,
    UploadFile,
    File,
    HTTPException,
    Request,
    Depends,
    status,
)
from fastapi.responses import RedirectResponse, HTMLResponse
from fastapi.security import HTTPBasic, HTTPBasicCredentials

from huggingface_hub import HfApi
from telethon import TelegramClient, events
from telethon.sessions import MemorySession


# ─────────────────────────────────────────
# Logging
# ─────────────────────────────────────────
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s - %(levelname)s - %(message)s",
    handlers=[logging.StreamHandler(sys.stdout)],
)
logger = logging.getLogger("MyCloud")


# ─────────────────────────────────────────
# Secrets / Config
# ─────────────────────────────────────────
HF_TOKEN = os.environ["HF_TOKEN"].strip()
HF_REPO = os.environ["HF_REPO"].strip()

API_ID = int(os.environ["TG_API_ID"])
API_HASH = os.environ["TG_API_HASH"].strip()
BOT_TOKEN = os.environ["TG_BOT_TOKEN"].strip()

PUBLIC_BASE_URL = os.getenv("PUBLIC_BASE_URL", "").strip().rstrip("/")

ADMIN_USERNAME = os.getenv("ADMIN_USERNAME", "").strip()
ADMIN_PASSWORD = os.getenv("ADMIN_PASSWORD", "").strip()

AUTH_ENABLED = bool(ADMIN_USERNAME and ADMIN_PASSWORD)

PROTECT_DOWNLOADS = (
    os.getenv("PROTECT_DOWNLOADS", "false").strip().lower()
    in {"1", "true", "yes", "on"}
)

MAX_FILE_SIZE = 2 * 1024 * 1024 * 1024  # 2 GB

TMP_DIR = Path(os.getenv("TMP_DIR", "/tmp/mycloud"))
TMP_DIR.mkdir(parents=True, exist_ok=True)

if not AUTH_ENABLED:
    logger.warning(
        "ADMIN_USERNAME / ADMIN_PASSWORD not set. "
        "Web UI and upload endpoints are NOT protected."
    )

if PROTECT_DOWNLOADS and not AUTH_ENABLED:
    logger.warning(
        "PROTECT_DOWNLOADS=true but auth is disabled. "
        "Download protection will not work properly."
    )


# ─────────────────────────────────────────
# Clients
# ─────────────────────────────────────────
hf_api = HfApi(token=HF_TOKEN)
app = FastAPI(title="My Cloud")
client = TelegramClient(MemorySession(), API_ID, API_HASH)

security = HTTPBasic(realm="My Cloud")
security_optional = HTTPBasic(auto_error=False, realm="My Cloud")


# ─────────────────────────────────────────
# Auth helpers
# ─────────────────────────────────────────
def validate_credentials(username: str, password: str) -> bool:
    if not AUTH_ENABLED:
        return True

    ok_user = secrets.compare_digest(
        username.encode("utf-8"),
        ADMIN_USERNAME.encode("utf-8"),
    )
    ok_pass = secrets.compare_digest(
        password.encode("utf-8"),
        ADMIN_PASSWORD.encode("utf-8"),
    )

    return ok_user and ok_pass


def require_auth(credentials: HTTPBasicCredentials = Depends(security)):
    if not AUTH_ENABLED:
        return "anonymous"

    if not validate_credentials(credentials.username, credentials.password):
        raise HTTPException(
            status_code=status.HTTP_401_UNAUTHORIZED,
            detail="Invalid username or password",
            headers={"WWW-Authenticate": "Basic"},
        )

    return credentials.username


def optional_download_auth(
    credentials: HTTPBasicCredentials | None = Depends(security_optional),
):
    """
    Used for /cdn and /download.

    If PROTECT_DOWNLOADS=false:
        public links work without login.

    If PROTECT_DOWNLOADS=true:
        login required.
    """
    if not PROTECT_DOWNLOADS:
        return "public"

    if credentials is None:
        raise HTTPException(
            status_code=status.HTTP_401_UNAUTHORIZED,
            detail="Login required for downloads",
            headers={"WWW-Authenticate": "Basic"},
        )

    if not validate_credentials(credentials.username, credentials.password):
        raise HTTPException(
            status_code=status.HTTP_401_UNAUTHORIZED,
            detail="Invalid username or password",
            headers={"WWW-Authenticate": "Basic"},
        )

    return credentials.username


# ─────────────────────────────────────────
# Path / URL helpers
# ─────────────────────────────────────────
def safe_relative_path(filename: str) -> str:
    """
    Prevent path traversal attacks.
    Allows normal filenames and relative paths like folder/file.mp4,
    but blocks ../ and absolute paths.
    """
    filename = (filename or "").strip()

    if not filename:
        raise HTTPException(status_code=400, detail="Invalid filename")

    path = PurePosixPath(filename)

    if (
        path.is_absolute()
        or ".." in path.parts
        or path.as_posix() in {"", "."}
    ):
        raise HTTPException(status_code=400, detail="Invalid file path")

    return path.as_posix()


def encode_path(path: str) -> str:
    return quote(path, safe="/")


def direct_hf_url(filename: str, download: bool = False) -> str:
    safe = safe_relative_path(filename)
    encoded = encode_path(safe)

    url = f"https://huggingface.co/datasets/{HF_REPO}/resolve/main/{encoded}"

    if download:
        url += "?download=true"

    return url


def get_base_url(request: Request | None = None) -> str:
    """
    Resolve public base URL.

    Priority:
    1. PUBLIC_BASE_URL secret
    2. Request headers / host, if available
    3. Empty string
    """
    if PUBLIC_BASE_URL:
        return PUBLIC_BASE_URL

    if request is None:
        return ""

    raw_proto = request.headers.get("x-forwarded-proto") or request.url.scheme
    raw_host = (
        request.headers.get("x-forwarded-host")
        or request.headers.get("host")
        or request.url.netloc
    )

    proto = raw_proto.split(",")[0].strip() if raw_proto else ""
    host = raw_host.split(",")[0].strip() if raw_host else ""

    if not proto or not host:
        return ""

    return f"{proto}://{host}".rstrip("/")


def build_download_url(filename: str, request: Request | None = None) -> str:
    safe = safe_relative_path(filename)
    encoded = encode_path(safe)

    base = get_base_url(request)

    if base:
        return f"{base}/download/{encoded}"

    return direct_hf_url(filename, download=True)


def build_cdn_url(filename: str, request: Request | None = None) -> str:
    safe = safe_relative_path(filename)
    encoded = encode_path(safe)

    base = get_base_url(request)

    if base:
        return f"{base}/cdn/{encoded}"

    return direct_hf_url(filename, download=False)


# ─────────────────────────────────────────
# Embedded Web UI
# No secrets are hardcoded here.
# ─────────────────────────────────────────
INDEX_HTML = """<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>My Cloud</title>
<style>
*{margin:0;padding:0;box-sizing:border-box}
body{font-family:'Segoe UI',system-ui,sans-serif;background:#0a0a0f;color:#e0e0e0;min-height:100vh}
.header{text-align:center;padding:40px 20px 20px}
.header h1{font-size:2rem;background:linear-gradient(135deg,#6366f1,#a855f7,#ec4899);-webkit-background-clip:text;-webkit-text-fill-color:transparent}
.header p{color:#888;margin-top:8px;font-size:.95rem}
.container{max-width:700px;margin:0 auto;padding:20px}
.drop-zone{border:2px dashed #333;border-radius:16px;padding:60px 20px;text-align:center;cursor:pointer;transition:all .3s;background:#12121a}
.drop-zone:hover,.drop-zone.dragover{border-color:#6366f1;background:#1a1a2e}
.drop-zone .icon{font-size:3rem;margin-bottom:12px}
.drop-zone p{color:#888;font-size:.9rem}
.drop-zone .browse{color:#6366f1;text-decoration:underline;cursor:pointer}
#fileInput{display:none}
.progress-wrap{display:none;margin-top:20px;background:#12121a;border-radius:12px;padding:20px}
.progress-bar-bg{width:100%;height:8px;background:#222;border-radius:4px;overflow:hidden;margin-top:10px}
.progress-bar-fill{height:100%;width:0%;background:linear-gradient(90deg,#6366f1,#a855f7);border-radius:4px;transition:width .3s}
.progress-info{display:flex;justify-content:space-between;font-size:.85rem;color:#888;margin-top:8px}
.result{display:none;margin-top:20px;background:#12121a;border:1px solid #1e1e2e;border-radius:12px;padding:20px}
.result .fname{font-weight:600;color:#fff}
.result .fsize{color:#888;font-size:.85rem;margin-top:4px}
.link-row{display:flex;gap:8px;margin-top:12px}
.link-row input[type=text]{flex:1;background:#0a0a0f;border:1px solid #333;border-radius:8px;padding:10px 14px;color:#a855f7;font-size:.85rem;outline:none}
.link-label{font-size:.75rem;color:#666;margin-top:10px}
.btn-copy{background:#6366f1;color:#fff;border:none;border-radius:8px;padding:10px 18px;cursor:pointer;font-size:.85rem;transition:background .2s}
.btn-copy:hover{background:#4f46e5}
.files-section{margin-top:30px}
.files-section h2{font-size:1.1rem;color:#aaa;margin-bottom:12px}
.file-list{list-style:none}
.file-list li{background:#12121a;border:1px solid #1e1e2e;border-radius:10px;padding:12px 16px;margin-bottom:8px;display:flex;justify-content:space-between;align-items:center;gap:10px;font-size:.9rem;flex-wrap:wrap}
.file-list li .fn{flex:1;word-break:break-all}
.file-list li a{color:#6366f1;text-decoration:none;font-size:.8rem}
.file-list li a:hover{text-decoration:underline}
.footer{text-align:center;padding:30px;color:#444;font-size:.8rem}
.toast{position:fixed;bottom:20px;right:20px;background:#6366f1;color:#fff;padding:12px 20px;border-radius:10px;font-size:.9rem;display:none;z-index:999}
</style>
</head>
<body>
<div class="header">
  <h1>☁️ My Cloud</h1>
  <p>Upload files → Get instant download link</p>
</div>
<div class="container">
  <div class="drop-zone" id="dropZone">
    <div class="icon">📁</div>
    <p>Drag &amp; drop your file here<br>or <span class="browse" onclick="document.getElementById('fileInput').click()">browse</span></p>
    <p style="margin-top:8px;font-size:.75rem;color:#555">Max 2GB • Any file type</p>
  </div>
  <input type="file" id="fileInput">
  <div class="progress-wrap" id="progressWrap">
    <div id="progressText">Uploading...</div>
    <div class="progress-bar-bg"><div class="progress-bar-fill" id="progressBar"></div></div>
    <div class="progress-info">
      <span id="progressPercent">0%</span>
      <span id="progressSize">0 MB / 0 MB</span>
    </div>
  </div>
  <div class="result" id="resultBox">
    <div class="fname" id="resName"></div>
    <div class="fsize" id="resSize"></div>
    <div class="link-label">🔗 Download Link</div>
    <div class="link-row">
      <input type="text" id="resDownload" readonly>
      <button class="btn-copy" onclick="copyText('resDownload')">Copy</button>
    </div>
    <div class="link-label">🌐 Inline CDN Link</div>
    <div class="link-row">
      <input type="text" id="resCdn" readonly>
      <button class="btn-copy" onclick="copyText('resCdn')">Copy</button>
    </div>
  </div>
  <div class="files-section">
    <h2>📂 Uploaded Files</h2>
    <ul class="file-list" id="fileList"><li style="color:#555;border:none;background:none">Loading...</li></ul>
  </div>
</div>
<div class="footer">Powered by Hugging Face Datasets</div>
<div class="toast" id="toast">✅ Copied!</div>
<script>
const dropZone=document.getElementById('dropZone');
const fileInput=document.getElementById('fileInput');
const progressWrap=document.getElementById('progressWrap');
const progressBar=document.getElementById('progressBar');
const progressText=document.getElementById('progressText');
const progressPercent=document.getElementById('progressPercent');
const progressSize=document.getElementById('progressSize');
const resultBox=document.getElementById('resultBox');
const resName=document.getElementById('resName');
const resSize=document.getElementById('resSize');
const resDownload=document.getElementById('resDownload');
const resCdn=document.getElementById('resCdn');
const fileList=document.getElementById('fileList');
const toast=document.getElementById('toast');

dropZone.addEventListener('dragover',e=>{e.preventDefault();dropZone.classList.add('dragover')});
dropZone.addEventListener('dragleave',()=>dropZone.classList.remove('dragover'));
dropZone.addEventListener('drop',e=>{e.preventDefault();dropZone.classList.remove('dragover');if(e.dataTransfer.files.length)uploadFile(e.dataTransfer.files[0])});
fileInput.addEventListener('change',e=>{if(e.target.files.length)uploadFile(e.target.files[0])});

function fmtBytes(b){if(b<1024)return b+' B';if(b<1048576)return (b/1024).toFixed(1)+' KB';if(b<1073741824)return (b/1048576).toFixed(1)+' MB';return (b/1073741824).toFixed(2)+' GB'}

async function uploadFile(file){
  progressWrap.style.display='block';
  resultBox.style.display='none';
  progressBar.style.width='0%';
  progressText.textContent='Uploading '+file.name+'...';
  progressPercent.textContent='0%';
  progressSize.textContent='0 MB / '+fmtBytes(file.size);
  const fd=new FormData();fd.append('file',file);
  try{
    const xhr=new XMLHttpRequest();
    xhr.open('POST','/upload');
    xhr.upload.onprogress=e=>{if(e.lengthComputable){const p=Math.round((e.loaded/e.total)*100);progressBar.style.width=p+'%';progressPercent.textContent=p+'%';progressSize.textContent=fmtBytes(e.loaded)+' / '+fmtBytes(e.total)}};
    xhr.onload=()=>{
      if(xhr.status===200){
        const d=JSON.parse(xhr.responseText);
        progressWrap.style.display='none';
        resultBox.style.display='block';
        resName.textContent='📁 '+d.filename;
        resSize.textContent='📦 '+fmtBytes(d.size);
        resDownload.value=d.download_url||d.url||'';
        resCdn.value=d.cdn_url||d.url||'';
        loadFiles();
      }else{progressWrap.style.display='none';alert('Upload failed: '+xhr.responseText)}
    };
    xhr.onerror=()=>{progressWrap.style.display='none';alert('Network error')};
    xhr.send(fd);
  }catch(err){progressWrap.style.display='none';alert('Error: '+err.message)}
}

function copyText(id){
  const el=document.getElementById(id);
  el.select();
  navigator.clipboard.writeText(el.value).then(()=>{toast.style.display='block';setTimeout(()=>toast.style.display='none',2000)});
}

async function loadFiles(){
  try{
    const r=await fetch('/files',{credentials:'same-origin'});
    const d=await r.json();
    const items=d.items||[];
    if(!items.length){fileList.innerHTML='<li style="color:#555;border:none;background:none">No files yet</li>';return}
    fileList.innerHTML=items.map(it=>{
      const dl=it.download_url||('/download/'+encodeURIComponent(it.name));
      const cd=it.cdn_url||('/cdn/'+encodeURIComponent(it.name));
      return '<li><span class="fn">'+it.name+'</span><span><a href="'+dl+'" target="_blank">⬇ Download</a> &nbsp; <a href="'+cd+'" target="_blank">🌐 Open</a></span></li>';
    }).join('');
  }catch(e){fileList.innerHTML='<li style="color:#f66;border:none;background:none">Failed to load</li>'}
}

loadFiles();
</script>
</body>
</html>"""


# ─────────────────────────────────────────
# Web Routes
# ─────────────────────────────────────────
@app.get("/", response_class=HTMLResponse, dependencies=[Depends(require_auth)])
def home():
    return HTMLResponse(INDEX_HTML)


@app.get("/health")
def health():
    return {
        "status": "ok",
        "repo": HF_REPO,
        "public_base_url": PUBLIC_BASE_URL or None,
        "auth_enabled": AUTH_ENABLED,
        "protect_downloads": PROTECT_DOWNLOADS,
    }


# ─────────────────────────────────────────
# Web Upload API
# ─────────────────────────────────────────
@app.post("/upload", dependencies=[Depends(require_auth)])
async def upload(request: Request, file: UploadFile = File(...)):
    original_name = file.filename or ""
    filename = Path(original_name).name

    if not filename:
        filename = f"file_{uuid.uuid4().hex[:8]}"

    try:
        safe_filename = safe_relative_path(filename)
    except HTTPException:
        safe_filename = f"file_{uuid.uuid4().hex[:8]}"

    tmp_path = TMP_DIR / f"{uuid.uuid4().hex}_{safe_filename}"
    size = 0

    try:
        async with aiofiles.open(tmp_path, "wb") as out:
            while chunk := await file.read(8 * 1024 * 1024):
                size += len(chunk)

                if size > MAX_FILE_SIZE:
                    raise HTTPException(
                        status_code=413,
                        detail="File too large (max 2GB)",
                    )

                await out.write(chunk)

        logger.info(
            f"🌐 Web upload: {safe_filename} ({size / (1024 * 1024):.1f} MB)"
        )

        await asyncio.to_thread(
            hf_api.upload_file,
            path_or_fileobj=str(tmp_path),
            path_in_repo=safe_filename,
            repo_id=HF_REPO,
            repo_type="dataset",
            commit_message=f"Web upload: {safe_filename}",
        )

        download_url = build_download_url(safe_filename, request)
        cdn_url = build_cdn_url(safe_filename, request)

        return {
            "success": True,
            "filename": safe_filename,
            "size": size,
            "url": download_url,
            "download_url": download_url,
            "cdn_url": cdn_url,
        }

    except HTTPException:
        raise

    except Exception as e:
        logger.error(f"❌ Web upload failed: {e}")
        raise HTTPException(status_code=500, detail=str(e))

    finally:
        try:
            tmp_path.unlink(missing_ok=True)
        except Exception:
            pass


# ─────────────────────────────────────────
# File Listing
# ─────────────────────────────────────────
@app.get("/files", dependencies=[Depends(require_auth)])
def list_files():
    try:
        raw = hf_api.list_repo_files(repo_id=HF_REPO, repo_type="dataset")

        skip = {".gitattributes", "README.md", ".gitignore"}
        files = [
            f
            for f in raw
            if f not in skip and not f.startswith(".")
        ]

        items = []

        for f in files:
            try:
                items.append(
                    {
                        "name": f,
                        "download_url": build_download_url(f),
                        "cdn_url": build_cdn_url(f),
                    }
                )
            except HTTPException:
                continue

        return {
            "files": files,
            "items": items,
            "count": len(files),
        }

    except Exception as e:
        logger.error(f"❌ List failed: {e}")
        return {
            "files": [],
            "items": [],
            "count": 0,
            "error": str(e),
        }


# ─────────────────────────────────────────
# CDN Redirect
# ─────────────────────────────────────────
@app.get(
    "/cdn/{filename:path}",
    dependencies=[Depends(optional_download_auth)],
)
def cdn_redirect(filename: str):
    return RedirectResponse(
        direct_hf_url(filename, download=False),
        status_code=302,
    )


# ─────────────────────────────────────────
# Download Endpoint
# ─────────────────────────────────────────
@app.get(
    "/download/{filename:path}",
    dependencies=[Depends(optional_download_auth)],
)
def download_file(filename: str):
    return RedirectResponse(
        direct_hf_url(filename, download=True),
        status_code=302,
    )


# ─────────────────────────────────────────
# Telegram Bot
# ─────────────────────────────────────────
@client.on(events.NewMessage(pattern="/start"))
async def tg_start(event):
    if PUBLIC_BASE_URL:
        web_line = f"\n\n☁️ Web: {PUBLIC_BASE_URL}"
    else:
        web_line = (
            "\n\n⚙️ Set PUBLIC_BASE_URL secret "
            "to enable your own domain links."
        )

    await event.reply(
        "👋 *My Cloud Bot*\n\n"
        "Send me any file (up to 2GB) and I'll give you a download link.\n"
        f"{web_line}",
        parse_mode="markdown",
    )


@client.on(events.NewMessage(pattern="/files"))
async def tg_files(event):
    try:
        raw = hf_api.list_repo_files(repo_id=HF_REPO, repo_type="dataset")

        skip = {".gitattributes", "README.md", ".gitignore"}
        files = [
            f
            for f in raw
            if f not in skip and not f.startswith(".")
        ]

        if not files:
            await event.reply("📂 No files uploaded yet.")
            return

        lines = "\n".join(f"• {f}" for f in files[:50])

        await event.reply(
            f"📂 *Files ({len(files)}):*\n{lines}",
            parse_mode="markdown",
        )

    except Exception as e:
        await event.reply(f"❌ Error: {e}")


@client.on(events.NewMessage())
async def tg_handle_file(event):
    if event.message.text and event.message.text.startswith("/"):
        return

    if not event.message.file:
        return

    msg = await event.reply("📥 *Downloading...*", parse_mode="markdown")

    raw_name = getattr(event.message.file, "name", None)
    fname = Path(raw_name).name if raw_name else ""

    if not fname:
        if getattr(event.message, "photo", None):
            ext = ".jpg"
        else:
            ext = getattr(event.message.file, "ext", None) or ".bin"
            if not ext.startswith("."):
                ext = f".{ext}"

        fname = f"tg_{event.message.id}{ext}"

    try:
        fname = safe_relative_path(fname)
    except HTTPException:
        fname = f"tg_{event.message.id}.bin"

    file_path = None

    try:
        last_pct = 0

        def progress(cur, tot):
            nonlocal last_pct

            if not tot:
                return

            pct = int((cur / tot) * 100)

            if pct >= last_pct + 10:
                last_pct = pct
                asyncio.create_task(
                    msg.edit(
                        f"📥 *Downloading:* `{fname}`\n⏳ {pct}%",
                        parse_mode="markdown",
                    )
                )

        result = await client.download_media(
            event.message,
            progress_callback=progress,
            parallel_count=8,
        )

        if result is None:
            raise Exception("Download returned None")

        if isinstance(result, bytes):
            tmp_file = TMP_DIR / f"{uuid.uuid4().hex}_{fname}"
            tmp_file.write_bytes(result)
            file_path = str(tmp_file)
        else:
            file_path = str(result)

        size_mb = os.path.getsize(file_path) / (1024 * 1024)

        await msg.edit(
            f"📤 *Uploading {size_mb:.1f} MB to Cloud...*",
            parse_mode="markdown",
        )

        await asyncio.to_thread(
            hf_api.upload_file,
            path_or_fileobj=file_path,
            path_in_repo=fname,
            repo_id=HF_REPO,
            repo_type="dataset",
            commit_message=f"TG upload: {fname}",
        )

        download_link = build_download_url(fname)
        cdn_link = build_cdn_url(fname)

        await msg.edit(
            "✅ *Done!*\n\n"
            f"📁 `{fname}`\n"
            f"📦 {size_mb:.2f} MB\n\n"
            f"🔗 *Download:*\n{download_link}\n\n"
            f"🌐 *Inline CDN:*\n{cdn_link}",
            parse_mode="markdown",
        )

        logger.info(f"✅ TG upload OK: {fname}")

    except Exception as e:
        logger.error(f"❌ TG upload failed: {e}")
        await msg.edit(
            f"❌ `{type(e).__name__}: {str(e)[:200]}`",
            parse_mode="markdown",
        )

    finally:
        if file_path:
            try:
                Path(file_path).unlink(missing_ok=True)
            except Exception:
                pass


# ─────────────────────────────────────────
# Startup / Shutdown
# ─────────────────────────────────────────
@app.on_event("startup")
async def on_startup():
    logger.info("🚀 Starting My Cloud...")

    if PUBLIC_BASE_URL:
        logger.info(f"PUBLIC_BASE_URL = {PUBLIC_BASE_URL}")
    else:
        logger.warning(
            "PUBLIC_BASE_URL is not set. "
            "Web links will use request host when possible. "
            "Telegram links will fallback to direct Hugging Face URLs."
        )

    await client.start(bot_token=BOT_TOKEN)
    logger.info("✅ Telegram bot connected")


@app.on_event("shutdown")
async def on_shutdown():
    await client.disconnect()
    logger.info("🛑 Bot stopped")


if __name__ == "__main__":
    import uvicorn

    uvicorn.run(
        app,
        host="0.0.0.0",
        port=int(os.getenv("PORT", "7860")),
        reload=False,
    )
