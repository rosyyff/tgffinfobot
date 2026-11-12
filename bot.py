"""
Free Fire Info Bot (Telegram)
  /info <uid>  |  info <uid>  |  /get <uid>  |  get <uid>  |  uid <uid>
  /item <item id or name>
  /track <uid>  (private chat only: instant alerts when anything on that profile changes)

Every value is wrapped in <code> so a single tap copies it.
Single file: missing packages are installed automatically on first run.
Env vars: BOT_TOKEN (required), INFO_API, ITEM_API, WATERMARK, FONT_PATH, PORT (Render keep-alive),
          TRACK_MIN, TRACK_MAX, MAX_TRACKS_PER_USER, MAX_TRACKS_TOTAL, DATA_DIR, MONGO_URI (see db.py)
"""
import os
import subprocess
import sys


def _ensure(mod, pkg, required=True):
    try:
        __import__(mod)
    except ImportError:
        try:
            subprocess.check_call([sys.executable, "-m", "pip", "install", "-q", pkg])
        except Exception as e:
            if required:
                raise SystemExit(f"Could not install {pkg}: {e}")


_ensure("telegram", "python-telegram-bot>=21,<23")
_ensure("httpx", "httpx")
_ensure("PIL", "Pillow", required=False)
if os.getenv("MONGO_URI"):  # optional: keeps /track data across restarts
    _ensure("motor", "motor", required=False)
    _ensure("dns", "dnspython", required=False)

import asyncio
import html
import io
import json
import logging
import os
import re
import random
import threading
import time
import urllib.request
from datetime import datetime, timedelta, timezone
from http.server import BaseHTTPRequestHandler, HTTPServer

import httpx

import db  # permanent storage (data/ffbot.db) - keep db.py next to this file
from telegram import BotCommand, InlineKeyboardButton, InlineKeyboardMarkup, InputMediaPhoto, Update
from telegram.constants import ChatAction, ChatType, ParseMode
from telegram.error import Forbidden, RetryAfter, TimedOut
from telegram.ext import (
    Application,
    CallbackQueryHandler,
    CommandHandler,
    ContextTypes,
    MessageHandler,
    filters,
)

try:
    from PIL import Image, ImageChops, ImageDraw, ImageFilter, ImageFont, ImageOps

    PIL_OK = True
except ImportError:  # images are optional
    PIL_OK = False

logging.basicConfig(level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s")
log = logging.getLogger("ffinfo")

BOT_TOKEN = os.getenv("BOT_TOKEN", "")
INFO_API = os.getenv("INFO_API", "https://rosyyinfo.vercel.app/info")
ITEM_API = os.getenv("ITEM_API", "https://starexx.vercel.app/api/items")
WATERMARK = os.getenv("WATERMARK", "SK")
# Icon CDNs (PNG first; WEBP is converted with Pillow)
ICON_URLS = [
    "https://cdn.jsdelivr.net/gh/ShahGCreator/icon@main/PNG/{id}.png",
    "https://cdn.jsdelivr.net/gh/AfnanTawsif/ff-catalog@main/Item-webp/{id}.webp",
]
FONT_URLS = [
    "https://cdn.jsdelivr.net/npm/dejavu-fonts-ttf@2.37.3/ttf/DejaVuSans-Bold.ttf",
    "https://cdn.jsdelivr.net/gh/dejavu-fonts/dejavu-fonts@version_2_37/ttf/DejaVuSans-Bold.ttf",
]

IST = timezone(timedelta(hours=5, minutes=30))
CACHE_TTL = 60       # player cache, seconds
ITEM_TTL = 6 * 3600  # item cache, seconds
COOLDOWN = 3         # per user, seconds
MAX_LEN = 3900       # Telegram limit is 4096
TO = dict(read_timeout=60, write_timeout=60, connect_timeout=20, pool_timeout=20)  # uploads need >5s

PLAYER_CACHE: dict = {}
ITEM_CACHE: dict = {}
LAST_USE: dict = {}
SEEN: dict = {}
_client = None


def trim(d: dict, limit: int):
    """Keep a cache dict from growing forever (drops the oldest quarter)."""
    if len(d) > limit:
        for k in list(d)[: max(1, limit // 4)]:
            d.pop(k, None)


# ───────────────────────── text helpers ─────────────────────────
_FX = str.maketrans({"a": "α", "k": "к", "r": "ʀ"})


def fx(s) -> str:
    """Label font: Pαcкʀʀ style."""
    return str(s).translate(_FX)


def http() -> httpx.AsyncClient:
    global _client
    if _client is None:
        _client = httpx.AsyncClient(
            timeout=20, follow_redirects=True, headers={"User-Agent": "Mozilla/5.0"}
        )
    return _client


def esc(v) -> str:
    return html.escape(str(v), quote=False)


def cp(v) -> str:
    """Tap-to-copy value."""
    s = "" if v is None else str(v)
    return f"<code>{esc(s if s != '' else '—')}</code>"


_TAG = re.compile(r"\[(?:/?[A-Za-z]{1,2}|[0-9A-Fa-f]{6,8})\]")


def clean(s) -> str:
    return _TAG.sub("", str(s or "")).strip()


def indian(n) -> str:
    try:
        s = str(int(n))
    except Exception:
        return str(n)
    neg = s.startswith("-")
    s = s.lstrip("-")
    if len(s) > 3:
        head, tail = s[:-3], s[-3:]
        parts = []
        while len(head) > 2:
            parts.insert(0, head[-2:])
            head = head[:-2]
        if head:
            parts.insert(0, head)
        s = ",".join(parts + [tail])
    return ("-" if neg else "") + s


def ts(t) -> str:
    try:
        t = int(t)
        if t <= 0:
            return "0"
        return datetime.fromtimestamp(t, IST).strftime("%d %b %Y, %I:%M %p")
    except Exception:
        return str(t)


def enum_txt(s, prefix="") -> str:
    return str(s).replace(prefix, "").replace("_", " ").title()


# Approximate BR tier names (API only returns a numeric code) - edit if needed
def br_rank(code) -> str:
    try:
        c = int(code)
    except Exception:
        return ""
    names = []
    for tier, n in (("Bronze", 3), ("Silver", 3), ("Gold", 4), ("Platinum", 4), ("Diamond", 4)):
        names += [f"{tier} {'I' * i if i < 4 else 'IV'}" for i in range(1, n + 1)]
    names += ["Heroic", "Elite Heroic", "Master", "Grandmaster"]
    idx = c - 301
    return names[idx] if 0 <= idx < len(names) else ""


def why(e) -> str:
    """Short failure reason for the user."""
    if isinstance(e, httpx.HTTPStatusError):
        return f"HTTP {e.response.status_code}"
    if isinstance(e, httpx.TimeoutException):
        return "timeout"
    if isinstance(e, ValueError):
        return "no data"
    return type(e).__name__


# rows: (label, html value)
def R(label, value, name="", fmt=None):
    shown = fmt(value) if fmt else value
    v = cp(shown)
    if name:
        v += f" → {esc(name)}"
    return (fx(label), v)


def B(label, value):
    return (fx(label), "Yes ✅" if value else "No ❌")


def E(label, value):
    return (fx(label), "Equipped ✅" if value else "Not Equipped ❌")


def L(label, items):
    """items: list of ready html strings"""
    if not items:
        return (fx(label), cp("[]"))
    return (fx(label), "".join(f"\n│    • {x}" for x in items))


def id_line(i, nm):
    n = nm.get(str(i), "")
    return cp(i) + (f" → {esc(n)}" if n else "")


def section(title, rows) -> str:
    out = [f"<b>{fx(title)}</b>"]
    for i, (lab, val) in enumerate(rows):
        pre = "└" if i == len(rows) - 1 else "├"
        out.append(f"{pre} {lab}: {val}")
    return "\n".join(out)


def pack(sections, limit=MAX_LEN):
    msgs, cur = [], ""
    for s in sections:
        chunks = [s]
        if len(s) > limit:
            chunks, buf = [], ""
            for line in s.split("\n"):
                if len(buf) + len(line) + 1 > limit:
                    chunks.append(buf)
                    buf = line
                else:
                    buf = f"{buf}\n{line}" if buf else line
            if buf:
                chunks.append(buf)
        for c in chunks:
            if cur and len(cur) + len(c) + 2 > limit:
                msgs.append(cur)
                cur = c
            else:
                cur = f"{cur}\n\n{c}" if cur else c
    if cur:
        msgs.append(cur)
    return msgs


# ───────────────────────── "add me to your group" button under every message ─────────────────────────
BOT_USER = ""


def with_add(kb=None):
    """Existing inline keyboard (if any) + one long 'Add me to your group' button."""
    rows = [list(r) for r in kb.inline_keyboard] if kb else []
    if BOT_USER:
        rows.append([InlineKeyboardButton("➕ Add me to your group", url=f"https://t.me/{BOT_USER}?startgroup=true")])
    return InlineKeyboardMarkup(rows) if rows else None


async def rt(msg, text, add=True, **kw):
    if add:
        kw["reply_markup"] = with_add(kw.get("reply_markup"))
    return await msg.reply_text(text, **kw)


async def rp(msg, photo, add=True, **kw):
    if add:
        kw["reply_markup"] = with_add(kw.get("reply_markup"))
    return await msg.reply_photo(photo, **kw)


# ───────────────────────── item db ─────────────────────────
def _pick(d, *keys, default=""):
    for k in keys:
        if k in d and d[k] not in (None, ""):
            return d[k]
    return default


def _extract_items(js):
    if isinstance(js, list):
        return [x for x in js if isinstance(x, dict)]
    if isinstance(js, dict):
        for k in ("items", "data", "results", "result"):
            v = js.get(k)
            if isinstance(v, list):
                return [x for x in v if isinstance(x, dict)]
            if isinstance(v, dict):
                return _extract_items(v)
        if any(k in js for k in ("itemID", "item_id", "id", "name")):
            return [js]
    return []


def _norm_item(d):
    return {
        "id": str(_pick(d, "itemID", "item_id", "ItemID", "id", "ID")),
        "name": str(_pick(d, "name", "Name", "itemName")),
        "desc": str(_pick(d, "description", "desc", "Description")),
        "icon": str(_pick(d, "icon", "iconName", "icon_name", "IconName")),
        "type": str(_pick(d, "type", "itemType", "Type")),
        "rarity": str(_pick(d, "rarity", "Rarity")),
    }


async def search_items(q):
    r = await http().get(ITEM_API, params={"raw": q}, timeout=10)
    r.raise_for_status()
    return [_norm_item(x) for x in _extract_items(r.json())]


async def get_item(item_id):
    key = str(item_id)
    hit = ITEM_CACHE.get(key)
    if hit and time.time() - hit[0] < ITEM_TTL:
        return hit[1]
    res = None
    try:
        for it in await search_items(key):
            if it["id"] == key:
                res = it
                break
    except Exception as e:
        log.warning("item lookup failed %s: %r", key, e)
        return None  # failures are not cached
    ITEM_CACHE[key] = (time.time(), res)
    trim(ITEM_CACHE, 4000)
    return res


async def resolve_names(ids):
    async def one(i):
        it = await get_item(i)
        return str(i), (it or {}).get("name", "")

    try:
        res = await asyncio.wait_for(
            asyncio.gather(*[one(i) for i in ids], return_exceptions=True), timeout=8
        )
    except Exception:
        return {}
    return {k: v for k, v in (r for r in res if isinstance(r, tuple)) if v}


async def fetch_icon(item_id):
    """Item icon as PNG/JPEG bytes (WEBP is converted)."""
    for tpl in ICON_URLS:
        try:
            r = await http().get(tpl.format(id=item_id), timeout=8)
            if r.status_code != 200 or len(r.content) < 300:
                continue
            data = r.content
            if data[:4] == b"RIFF":  # webp -> png
                if not PIL_OK:
                    continue
                buf = io.BytesIO()
                Image.open(io.BytesIO(data)).convert("RGBA").save(buf, "PNG")
                data = buf.getvalue()
            return data
        except Exception:
            continue
    return None


# ───────────────────────── image cards (Pillow) ─────────────────────────
FONT_PATHS = [
    p
    for p in (
        os.getenv("FONT_PATH", ""),
        "DejaVuSans-Bold.ttf",
        "/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf",
        "/data/data/com.termux/files/usr/share/fonts/TTF/DejaVuSans-Bold.ttf",
        "/system/fonts/Roboto-Bold.ttf",
        "/system/fonts/NotoSansCJK-Bold.ttc",
        "/system/fonts/NotoSansCJK-Regular.ttc",
        "/system/fonts/DroidSansFallback.ttf",
        "/system/fonts/NotoSansSymbols-Regular-Subtitle.ttf",
        "/usr/share/fonts/truetype/freefont/FreeSansBold.ttf",
    )
    if p
]
_FONT_CACHE: dict = {}
_GLYPH_CACHE: dict = {}


def ensure_font():
    """If no usable font exists, fetch DejaVu Sans Bold once."""
    if not PIL_OK or any(os.path.exists(p) for p in FONT_PATHS):
        return
    for url in FONT_URLS:
        try:
            with urllib.request.urlopen(url, timeout=20) as r:
                data = r.read()
            if len(data) > 50000:
                with open("DejaVuSans-Bold.ttf", "wb") as f:
                    f.write(data)
                log.info("Font downloaded")
                return
        except Exception as e:
            log.warning("font download failed: %r", e)


def _fonts(size):
    if size in _FONT_CACHE:
        return _FONT_CACHE[size]
    fonts = []
    for p in FONT_PATHS:
        if os.path.exists(p):
            try:
                fonts.append(ImageFont.truetype(p, size))
            except Exception:
                pass
    if not fonts:
        try:
            fonts = [ImageFont.load_default(size)]
        except TypeError:
            fonts = [ImageFont.load_default()]
    _FONT_CACHE[size] = fonts
    return fonts


def _has(font, ch) -> bool:
    key = (id(font), ch)
    if key not in _GLYPH_CACHE:
        try:
            m, nd = font.getmask(ch), font.getmask("￿")
            _GLYPH_CACHE[key] = m.getbbox() is not None and (m.size, m.tobytes()) != (nd.size, nd.tobytes())
        except Exception:
            _GLYPH_CACHE[key] = True
    return _GLYPH_CACHE[key]


def _font_for(fonts, ch):
    if len(fonts) == 1 or ch.isspace():
        return fonts[0]
    for f in fonts:
        if _has(f, ch):
            return f
    return fonts[0]


_BLANK = {0x3164: " ", 0x2800: " ", 0x200B: None, 0x200E: None, 0x200F: None, 0x2060: None, 0xFEFF: None}


def _vis(text) -> str:
    return str(text).translate(_BLANK)


def _tw(text, fonts) -> float:
    return sum(_font_for(fonts, c).getlength(c) for c in _vis(text))


def _dt(d, xy, text, fonts, fill, stroke=0, stroke_fill=None):
    """Draw text on a baseline, picking a font per character (handles fancy unicode)."""
    x, y = xy
    for c in _vis(text):
        f = _font_for(fonts, c)
        d.text((x, y), c, font=f, fill=fill, anchor="ls", stroke_width=stroke, stroke_fill=stroke_fill)
        x += f.getlength(c)


def _shear(layer, k=0.22):
    w, h = layer.size
    return layer.transform((w + int(k * h), h), Image.AFFINE, (1, k, -k * h, 0, 1, 0), Image.BICUBIC)


def _title_layer(text, size, fill=(255, 255, 255, 255), glow=(255, 40, 30), slant=0.22):
    fonts = _fonts(size)
    pad = 30
    w, h = int(_tw(text, fonts)) + pad * 2, int(size * 1.6)
    lay = Image.new("RGBA", (w, h), (0, 0, 0, 0))
    _dt(ImageDraw.Draw(lay), (pad, int(size * 1.15)), text, fonts, fill)
    lay = _shear(lay, slant)
    alpha = lay.split()[3].filter(ImageFilter.GaussianBlur(max(2, size // 6)))
    gl = Image.new("RGBA", lay.size, glow + (0,))
    gl.putalpha(alpha)
    out = Image.new("RGBA", lay.size, (0, 0, 0, 0))
    out.alpha_composite(gl)
    out.alpha_composite(gl)
    out.alpha_composite(lay)
    return out


def _bg(W, H):
    rnd = random.Random(7)
    base = Image.new("RGB", (W, H), (7, 0, 3))
    glow = Image.new("RGB", (W, H), (0, 0, 0))
    gd = ImageDraw.Draw(glow)
    gd.ellipse((W * 0.08, H * 0.1, W * 0.92, H * 0.9), fill=(125, 8, 14))
    gd.ellipse((W * 0.3, H * 0.28, W * 0.7, H * 0.72), fill=(95, 10, 10))
    glow = glow.filter(ImageFilter.GaussianBlur(W // 7))
    img = ImageChops.add(base, glow).convert("RGBA")
    lay = Image.new("RGBA", (W, H), (0, 0, 0, 0))
    ld = ImageDraw.Draw(lay)
    for _ in range(110):
        x, y = rnd.randint(-100, W), rnd.randint(0, H + 100)
        n = rnd.randint(70, 280)
        ld.line((x, y, x + n * 0.5, y - n * 0.87), fill=(255, rnd.randint(20, 80), 20, rnd.randint(70, 210)), width=rnd.choice([1, 2, 2, 3]))
    img.alpha_composite(lay.filter(ImageFilter.GaussianBlur(5)))
    img.alpha_composite(lay)
    vig = Image.new("L", (W, H), 0)
    ImageDraw.Draw(vig).ellipse((-W * 0.25, -H * 0.25, W * 1.25, H * 1.25), fill=255)
    vig = vig.filter(ImageFilter.GaussianBlur(W // 6))
    dark = Image.new("RGBA", (W, H), (0, 0, 0, 255))
    img = Image.composite(img, dark, vig)
    return img


def _rarity_color(r):
    r = (r or "").lower()
    for key, col in (
        ("artifact", (255, 70, 70)),
        ("mythic+", (255, 140, 20)),
        ("mythic", (255, 205, 40)),
        ("epic", (190, 70, 255)),
        ("rare", (60, 150, 255)),
        ("uncommon", (70, 220, 100)),
        ("common", (235, 235, 235)),
    ):
        if key in r:
            return col
    return (200, 200, 200)


def _open(data):
    try:
        return Image.open(io.BytesIO(data)).convert("RGBA") if data else None
    except Exception:
        return None


def safe_name(name, fallback="Player"):
    """Name for images: drops characters the font cannot draw (no boxes); falls back to a plain label."""
    t = _vis(clean(name))
    fonts = _fonts(40)
    out = "".join(c for c in t if c.isspace() or any(_has(f, c) for f in fonts))
    out = re.sub(r"\s+", " ", out).strip()
    return out if sum(ch.isalnum() for ch in out) >= 2 else fallback


def _fit(text, max_w, size, min_size=14):
    """Largest font that fits max_w; adds an ellipsis if even min_size is too wide."""
    text = str(text or "")
    sz = size
    while sz > min_size and _tw(text, _fonts(sz)) > max_w:
        sz -= 2
    fonts = _fonts(sz)
    if text and _tw(text, fonts) > max_w:
        while text and _tw(text + "…", fonts) > max_w:
            text = text[:-1]
        text = text.rstrip() + "…"
    return text, fonts


def _round(im, size, radius=18):
    im = ImageOps.fit(im, (size, size), Image.LANCZOS)
    m = Image.new("L", (size, size), 0)
    ImageDraw.Draw(m).rounded_rectangle((0, 0, size - 1, size - 1), radius, fill=255)
    im.putalpha(ImageChops.multiply(im.split()[3], m))
    return im


def _slot(img, x, y, s, icon, color, label=""):
    pad = 40
    lay = Image.new("RGBA", (s + 2 * pad, s + 2 * pad), (0, 0, 0, 0))
    ImageDraw.Draw(lay).rounded_rectangle((pad, pad, pad + s, pad + s), 14, outline=color + (255,), width=8)
    bl = lay.filter(ImageFilter.GaussianBlur(10))
    img.paste(bl, (x - pad, y - pad), bl)
    d = ImageDraw.Draw(img)
    d.rounded_rectangle((x, y, x + s, y + s), 14, fill=(16, 6, 12, 255), outline=color + (255,), width=3)
    ramp = Image.linear_gradient("L").resize((s - 8, s - 8)).point(lambda v: int(v * 0.5))
    tint = Image.new("RGBA", (s - 8, s - 8), color + (255,))
    tint.putalpha(ramp)
    img.paste(tint, (x + 4, y + 4), tint)
    band = 44 if label else 0
    if icon is not None:
        ic = ImageOps.contain(icon, (s - 36, s - 36 - band), Image.LANCZOS)
        img.paste(ic, (x + (s - ic.width) // 2, y + 10 + (s - 20 - band - ic.height) // 2), ic)
    else:
        txt, f = _fit("NO IMAGE" if label else "EMPTY", s - 40, 22, 12)
        _dt(d, (x + (s - _tw(txt, f)) / 2, y + (s - band) // 2 + 8), txt, f, (150, 80, 80, 255))
    if label:
        bar = Image.new("RGBA", (s - 8, band), (0, 0, 0, 190))
        img.paste(bar, (x + 4, y + s - band - 4), bar)
        d.rectangle((x + 4, y + s - band - 5, x + s - 4, y + s - band - 3), fill=color + (255,))
        txt, f = _fit(label, s - 24, 22, 16)
        _dt(d, (x + (s - _tw(txt, f)) / 2, y + s - 17), txt, f, (255, 255, 255, 255))


def _jpeg(img, q=92):
    buf = io.BytesIO()
    img.convert("RGB").save(buf, "JPEG", quality=q)
    return buf.getvalue()


def _watermark(img, x_right, y, size=88):
    wm = _title_layer(WATERMARK, size, glow=(255, 30, 30))
    img.paste(wm, (x_right - wm.width, y), wm)


def _chip(img, x, y, label, value, h=56):
    """Small stat box: tiny label on top, value below. Returns the next free x."""
    d = ImageDraw.Draw(img)
    fl, fv = _fonts(16), _fonts(28)
    value = str(value)
    w = int(max(_tw(label, fl), _tw(value, fv))) + 34
    box = Image.new("RGBA", (w, h), (0, 0, 0, 0))
    ImageDraw.Draw(box).rounded_rectangle((0, 0, w - 1, h - 1), 12, fill=(0, 0, 0, 170), outline=(235, 35, 35, 255), width=2)
    img.paste(box, (x, y), box)
    _dt(d, (x + 17, y + 22), label, fl, (255, 150, 150, 255))
    _dt(d, (x + 17, y + 49), value, fv, (255, 255, 255, 255))
    return x + w + 14


def render_loadout(js, icons, rarity, names=None):
    """3x3 ring of equipped items around the avatar, item names under each icon."""
    names = names or {}
    W, H = 1080, 1190
    img = _bg(W, H)
    b, p = js.get("basic_info") or {}, js.get("profile_info") or {}
    t = _title_layer("PLAYER LOADOUT", 64)
    img.paste(t, (50, 28), t)
    _watermark(img, W - 40, 22, 68)

    S, G = 250, 28
    x0, y0 = (W - 3 * S - 2 * G) // 2, 175
    cell = lambda r, c: (x0 + c * (S + G), y0 + r * (S + G))  # noqa: E731
    order = [(0, 0), (0, 1), (0, 2), (1, 0), (1, 2), (2, 0), (2, 1), (2, 2)]
    ids = [i for i in (p.get("equipped_skills") or []) + (b.get("weapon_skin_shows") or []) if i][:8]

    cx, cy = cell(1, 1)
    lay = Image.new("RGBA", (W, H), (0, 0, 0, 0))
    ld = ImageDraw.Draw(lay)
    for r, c in order:
        ox, oy = cell(r, c)
        ld.line((cx + S // 2, cy + S // 2, ox + S // 2, oy + S // 2), fill=(255, 50, 40, 210), width=4)
    img.alpha_composite(lay.filter(ImageFilter.GaussianBlur(6)))
    img.alpha_composite(lay)

    for n, (r, c) in enumerate(order):
        x, y = cell(r, c)
        i = ids[n] if n < len(ids) else None
        col = _rarity_color(rarity.get(str(i), "")) if i else (120, 60, 60)
        label = (names.get(str(i)) or str(i)) if i else ""
        _slot(img, x, y, S, _open(icons.get(str(i))) if i else None, col, label)
    av = p.get("avatar_id") or b.get("head_pic")
    center = _open(icons.get(str(p.get("avatar_id")))) or _open(icons.get(str(b.get("head_pic"))))
    _slot(img, cx, cy, S, center, (255, 205, 40), (names.get(str(av)) or "AVATAR") if av else "AVATAR")

    # footer panel
    fy, fh = 1018, 140
    panel = Image.new("RGBA", (W - 100, fh), (0, 0, 0, 0))
    ImageDraw.Draw(panel).rounded_rectangle((0, 0, W - 101, fh - 1), 18, fill=(10, 2, 6, 205), outline=(235, 35, 35, 255), width=3)
    img.paste(panel, (50, fy), panel)
    d = ImageDraw.Draw(img)
    name = safe_name(b.get("nickname"))
    txt, f = _fit(name, 560, 46, 24)
    _dt(d, (80, fy + 62), txt, f, (255, 255, 255, 255), stroke=2, stroke_fill=(40, 0, 0, 255))
    _dt(d, (80, fy + 108), f"UID {b.get('account_id', '')}", _fonts(28), (255, 150, 150, 255))
    chips = [("LEVEL", b.get("level", "-")), ("BR PTS", b.get("ranking_points", "-"))]
    widths = []
    for lab, val in chips:
        widths.append(int(max(_tw(lab, _fonts(16)), _tw(str(val), _fonts(28)))) + 34 + 14)
    x = W - 80 - sum(widths) + 14
    for lab, val in chips:
        x = _chip(img, x, fy + 42, lab, val)
    return _jpeg(img)


def render_banner(js, icons, names=None):
    """Full profile banner (never cropped) + an info panel underneath."""
    b = js.get("basic_info") or {}
    W, PH = 1000, 210
    ban = _open(icons.get(str(b.get("banner_id"))))
    if ban is not None:
        HB = int(max(190, min(440, W * ban.height / ban.width)))
        top = ImageOps.fit(ban, (W, HB), Image.LANCZOS).filter(ImageFilter.GaussianBlur(18))
        top.alpha_composite(Image.new("RGBA", (W, HB), (0, 0, 0, 110)))
        fg = ImageOps.contain(ban, (W, HB), Image.LANCZOS)
        top.paste(fg, ((W - fg.width) // 2, (HB - fg.height) // 2), fg)
    else:
        HB = 230
        grad = Image.linear_gradient("L").resize((W, HB))
        top = Image.composite(Image.new("RGBA", (W, HB), (235, 70, 140, 255)), Image.new("RGBA", (W, HB), (240, 150, 190, 255)), grad)
    img = Image.new("RGBA", (W, HB + PH), (0, 0, 0, 255))
    img.paste(top, (0, 0))
    img.paste(_bg(W, PH), (0, HB))
    d = ImageDraw.Draw(img)
    d.rectangle((0, HB - 2, W, HB + 3), fill=(235, 35, 35, 255))

    A = 150
    ax, ay = 30, HB + 30
    av = _open(icons.get(str(b.get("head_pic"))))
    d.rounded_rectangle((ax - 4, ay - 4, ax + A + 3, ay + A + 3), 20, fill=(16, 6, 12, 255), outline=(255, 205, 40, 255), width=4)
    if av is not None:
        r = _round(av, A, 16)
        img.paste(r, (ax, ay), r)

    tx = ax + A + 32
    name = safe_name(b.get("nickname"))
    txt, f = _fit(name, W - tx - 30, 58, 26)
    _dt(d, (tx, HB + 82), txt, f, (255, 255, 255, 255), stroke=3, stroke_fill=(40, 0, 0, 255))
    _dt(d, (tx, HB + 118), f"UID {b.get('account_id', '')}", _fonts(26), (255, 150, 150, 255))
    x = tx
    for lab, val in (("LEVEL", b.get("level", "-")), ("LIKES", indian(b.get("liked", 0))), ("BR PTS", b.get("ranking_points", "-"))):
        x = _chip(img, x, HB + 136, lab, val)
    _watermark(img, W - 24, HB + 112, 54)
    return _jpeg(img)


def render_item_card(icon_bytes, it):
    W = H = 1080
    img = _bg(W, H)
    t = _title_layer("ITEM", 64)
    img.paste(t, (50, 30), t)
    S = 560
    _slot(img, (W - S) // 2, 150, S, _open(icon_bytes), _rarity_color(it.get("rarity", "")))
    d = ImageDraw.Draw(img)
    name = it.get("name") or f"ID {it.get('id', '')}"
    size = 60
    while size > 28 and _tw(name, _fonts(size)) > W - 120:
        size -= 4
    f = _fonts(size)
    _dt(d, ((W - _tw(name, f)) / 2, 850), name, f, (255, 255, 255, 255), stroke=2, stroke_fill=(40, 0, 0, 255))
    idt = f"ID {it.get('id', '')}"
    f2 = _fonts(34)
    _dt(d, ((W - _tw(idt, f2)) / 2, 905), idt, f2, (255, 150, 150, 255))
    _watermark(img, W - 40, H - 150)
    return _jpeg(img)


_WELCOME = {}


def render_welcome():
    if "img" in _WELCOME:
        return _WELCOME["img"]
    W, H = 1080, 560
    img = _bg(W, H)
    t = _title_layer("PLAYER INFO BOT", 96)
    img.paste(t, ((W - t.width) // 2, 130), t)
    d = ImageDraw.Draw(img)
    sub = "Free Fire  •  Player & Item Lookup"
    f = _fonts(36)
    _dt(d, ((W - _tw(sub, f)) / 2, 370), sub, f, (255, 170, 170, 255))
    _watermark(img, W - 40, H - 140, 72)
    _WELCOME["img"] = _jpeg(img)
    return _WELCOME["img"]


async def build_cards(js, nm):
    """Returns [banner, loadout] jpeg bytes (any that fail are skipped)."""
    if not PIL_OK:
        return []
    b, p = js.get("basic_info") or {}, js.get("profile_info") or {}
    ids = [i for i in (p.get("equipped_skills") or []) + (b.get("weapon_skin_shows") or []) if i][:8]
    extra = [p.get("avatar_id"), b.get("head_pic"), b.get("banner_id")]
    want = []
    for i in ids + extra:
        if i and i not in want:
            want.append(i)
    got = await asyncio.gather(*[fetch_icon(i) for i in want], return_exceptions=True)
    icons = {str(i): g for i, g in zip(want, got) if isinstance(g, (bytes, bytearray))}
    rarity = {}
    for i in ids:
        hit = ITEM_CACHE.get(str(i))
        if hit and hit[1]:
            rarity[str(i)] = hit[1].get("rarity", "")
    out = []
    for fn, args in ((render_banner, (js, icons, nm)), (render_loadout, (js, icons, rarity, nm))):
        try:
            out.append(await asyncio.to_thread(fn, *args))
        except Exception as e:
            log.warning("card render failed: %r", e)
    return out


# ───────────────────────── player ─────────────────────────
async def fetch_player(uid, force=False):
    hit = PLAYER_CACHE.get(uid)
    if hit and not force and time.time() - hit[0] < CACHE_TTL:
        return hit[1]
    last = None
    for attempt in range(3):
        try:
            r = await http().get(INFO_API, params={"uid": uid})
            r.raise_for_status()
            js = r.json()
            if isinstance(js, dict) and js.get("basic_info"):
                PLAYER_CACHE[uid] = (time.time(), js)
                trim(PLAYER_CACHE, 300)
                return js
            last = ValueError(f"basic_info missing: {str(js)[:120]}")
        except Exception as e:
            last = e
        log.warning("player fetch attempt %s failed: %r", attempt + 1, last)
        await asyncio.sleep(1)
    raise last


def collect_ids(js):
    b = js.get("basic_info") or {}
    p = js.get("profile_info") or {}
    pet = js.get("pet_info") or {}
    ids = [
        b.get("badge_id"), b.get("banner_id"), b.get("head_pic"), b.get("title"),
        p.get("avatar_id"), pet.get("pet_id"), pet.get("skin_id"), pet.get("selected_skill_id"),
    ]
    ids += b.get("weapon_skin_shows") or []
    ids += p.get("equipped_skills") or []
    out = []
    for i in ids:
        if i and i not in out:
            out.append(i)
    return out[:18]


def _jl(items):
    return [cp(json.dumps(x, ensure_ascii=False)) for x in items or []]


def build_player(js, nm):
    b = js.get("basic_info") or {}
    p = js.get("profile_info") or {}
    cl = js.get("clan_basic_info") or {}
    cap = js.get("captain_basic_info") or {}
    pet = js.get("pet_info") or {}
    so = js.get("social_info") or {}
    cr = js.get("credit_score_info") or {}
    pr = b.get("account_prefers") or {}
    n = lambda i: nm.get(str(i), "")  # noqa: E731

    nick = b.get("nickname", "")
    basic = [R("Name", nick)]
    if clean(nick) != nick:
        basic.append(R("Name (clean)", clean(nick)))
    basic += [
        R("UID", b.get("account_id")),
        R("Account Type", b.get("account_type")),
        R("Level", b.get("level")),
        R("EXP", b.get("exp"), fmt=indian),
        R("Likes", b.get("liked"), fmt=indian),
        R("Badges", b.get("badge_cnt")),
        R("Badge ID", b.get("badge_id"), n(b.get("badge_id"))),
        R("Banner ID", b.get("banner_id"), n(b.get("banner_id"))),
        R("Head Pic", b.get("head_pic"), n(b.get("head_pic"))),
        R("Title", b.get("title"), n(b.get("title"))),
        R("Prime Level", (b.get("prime_info") or {}).get("prime_level")),
        R("Booyah Pass", "Premium" if b.get("has_elite_pass") else "Normal"),
        R("Created", b.get("create_at"), fmt=ts),
        R("Last Login", b.get("last_login_at"), fmt=ts),
        R("Version", b.get("release_version")),
    ]

    rank = [
        R("BR Rank", b.get("rank"), br_rank(b.get("rank"))),
        R("BR Points", b.get("ranking_points")),
        R("BR Max Rank", b.get("max_rank"), br_rank(b.get("max_rank"))),
        R("CS Rank", b.get("cs_rank")),
        R("CS Points", b.get("cs_ranking_points")),
        R("CS Max Rank", b.get("cs_max_rank")),
        R("Hippo Rank", b.get("hippo_rank")),
        R("Hippo Points", b.get("hippo_ranking_points")),
        R("Season", b.get("season_id")),
        R("Peak Rank Pos", b.get("peak_rank_pos")),
        R("Leaderboard Pos", js.get("ranking_leaderboard_pos")),
        E("Show Rank", b.get("show_rank")),
        E("Show BR Rank", b.get("show_br_rank")),
        E("Show CS Rank", b.get("show_cs_rank")),
        L("CS Rank Entries", _jl(b.get("cs_rank_entries"))),
    ]

    gname = cl.get("clan_name", "")
    guild = [R("Name", gname)]
    if clean(gname) != gname:
        guild.append(R("Name (clean)", clean(gname)))
    guild += [
        R("Guild ID", cl.get("clan_id")),
        R("Level", cl.get("clan_level")),
        R("Members", f"{cl.get('current_members', 0)}/{cl.get('max_members', 0)}"),
        R("Leader ID", cl.get("captain_id")),
        R("Leader Name", cap.get("nickname")),
        R("Leader Level", cap.get("level")),
        R("Leader EXP", cap.get("exp"), fmt=indian),
        R("Leader Likes", cap.get("liked"), fmt=indian),
        R("Leader BR Rank", cap.get("rank"), br_rank(cap.get("rank"))),
        R("Leader BR Points", cap.get("ranking_points")),
        R("Leader Last Login", cap.get("last_login_at"), fmt=ts),
    ]

    petrows = [
        R("Name", pet.get("pet_name")),
        R("Pet ID", pet.get("pet_id"), n(pet.get("pet_id"))),
        R("Level", pet.get("level")),
        R("EXP", pet.get("exp")),
        B("Selected", pet.get("is_selected")),
        R("Skin ID", pet.get("skin_id"), n(pet.get("skin_id"))),
        R("Skill ID", pet.get("selected_skill_id"), n(pet.get("selected_skill_id"))),
    ]

    bio = so.get("social_highlight", "")
    privacy = so.get("privacy", "")
    social = [R("Gender", enum_txt(so.get("gender", ""), "GENDER_")), R("Language", so.get("language")), R("Bio", bio)]
    if clean(bio) != bio:
        social.append(R("Bio (clean)", clean(bio)))
    social += [
        R("Privacy", ("🔒 " if "CLOSED" in str(privacy) else "🔓 ") + enum_txt(privacy, "PRIVACY_")),
        R("Region", ((so.get("region_stats") or [{}])[0] or {}).get("region_code") or b.get("region")),
    ]

    load = [
        L("Equipped Items", [id_line(i, nm) for i in p.get("equipped_skills") or []]),
        L("Skill Slots", [f"slot {s.get('slot_index')} → {cp(s.get('skill_id'))}" for s in p.get("skill_slots") or []]),
        R("PvE Weapon", p.get("pve_primary_weapon")),
        R("Avatar ID", p.get("avatar_id"), n(p.get("avatar_id"))),
        L("Cosmetic Items", [id_line(i, nm) for i in p.get("cosmetic_items") or []]),
        L("Weapon Skins", [id_line(i, nm) for i in b.get("weapon_skin_shows") or []]),
        R("Skin Unlock Time", p.get("skin_unlock_time")),
    ]

    acc = [
        R("Honor Score", cr.get("score")),
        R("Honor Status", cr.get("status")),
        R("Honor Start", cr.get("start"), fmt=ts),
        R("Honor End", cr.get("end"), fmt=ts),
        R("Honor Reason", cr.get("reason")),
        R("Diamond Cost", (js.get("diamond_cost_res") or {}).get("diamond_cost")),
        B("Hide Clan Info", pr.get("hide_clan_info")),
        B("Hide Weapon Skins", pr.get("hide_weapon_skins")),
        E("Show Booyah Pass", pr.get("show_elite_pass")),
        E("Show Title", pr.get("show_title")),
    ]

    return [
        f"<b>{fx('🍁 Player Profile Info')}</b>",
        section("👤 Basic", basic),
        section("✅ Account", acc),
        section("💬 Social", social),
        section("🐾 Pet", petrows),
        section("🏆 Rank", rank),
        section("🎒 Loadout", load),
        section("🛡 Guild", guild),
        f"⏱ {esc(js.get('Time_Spne', ''))} · {esc(WATERMARK)}",
    ]


# ───────────────────────── handlers ─────────────────────────
def welcome_caption():
    return (
        f"🍁 <b>{fx('Free Fire Player Info')}</b>\n"
        "Full profile, loadout &amp; item details from just a UID.\n\n"
        f"✨ <b>{fx('What you get')}</b>\n"
        "• Profile banner + loadout card\n"
        "• Rank, guild, pet, Honor Score &amp; Booyah Pass\n"
        "• Item names with pictures\n\n"
        f"🚀 <b>{fx('Try it')}</b>\n"
        "/info 6118588149\n"
        "/item 907102815\n\n"
        "📖 All commands: /help\n"
        "<i>Tap any value in the results to copy it. Works in groups too.</i>"
    )


def help_text():
    return (
        f"🍁 <b>{fx('Command Guide')}</b>\n"
        "Send a command followed by a player UID.\n\n"
        f"👤 <b>{fx('Player')}</b>\n"
        "/info &lt;uid&gt; — full profile with banner &amp; loadout card\n"
        "/level &lt;uid&gt; — level, EXP, likes &amp; prime level\n"
        "/bio &lt;uid&gt; — signature / bio text\n"
        "/outfit &lt;uid&gt; — equipped items &amp; weapon skins\n"
        "/rank &lt;uid&gt; — BR &amp; CS rank with points\n"
        "/login &lt;uid&gt; — account created &amp; last login\n\n"
        f"🛡 <b>{fx('Guild')}</b>\n"
        "/clan &lt;uid&gt; — guild name, level &amp; members\n"
        "/leader &lt;uid&gt; — guild leader's details\n\n"
        f"🐾 <b>{fx('Pet')}</b>\n"
        "/pet &lt;uid&gt; — pet name, level, skin &amp; skill\n\n"
        f"🧾 <b>{fx('Items')}</b>\n"
        "/item &lt;id&gt; — item details with picture\n"
        "/item &lt;name&gt; — search items by name\n\n"
        f"🛰 <b>{fx('Live tracking')}</b> (private chat only)\n"
        "/track &lt;uid&gt; — instant alert on profile changes (you choose which ones)\n"
        "/tracklist — everyone you track, with details &amp; alert settings\n"
        "/untrack &lt;uid|all&gt; — stop tracking\n\n"
        f"💡 <b>{fx('Tips')}</b>\n"
        "• Example: /info 6118588149\n"
        "• Without a slash also works: info 6118588149\n"
        "• Tap any value in the results to copy it\n"
        "• Works in groups: /info@botusername 6118588149"
    )


def duplicate(update) -> bool:
    """True if this exact Telegram update was already handled (re-delivery guard)."""
    now = time.time()
    if len(SEEN) > 500:
        for k in [k for k, t in SEEN.items() if now - t > 300]:
            SEEN.pop(k, None)
    if update.update_id in SEEN:
        return True
    SEEN[update.update_id] = now
    return False


def limited(user_id) -> bool:
    now = time.time()
    if now - LAST_USE.get(user_id, 0) < COOLDOWN:
        return True
    LAST_USE[user_id] = now
    trim(LAST_USE, 3000)
    return False


async def action(msg, act):
    try:
        await msg.chat.send_action(act)
    except Exception:
        pass


async def send_parts(msg, parts, kb=None):
    for i, part in enumerate(parts):
        last = i == len(parts) - 1
        await rt(msg, part, add=last, parse_mode=ParseMode.HTML, reply_markup=kb if last else None)


async def send_photo(msg, photo, text) -> bool:
    """Send photo (+ text as caption, or as a follow-up if too long).
    Returns True when the photo is out or MAY be out (timeout) so the caller must never
    send the same text again; False only when Telegram clearly rejected the photo."""
    cap = text if len(text) <= 1024 else None
    try:
        if cap:
            await rp(msg, photo, caption=cap, parse_mode=ParseMode.HTML, **TO)
        else:
            await rp(msg, photo, **TO)
    except TimedOut:
        log.warning("photo upload timed out - not resending")
        return True
    except Exception as e:
        log.warning("photo send failed: %r", e)
        return False
    if cap is None:
        try:
            await send_parts(msg, pack([text]))
        except Exception as e:
            log.warning("text after photo failed: %r", e)
    return True


async def send_cards(msg, cards):
    """Banner + loadout as one album (single card -> normal photo). Never raises."""
    if not cards:
        return
    try:
        if len(cards) == 1:
            await rp(msg, cards[0], **TO)
        else:
            await msg.reply_media_group(media=[InputMediaPhoto(c) for c in cards], **TO)
        return
    except TimedOut:
        log.warning("album upload timed out - not resending")
        return
    except Exception as e:
        log.warning("album send failed: %r", e)
    for c in cards:  # album rejected as a whole -> nothing was delivered yet
        try:
            await rp(msg, c, **TO)
        except Exception as e:
            log.warning("card send failed: %r", e)


async def build_cards_safe(js, nm):
    try:
        return await asyncio.wait_for(build_cards(js, nm), timeout=40)
    except Exception as e:
        log.warning("cards failed: %r", e)
        return []


async def handle_info(msg, uid, force=False):
    await action(msg, ChatAction.TYPING)
    try:
        js = await fetch_player(uid, force)
    except Exception as e:
        log.warning("player fetch failed %s: %r", uid, e)
        await rt(msg, f"❌ Couldn't fetch this player ({why(e)}). Check the UID and try again.")
        return
    nm = await resolve_names(collect_ids(js))
    # images are rendered in the background while the details go out first
    cards_task = asyncio.create_task(build_cards_safe(js, nm)) if PIL_OK else None
    row = [InlineKeyboardButton("🔄 Refresh", callback_data=f"r:{uid}")]
    lead_id = (js.get("clan_basic_info") or {}).get("captain_id")
    if lead_id and str(lead_id) != str(uid):
        row.append(InlineKeyboardButton("👑 Leader", callback_data=f"c:{lead_id}"))
    try:
        await send_parts(msg, pack(build_player(js, nm)), InlineKeyboardMarkup([row]))
    except Exception as e:
        log.warning("details send failed: %r", e)
        if cards_task:
            cards_task.cancel()
        try:
            await rt(msg, "❌ Couldn't send the info. Please try again.")
        except Exception:
            pass
        return
    if cards_task:
        await action(msg, ChatAction.UPLOAD_PHOTO)
        await send_cards(msg, await cards_task)


def item_text(it):
    rows = []
    for lab, key in (("Name", "name"), ("Item ID", "id"), ("Type", "type"), ("Rarity", "rarity"), ("Icon Name", "icon"), ("Description", "desc")):
        if it.get(key):
            rows.append(R(lab, it[key]))
    return section("🧾 Item Info", rows)


async def handle_item(msg, arg):
    await action(msg, ChatAction.TYPING)
    arg = arg.strip()
    is_id = arg.isdigit()
    it, results = None, []
    try:
        if is_id:
            it = await get_item(arg)
        else:
            results = await search_items(arg)
            if len(results) == 1:
                it = results[0]
    except Exception as e:
        log.warning("item search failed %s: %r", arg, e)
        if not is_id:
            await rt(msg, f"❌ Item search is unavailable right now ({why(e)}).")
            return
    if not is_id:
        if not results:
            await rt(msg, "❌ No items found.")
            return
        if len(results) > 1:
            lines = [f"{cp(x['id'])} → {esc(x['name'])}" for x in results[:15]]
            await rt(msg, 
                f"🔎 <b>{len(results)} {fx('results')}</b>\n" + "\n".join(lines) + "\n\n<code>/item &lt;id&gt;</code>",
                parse_mode=ParseMode.HTML,
            )
            return
    iid = it["id"] if it else arg
    icon = await fetch_icon(iid)
    if not it and not icon:
        await rt(msg, "❌ Item not found.")
        return
    it = it or {"id": iid, "name": "", "desc": "", "icon": "", "type": "", "rarity": ""}
    text = item_text(it)
    photo = icon
    if icon and PIL_OK:
        await action(msg, ChatAction.UPLOAD_PHOTO)
        try:
            photo = await asyncio.to_thread(render_item_card, icon, it)
        except Exception as e:
            log.warning("item card failed: %r", e)
    if photo and await send_photo(msg, photo, text):
        return
    await send_parts(msg, pack([text]))


QUICK = ("level", "bio", "outfit", "rank", "clan", "leader", "pet", "login")
QUICK_RE = re.compile(r"^\s*[/!.#]?\s*(?P<c>" + "|".join(QUICK) + r")(?:@\w+)?\s*[:=\-]?\s*(?P<u>\d{5,13})\s*$", re.I)


def quick_text(js, nm, kind):
    b = js.get("basic_info") or {}
    p = js.get("profile_info") or {}
    cl = js.get("clan_basic_info") or {}
    ld = js.get("captain_basic_info") or {}
    pet = js.get("pet_info") or {}
    so = js.get("social_info") or {}
    n = lambda i: nm.get(str(i), "")  # noqa: E731
    head = [R("Name", b.get("nickname")), R("UID", b.get("account_id"))]

    if kind == "level":
        title = "📈 Level"
        rows = [R("Level", b.get("level")), R("EXP", b.get("exp"), fmt=indian),
                R("Likes", b.get("liked"), fmt=indian), R("Prime Level", (b.get("prime_info") or {}).get("prime_level"))]
    elif kind == "bio":
        title = "💬 Bio"
        bio = so.get("social_highlight", "")
        rows = [R("Bio", bio)]
        if clean(bio) != bio:
            rows.append(R("Bio (clean)", clean(bio)))
    elif kind == "outfit":
        title = "🎒 Outfit"
        rows = [
            L("Equipped Items", [id_line(i, nm) for i in p.get("equipped_skills") or []]),
            R("Avatar ID", p.get("avatar_id"), n(p.get("avatar_id"))),
            R("Banner ID", b.get("banner_id"), n(b.get("banner_id"))),
            R("Head Pic", b.get("head_pic"), n(b.get("head_pic"))),
            R("Title", b.get("title"), n(b.get("title"))),
            L("Cosmetic Items", [id_line(i, nm) for i in p.get("cosmetic_items") or []]),
            L("Weapon Skins", [id_line(i, nm) for i in b.get("weapon_skin_shows") or []]),
        ]
    elif kind == "rank":
        title = "🏆 Rank"
        rows = [
            R("BR Rank", b.get("rank"), br_rank(b.get("rank"))),
            R("BR Points", b.get("ranking_points")),
            R("BR Max Rank", b.get("max_rank"), br_rank(b.get("max_rank"))),
            R("CS Rank", b.get("cs_rank")), R("CS Points", b.get("cs_ranking_points")),
            R("CS Max Rank", b.get("cs_max_rank")),
        ]
    elif kind == "pet":
        title = "🐾 Pet"
        rows = [
            R("Pet Name", pet.get("pet_name")), R("Pet Level", pet.get("level")), R("Pet EXP", pet.get("exp")),
            R("Skin ID", pet.get("skin_id"), n(pet.get("skin_id"))),
            R("Skill ID", pet.get("selected_skill_id"), n(pet.get("selected_skill_id"))),
        ]
    elif kind == "login":
        title = "🕒 Activity"
        rows = [R("Created", b.get("create_at"), fmt=ts), R("Last Login", b.get("last_login_at"), fmt=ts),
                R("Version", b.get("release_version"))]
    elif kind == "leader":
        title = "👑 Leader"
        head = []
        rows = [
            R("Leader ID", cl.get("captain_id")), R("Leader Name", ld.get("nickname")),
            R("Leader Level", ld.get("level")), R("Leader EXP", ld.get("exp"), fmt=indian),
            R("Leader Likes", ld.get("liked"), fmt=indian),
            R("Leader BR Rank", ld.get("rank"), br_rank(ld.get("rank"))),
            R("Leader BR Points", ld.get("ranking_points")),
            R("Leader Last Login", ld.get("last_login_at"), fmt=ts),
        ]
    else:  # clan
        title = "🛡 Guild"
        head = []
        rows = [
            R("Name", cl.get("clan_name")), R("Guild ID", cl.get("clan_id")),
            R("Level", cl.get("clan_level")),
            R("Members", f"{cl.get('current_members', 0)}/{cl.get('max_members', 0)}"),
            R("Leader ID", cl.get("captain_id")), R("Leader Name", ld.get("nickname")),
        ]
    return [section(title, head + rows)]


async def handle_quick(msg, kind, uid):
    await action(msg, ChatAction.TYPING)
    try:
        js = await fetch_player(uid)
    except Exception as e:
        log.warning("quick fetch failed %s: %r", uid, e)
        await rt(msg, f"❌ Couldn't fetch this player ({why(e)}). Check the UID and try again.")
        return
    nm = await resolve_names(collect_ids(js)) if kind in ("outfit", "pet") else {}
    await send_parts(msg, pack(quick_text(js, nm, kind)))


INFO_RE = re.compile(r"^\s*[/!.#]?\s*(?:info|get|uid)(?:@\w+)?\s*[:=\-]?\s*(\d{5,13})\s*$", re.I)
ITEM_RE = re.compile(r"^\s*(?P<p>[/!.#])?\s*item(?:@\w+)?\s*[:=\-]?\s*(?P<a>.+?)\s*$", re.I)
BARE_RE = re.compile(r"^\s*[/!.#]\s*(?P<c>info|get|uid|item|level|bio|outfit|rank|clan|leader|pet|login)(?:@\w+)?\s*$", re.I)


async def router(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    msg = update.effective_message
    if not msg or not msg.text or not update.effective_user:
        return
    if duplicate(update):
        return
    text, uid = msg.text, update.effective_user.id
    m = TRACK_RE.match(text)
    if m:
        bn = m.group("b")
        if bn and ctx.bot.username and bn.lower() != ctx.bot.username.lower():
            return
        await handle_track(update, ctx, msg, m.group("c").lower(), m.group("a"))
        return
    m = INFO_RE.match(text)
    if m:
        if limited(uid):
            await rt(msg, "⏳ Slow down a little.")
            return
        await handle_info(msg, m.group(1))
        return
    m = QUICK_RE.match(text)
    if m:
        if limited(uid):
            await rt(msg, "⏳ Slow down a little.")
            return
        await handle_quick(msg, m.group("c").lower(), m.group("u"))
        return
    m = ITEM_RE.match(text)
    if m and (m.group("a").isdigit() or m.group("p")):
        if limited(uid):
            await rt(msg, "⏳ Slow down a little.")
            return
        await handle_item(msg, m.group("a"))
        return
    m = BARE_RE.match(text)
    if m:
        if m.group("c").lower() == "item":
            await rt(msg, "Usage: /item <id or name>")
        else:
            await rt(msg, f"Usage: /{m.group('c').lower()} <uid>")


async def start(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    msg = update.effective_message
    if not msg or duplicate(update):
        return
    cap = welcome_caption()
    if PIL_OK:
        try:
            card = await asyncio.to_thread(render_welcome)
        except Exception as e:
            log.warning("welcome card failed: %r", e)
            card = None
        if card and await send_photo(msg, card, cap):
            return
    await rt(msg, cap, parse_mode=ParseMode.HTML)


async def help_cmd(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    msg = update.effective_message
    if not msg or duplicate(update):
        return
    await rt(msg, help_text(), parse_mode=ParseMode.HTML)


async def on_cb(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    if not q or not q.data or not q.message:
        return
    if duplicate(update):
        return
    kind, _, val = q.data.partition(":")
    if kind in ("dt", "pf", "pt", "pa", "pd", "tl"):
        await track_cb(q, kind, val)
        return
    if limited(q.from_user.id):
        await q.answer("⏳ Slow down a little.")
        return
    await q.answer()
    if kind == "r":
        await handle_info(q.message, val, force=True)
    elif kind == "c":
        await handle_info(q.message, val)
    elif kind == "ut":
        t = TRACKS.get(val)
        if t and q.from_user.id in t["subs"]:
            t["subs"].remove(q.from_user.id)
            (t.get("off") or {}).pop(str(q.from_user.id), None)
            if not t["subs"]:
                TRACKS.pop(val, None)
            await tstore_save()
            await rt(q.message, f"🛑 Stopped tracking {cp(val)}", parse_mode=ParseMode.HTML)
        else:
            await rt(q.message, "You're not tracking that UID.")


# ───────────────────────── /track — live profile change alerts (private chat only) ─────────────────────────
UID_RE = re.compile(r"^\d{5,13}$")
TRACK_MIN = float(os.getenv("TRACK_MIN", "5"))
TRACK_MAX = max(TRACK_MIN, float(os.getenv("TRACK_MAX", "10")))
MAX_PER_USER = int(os.getenv("MAX_TRACKS_PER_USER", "5"))
MAX_TOTAL = int(os.getenv("MAX_TRACKS_TOTAL", "40"))
TRACK_IGNORE = [x.strip() for x in os.getenv("TRACK_IGNORE", "").split(",") if x.strip()]  # path fragments to ignore
TRACK_FILE = os.getenv("TRACK_FILE", "tracks.json")
MONGO_URI = os.getenv("MONGO_URI", "")
TRACKS: dict = {}   # uid -> {"subs": [chat ids], "snap": {flat}, "name": str, "fails": int, "due": float, "busy": bool, "warned": bool}
_TASKS: set = set()
_SAVE_LOCK = None
_mcol = None


def _dump():
    return {u: {"subs": t["subs"], "name": t.get("name", ""), "mute": t.get("mute") or [],
                "snap": json.dumps(t.get("snap") or {}, ensure_ascii=False),
                "base": json.dumps(t.get("base") or {}, ensure_ascii=False),
                "since": t.get("since", 0), "n": t.get("n", 0), "last": t.get("last", 0),
                "color": t.get("color", 0), "guild": t.get("guild", ""), "off": t.get("off") or {},
                "log": json.dumps(t.get("log") or [], ensure_ascii=False)}
            for u, t in TRACKS.items()}


async def tstore_load():
    data = {}
    try:
        data = await db.load_tracks()
    except Exception as e:
        log.warning("track load failed: %r", e)
    for u, t in data.items():
        try:
            _snap = json.loads(t.get("snap") or "{}")
            TRACKS[u] = {"subs": [int(x) for x in t["subs"]], "name": t.get("name", ""), "snap": _snap,
                         "base": json.loads(t.get("base") or "{}") or dict(_snap),
                         "since": t.get("since") or time.time(), "n": t.get("n", 0), "last": t.get("last", 0),
                         "color": t.get("color", 0), "guild": t.get("guild", ""), "off": dict(t.get("off") or {}),
                         "log": json.loads(t.get("log") or "[]"),
                         "mute": list(t.get("mute") or []),
                         "fails": 0, "due": time.time() + random.uniform(1, TRACK_MAX), "busy": False, "warned": False}
        except Exception:
            continue
    log.info("tracking %d player(s) (%s) | %d premium emoji", len(TRACKS), db.backend(), len(PREMIUM))


async def tstore_save():
    global _SAVE_LOCK
    _SAVE_LOCK = _SAVE_LOCK or asyncio.Lock()
    async with _SAVE_LOCK:
        payload = _dump()
        try:
            await db.save_tracks(payload)
        except Exception as e:
            log.warning("track save failed: %r", e)


def trackable(path):
    """Only fields inside the profile sections count. Top-level scalars (API meta such as response time) never do."""
    return "." in path and not any(f in path for f in TRACK_IGNORE)


def flatten_player(js):
    out = {}

    def walk(o, pre):
        if isinstance(o, dict):
            for k, v in o.items():
                walk(v, f"{pre}.{k}" if pre else str(k))
        elif isinstance(o, list):
            if all(not isinstance(x, (dict, list)) for x in o):
                out[pre] = list(o)
            else:
                for i, x in enumerate(o):
                    walk(x, f"{pre}[{i}]")
        else:
            out[pre] = o

    walk(js, "")
    return {k: v for k, v in out.items() if trackable(k)}


def diff_snap(old, new, mute=()):
    ch = []
    for k in list(old) + [k for k in new if k not in old]:
        if not trackable(k) or k in mute:  # also filters snapshots saved by an older run
            continue
        a, b = old.get(k), new.get(k)
        if a != b:
            ch.append((k, a, b))
    return ch


# ───────── premium (custom) emoji — optional ─────────
# Emoji ids come from db.py (imported from emoji.txt, stored in data/ffbot.db). Anything missing falls back to
# the normal emoji, so the bot never breaks. (Custom emoji render only if Telegram allows them for your bot.)
def _load_premium():
    try:
        return db.get_emojis()  # emoji.txt is imported into the DB automatically
    except Exception as e:
        log.warning("premium emoji map ignored: %r", e)
        return {}


PREMIUM = _load_premium()


def em(e: str) -> str:
    i = PREMIUM.get(db.norm(e))
    return f'<tg-emoji emoji-id="{i}">{e}</tg-emoji>' if i else e


# one colour square per tracked player -> every alert is instantly recognisable
DOTS = ["🟦", "🟩", "🟨", "🟧", "🟥", "🟪", "🟫", "⬜"]
SEP = "▬▬▬▬▬▬▬▬▬▬▬▬▬▬"

# alert categories (the user chooses which ones to receive)
CATS = [
    ("lvl", "📈", "Level & EXP"),
    ("like", "❤️", "Likes"),
    ("login", "🟢", "Login"),
    ("rank", "🏆", "Rank"),
    ("prof", "✏️", "Name & Bio"),
    ("look", "🎒", "Outfit & Items"),
    ("guild", "🛡", "Guild"),
    ("lead", "👑", "Guild Leader"),
    ("leadact", "⭐", "Leader Likes·EXP·Login"),
    ("pet", "🐾", "Pet"),
    ("misc", "🔧", "Other"),
]
CAT = {k: (e, n) for k, e, n in CATS}
CAT_ORDER = {k: i for i, (k, _, _) in enumerate(CATS)}


def cat_of(path):
    base = re.sub(r"\[\d+\]", "", path)
    sec, _, key = base.partition(".")
    if sec == "captain_basic_info":
        return "leadact" if key in ("exp", "liked", "last_login_at", "level") else "lead"
    if sec == "clan_basic_info":
        return "guild"
    if sec == "pet_info":
        return "pet"
    if sec == "social_info":
        return "prof"
    if sec == "profile_info":
        return "look"
    if sec == "basic_info":
        if key in ("level", "exp"):
            return "lvl"
        if key == "liked":
            return "like"
        if key == "last_login_at":
            return "login"
        if key == "nickname":
            return "prof"
        if key.startswith(("rank", "ranking_", "max_rank", "cs_", "hippo_", "peak_rank", "season")):
            return "rank"
        if key in ("banner_id", "head_pic", "title", "badge_id", "badge_cnt", "weapon_skin_shows"):
            return "look"
    return "misc"


# path -> (emoji, label, kind)   kind: ts | num | id | ids | rank | text
TRACK_LABELS = {
    "basic_info.nickname": ("👤", "Name", "text"), "basic_info.level": ("📈", "Level", "num"),
    "basic_info.exp": ("✨", "EXP", "num"), "basic_info.liked": ("❤️", "Likes", "num"),
    "basic_info.rank": ("🏆", "BR Rank", "rank"), "basic_info.ranking_points": ("🏅", "BR Points", "num"),
    "basic_info.max_rank": ("🥇", "BR Max Rank", "rank"), "basic_info.cs_rank": ("⚔️", "CS Rank", "text"),
    "basic_info.cs_ranking_points": ("🎯", "CS Points", "num"), "basic_info.cs_max_rank": ("🥇", "CS Max Rank", "text"),
    "basic_info.banner_id": ("🖼", "Banner", "id"), "basic_info.head_pic": ("🎭", "Head Pic", "id"),
    "basic_info.title": ("🎖", "Title", "id"), "basic_info.badge_id": ("🏷", "Badge", "id"),
    "basic_info.badge_cnt": ("🏷", "Badges", "num"), "basic_info.last_login_at": ("🟢", "Logged in", "ts"),
    "basic_info.weapon_skin_shows": ("🔫", "Weapon Skins", "ids"), "profile_info.avatar_id": ("🧑", "Avatar", "id"),
    "profile_info.equipped_skills": ("🎒", "Equipped Items", "ids"), "profile_info.cosmetic_items": ("🧥", "Cosmetics", "ids"),
    "social_info.social_highlight": ("💬", "Bio", "text"), "clan_basic_info.clan_name": ("🛡", "Guild Name", "text"),
    "clan_basic_info.clan_id": ("🛡", "Guild ID", "text"), "clan_basic_info.clan_level": ("🛡", "Guild Level", "num"),
    "clan_basic_info.captain_id": ("👑", "Leader changed", "text"), "pet_info.pet_name": ("🐾", "Pet Name", "text"),
    "pet_info.level": ("🐾", "Pet Level", "num"), "pet_info.skin_id": ("🐾", "Pet Skin", "id"),
    "pet_info.selected_skill_id": ("🐾", "Pet Skill", "id"),
}


def _label(path, cat="misc"):
    base = re.sub(r"\[\d+\]", "", path)
    sec, _, key = base.partition(".")
    look = ("basic_info." + key) if sec == "captain_basic_info" else base
    if look in TRACK_LABELS:
        return TRACK_LABELS[look]
    last = key.replace(".", " · ").replace("_", " ").title()
    pre = (sec.replace("_info", "").replace("_", " ").title() + " · ") if cat == "misc" else ""
    return (CAT[cat][0], pre + last, "auto")


def _is_id(v):
    return isinstance(v, int) and not isinstance(v, bool) and v >= 100000 or (isinstance(v, str) and v.isdigit() and len(v) >= 6)


def tss(t) -> str:
    try:
        return datetime.fromtimestamp(int(t), IST).strftime("%d %b %Y, %I:%M:%S %p")
    except Exception:
        return str(t)


def ago(t) -> str:
    if not t:
        return "—"
    s = int(time.time() - t)
    if s < 60:
        return f"{max(s, 0)}s ago"
    if s < 3600:
        return f"{s // 60}m ago"
    if s < 86400:
        return f"{s // 3600}h {(s % 3600) // 60}m ago"
    return f"{s // 86400}d {(s % 86400) // 3600}h ago"


def _delta(a, b):
    try:
        if isinstance(a, bool) or isinstance(b, bool) or not isinstance(a, (int, float)) or not isinstance(b, (int, float)):
            return ""
        d = b - a
        if d == 0:
            return ""
        return f"  <b>{'▲ +' if d > 0 else '▼ −'}{indian(abs(d))}</b>"
    except Exception:
        return ""


def _tv(v, kind, nm):
    if v is None or v == "":
        return cp("—")
    if kind == "ts":
        return cp(tss(v))
    if kind == "num":
        return cp(indian(v))
    if kind == "rank":
        r = br_rank(v)
        return cp(v) + (f" → {esc(r)}" if r else "")
    if kind == "text" and isinstance(v, str):
        c = clean(v)
        return cp(c[:140]) + (" <i>(colour codes removed)</i>" if c != v else "")
    n = nm.get(str(v), "") if (kind in ("id", "ids") or (kind == "auto" and _is_id(v))) else ""
    return cp(str(v)[:140]) + (f" → {esc(n)}" if n else "")


def alert_ids(changes):
    ids = []
    for p, a, b in changes:
        for v in (a if isinstance(a, list) else [a]) + (b if isinstance(b, list) else [b]):
            if _is_id(v) and str(v) not in ids:
                ids.append(str(v))
    return ids[:24]


def render_rows(changes, nm, snap):
    """-> [[cat, emoji, label, value_html], ...]  (JSON-safe, also stored in the history log)"""
    out = []
    for p, a, b in changes:
        cat = cat_of(p)
        emo, lab, kind = _label(p, cat)
        if p == "clan_basic_info.captain_id":
            who = clean(snap.get("captain_basic_info.nickname") or "")
            val = f"{_tv(a, 'text', nm)} → {_tv(b, 'text', nm)}" + (f"\n│    👑 New leader: {cp(who)}" if who else "")
        elif kind == "ts":
            lab = "Logged in" if cat == "login" else "Leader logged in"
            val = cp(tss(b)) + (f"\n│    ↩ Previous: {esc(tss(a))}" if a else "")
        elif isinstance(a, list) or isinstance(b, list):
            la, lb = (a or []), (b or [])
            add, rem = [x for x in lb if x not in la], [x for x in la if x not in lb]
            val = ""
            if add:
                val += "\n│    ➕ " + ", ".join(_tv(x, kind, nm) for x in add[:12])
            if rem:
                val += "\n│    ➖ " + ", ".join(_tv(x, kind, nm) for x in rem[:12])
            if not val:
                val = "\n│    🔀 order changed"
        elif a is None:
            val = f"new → {_tv(b, kind, nm)}"
        elif b is None:
            val = f"{_tv(a, kind, nm)} → removed"
        else:
            d = _delta(a, b) if (kind == "num" or (kind == "auto" and not _is_id(a))) else ""
            val = f"{_tv(a, kind, nm)} → {_tv(b, kind, nm)}{d}"
        if cat in ("lead", "leadact") and not lab.startswith("Leader"):
            lab = "Leader " + lab  # leader rows must never look like the player's own
        out.append([cat, emo, lab, val])
    out.sort(key=lambda r: CAT_ORDER.get(r[0], 99))
    return out


def dot_of(t):
    return DOTS[int(t.get("color", 0)) % len(DOTS)]


def _group_html(cat, rows):
    e, n = CAT[cat]
    lines = [f"<b>{em(e)} {fx(n)}</b>"]
    for i, (_, emo, lab, val) in enumerate(rows):
        pre = "└" if i == len(rows) - 1 else "├"
        lines.append(f"{pre} {em(emo)} {fx(lab)}: {val}")
    return "\n".join(lines)


def _groups(rows):
    out, cur, buf = [], None, []
    for r in rows:
        if r[0] != cur and buf:
            out.append(_group_html(cur, buf))
            buf = []
        cur = r[0]
        buf.append(r)
    if buf:
        out.append(_group_html(cur, buf))
    return out


def alert_parts(t, uid, rows, now):
    name = clean(t.get("name")) or uid
    head = (f"{dot_of(t)} <b>{esc(name)}</b>\n"
            f"{em('🔔')} <b>{fx('Profile update')}</b>\n"
            f"🆔 UID {cp(uid)}\n"
            f"🕒 {datetime.fromtimestamp(now, IST).strftime('%d %b %Y, %I:%M:%S %p')}\n{SEP}")
    foot = f"<i>{em('📊')} Change #{t.get('n', 0)} · {len(rows)} update(s)</i>"
    return pack([head] + _groups(rows) + [foot])


# ---- full details ("everything that changed so far") ----
SUM_NUM = [
    ("basic_info.level", "Level"), ("basic_info.exp", "EXP"), ("basic_info.liked", "Likes"),
    ("basic_info.badge_cnt", "Badges"), ("basic_info.ranking_points", "BR Points"),
    ("basic_info.cs_ranking_points", "CS Points"), ("pet_info.level", "Pet Level"),
    ("clan_basic_info.clan_level", "Guild Level"), ("captain_basic_info.level", "Leader Level"),
    ("captain_basic_info.exp", "Leader EXP"), ("captain_basic_info.liked", "Leader Likes"),
]
SUM_TXT = [
    ("basic_info.nickname", "Name"), ("social_info.social_highlight", "Bio"),
    ("clan_basic_info.clan_name", "Guild"), ("clan_basic_info.captain_id", "Leader ID"),
]


def details_parts(t, uid):
    cur, base = t.get("snap") or {}, t.get("base") or {}
    name = clean(t.get("name")) or uid
    head = [
        f"{dot_of(t)} <b>{esc(name)}</b>",
        f"{em('📋')} <b>{fx('Full details')}</b>",
        f"├ 🆔 UID {cp(uid)}",
        f"├ 🛰 Tracking since: {cp(tss(t.get('since')) if t.get('since') else '—')} ({ago(t.get('since'))})",
        f"├ 🟢 Last login: {cp(tss(cur.get('basic_info.last_login_at')) if cur.get('basic_info.last_login_at') else '—')}",
        f"├ 📊 Changes caught: {cp(t.get('n', 0))}",
        f"└ ⏱ Last change: {esc(ago(t.get('last')))}",
        SEP,
    ]
    tot = []
    for p, lab in SUM_NUM:
        a, b = base.get(p), cur.get(p)
        if a is not None and b is not None and a != b:
            tot.append(f"{CAT[cat_of(p)][0]} {fx(lab)}: {cp(indian(a))} → {cp(indian(b))}{_delta(a, b)}")
    for p, lab in SUM_TXT:
        a, b = base.get(p), cur.get(p)
        if a != b and not (a is None and b is None):
            tot.append(f"{CAT[cat_of(p)][0]} {fx(lab)}: {cp(clean(str(a))[:60] if a not in (None, '') else '—')} → "
                       f"{cp(clean(str(b))[:60] if b not in (None, '') else '—')}")
    if not tot:
        tot = ["No changes yet — I'm watching 👀"]
    total_txt = f"<b>{em('📈')} {fx('Total since tracking started')}</b>\n" + "\n".join(
        ("└ " if i == len(tot) - 1 else "├ ") + x for i, x in enumerate(tot))

    log_ = t.get("log") or []
    entries = []
    for e in log_:
        lines = [f"🕒 <b>{esc(datetime.fromtimestamp(e['t'], IST).strftime('%d %b, %I:%M:%S %p'))}</b>"]
        rs = e.get("rows") or []
        for i, (_, emo, lab, val) in enumerate(rs):
            lines.append(("└ " if i == len(rs) - 1 else "├ ") + f"{em(emo)} {fx(lab)}: {val}")
        entries.append("\n".join(lines))
    shown, size = [], 0
    for en in reversed(entries):  # newest first until the message is full
        if size + len(en) > 2400:
            break
        shown.append(en)
        size += len(en) + 2
    shown.reverse()
    hidden = len(entries) - len(shown)
    tl_head = f"<b>{em('🧾')} {fx('Timeline')}</b>" + (f" <i>(latest {len(shown)}, {hidden} older hidden)</i>" if hidden > 0 else "")
    tl = [tl_head] + (shown or ["Nothing yet."])
    return pack(["\n".join(head), total_txt] + tl)


# ---- buttons ----
def track_kb(uid):
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("📋 Full details", callback_data=f"dt:{uid}"),
         InlineKeyboardButton("⚙️ Alerts", callback_data=f"pf:{uid}")],
        [InlineKeyboardButton(f"🛑 Stop tracking {uid}", callback_data=f"ut:{uid}")],
    ])


stop_kb = track_kb


def prefs_view(chat_id, uid, intro=True):
    t = TRACKS.get(uid) or {}
    off = set((t.get("off") or {}).get(str(chat_id), []))
    btns = [InlineKeyboardButton(f"{'❌' if k in off else '✅'} {e} {n}", callback_data=f"pt:{uid}:{k}") for k, e, n in CATS]
    rows = [btns[i:i + 2] for i in range(0, len(btns), 2)]
    rows.append([InlineKeyboardButton("✅ All ON", callback_data=f"pa:{uid}:1"),
                 InlineKeyboardButton("🚫 All OFF", callback_data=f"pa:{uid}:0")])
    rows.append([InlineKeyboardButton("💾 Done", callback_data=f"pd:{uid}")])
    name = clean(t.get("name")) or uid
    text = (f"⚙️ <b>{fx('Alert settings')}</b>\n{dot_of(t)} <b>{esc(name)}</b> • UID {cp(uid)}\n\n"
            "Choose which updates you want to be notified about. Tap to switch ON ✅ / OFF ❌.\n"
            f"<i>{len(CATS) - len(off)}/{len(CATS)} ON</i>")
    return text, InlineKeyboardMarkup(rows)


async def send_to(app, uid, chat_id, parts, kb=None):
    t = TRACKS.get(uid)
    if not t:
        return
    for i, part in enumerate(parts):
        for attempt in range(2):
            try:
                await app.bot.send_message(chat_id, part, parse_mode=ParseMode.HTML,
                                           reply_markup=kb if i == len(parts) - 1 else None)
                break
            except RetryAfter as e:
                await asyncio.sleep(min(float(getattr(e, "retry_after", 2)), 20))
            except Forbidden:  # user blocked the bot / deleted chat -> stop tracking for them
                if chat_id in t["subs"]:
                    t["subs"].remove(chat_id)
                return
            except Exception as e:
                log.warning("alert send failed: %r", e)
                break


async def _cleanup(uid):
    t = TRACKS.get(uid)
    if t is not None and not t["subs"]:
        TRACKS.pop(uid, None)
        await tstore_save()


async def notify(app, uid, text_parts):
    """Plain notices (API down / back) to every subscriber."""
    t = TRACKS.get(uid)
    if not t:
        return
    for chat_id in list(t["subs"]):
        await send_to(app, uid, chat_id, text_parts, with_add(track_kb(uid)))
    await _cleanup(uid)


async def notify_changes(app, uid, rows, now):
    t = TRACKS.get(uid)
    if not t:
        return
    for chat_id in list(t["subs"]):
        off = set((t.get("off") or {}).get(str(chat_id), []))
        mine_rows = [r for r in rows if r[0] not in off]
        if mine_rows:
            await send_to(app, uid, chat_id, alert_parts(t, uid, mine_rows, now), with_add(track_kb(uid)))
    await _cleanup(uid)


async def fetch_once(uid):
    """One quick fetch (no retries, no cache read) for the tracker."""
    r = await http().get(INFO_API, params={"uid": uid}, headers={"Cache-Control": "no-cache"}, timeout=15)
    r.raise_for_status()
    js = r.json()
    if not (isinstance(js, dict) and js.get("basic_info")):
        raise ValueError("no data")
    PLAYER_CACHE[uid] = (time.time(), js)
    trim(PLAYER_CACHE, 300)
    return js


async def poll_one(app, uid):
    t = TRACKS.get(uid)
    if not t:
        return
    try:
        js = await fetch_once(uid)
    except Exception as e:
        t["fails"] += 1
        if t["fails"] in (1, 5, 30):
            log.warning("track %s fetch failed (%d): %r", uid, t["fails"], e)
        if t["fails"] >= 30 and not t["warned"]:
            t["warned"] = True
            await notify(app, uid, [f"⚠️ I can't reach the API for UID {cp(uid)} right now ({esc(why(e))}). "
                                    "I keep retrying and will message you when it's back."])
        return
    recovered = t["warned"]
    t["fails"], t["warned"] = 0, False
    snap = flatten_player(js)
    b = js.get("basic_info") or {}
    if b.get("nickname"):
        t["name"] = b["nickname"]
    g = (js.get("clan_basic_info") or {}).get("clan_name")
    if g is not None:
        t["guild"] = g
    if recovered:
        await notify(app, uid, [f"✅ API is back — tracking UID {cp(uid)} again."])
    if not t.get("snap"):
        t["snap"] = snap
        t.setdefault("base", snap)
        t.setdefault("since", time.time())
        await tstore_save()
        return
    old = t["snap"]
    # API hiccup: leader block vanished for one poll while the guild is the same -> keep the old values
    has = lambda d: any(k.startswith("captain_basic_info.") for k in d)  # noqa: E731
    if has(old) and not has(snap) and old.get("clan_basic_info.clan_id") == snap.get("clan_basic_info.clan_id"):
        for k, v in old.items():
            if k.startswith("captain_basic_info."):
                snap[k] = v
    changes = diff_snap(old, snap, t.get("mute") or ())
    now = time.time()
    hist = t.setdefault("hist", {})
    real = []
    for p, a, b2 in changes:
        h = [x for x in hist.get(p, []) if now - x < 90] + [now]
        hist[p] = h
        if len(h) >= 3:  # keeps flipping -> API noise
            t.setdefault("mute", []).append(p)
            log.info("track %s: muting noisy field %s", uid, p)
            continue
        real.append((p, a, b2))
    if len(hist) > 200:
        hist.clear()
    if real and any(p == "clan_basic_info.captain_id" for p, _, _ in real):
        # new leader: one clean "Leader changed" row instead of a dump of the whole leader profile
        real = [c for c in real if not c[0].startswith("captain_basic_info.")]
    if not real:
        t["snap"] = snap
        await tstore_save()
        return
    nm = await resolve_names(alert_ids(real)) if alert_ids(real) else {}
    rows = render_rows(real, nm, snap)
    t["snap"] = snap
    t["n"] = t.get("n", 0) + 1
    t["last"] = now
    t.setdefault("log", []).append({"t": now, "rows": rows})
    t["log"] = t["log"][-60:]
    await tstore_save()
    await notify_changes(app, uid, rows, now)


async def track_loop(app):
    sem = asyncio.Semaphore(6)

    async def run(uid):
        try:
            async with sem:
                await poll_one(app, uid)
        except Exception as e:
            log.warning("track poll crashed %s: %r", uid, e)
        finally:
            t = TRACKS.get(uid)
            if t:
                t["busy"] = False
                t["due"] = time.time() + (random.uniform(TRACK_MIN, TRACK_MAX) if t["fails"] < 5 else 30)

    while True:
        now = time.time()
        for uid, t in list(TRACKS.items()):
            if not t.get("busy") and t.get("due", 0) <= now:
                t["busy"] = True
                task = asyncio.create_task(run(uid))
                _TASKS.add(task)
                task.add_done_callback(_TASKS.discard)
        await asyncio.sleep(1)


TRACK_RE = re.compile(r"^\s*/(?P<c>track|untrack|tracklist)(?:@(?P<b>\w+))?(?:\s+(?P<a>.+))?\s*$", re.I | re.S)


def mine(user_id):
    return [u for u, t in TRACKS.items() if user_id in t["subs"]]


def track_list_text(user_id):
    ids = mine(user_id)
    if not ids:
        return "🛰 You're not tracking anyone yet.\nStart: <code>/track 6118588149</code>", None
    blocks = [f"{em('🛰')} <b>{fx('Tracking')} {len(ids)}/{MAX_PER_USER}</b> · ⏱ every {TRACK_MIN:g}–{TRACK_MAX:g}s"]
    kb = []
    for u in ids:
        t = TRACKS[u]
        off = set((t.get("off") or {}).get(str(user_id), []))
        nm = clean(t.get("name")) or u
        gd = clean(t.get("guild") or "") or "—"
        blocks.append(
            f"{dot_of(t)} <b>{esc(nm)}</b>\n"
            f"├ 🆔 {cp(u)}\n"
            f"├ 🛡 {esc(gd)}\n"
            f"├ 📊 {t.get('n', 0)} change(s) · last {esc(ago(t.get('last')))}\n"
            f"└ 🔔 alerts {len(CATS) - len(off)}/{len(CATS)} ON")
        kb.append([InlineKeyboardButton(f"{dot_of(t)} {nm[:12]} 📋", callback_data=f"dt:{u}"),
                   InlineKeyboardButton("⚙️", callback_data=f"pf:{u}"),
                   InlineKeyboardButton("🛑", callback_data=f"ut:{u}")])
    return "\n\n".join(blocks), InlineKeyboardMarkup(kb)


async def track_cb(q, kind, val):
    """Inline-button handlers for the tracker. Never rate-limited (they are quick taps)."""
    user = q.from_user.id
    if kind == "tl":
        await q.answer()
        text, kb = track_list_text(user)
        await q.message.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)
        return
    uid, _, rest = val.partition(":")
    t = TRACKS.get(uid)
    if not t or user not in t["subs"]:
        await q.answer("You're not tracking this UID.", show_alert=True)
        return
    if kind == "dt":
        await q.answer()
        parts = details_parts(t, uid)
        for i, part in enumerate(parts):
            await q.message.reply_text(part, parse_mode=ParseMode.HTML,
                                       reply_markup=with_add(track_kb(uid)) if i == len(parts) - 1 else None)
        return
    if kind == "pf":
        await q.answer()
        text, kb = prefs_view(user, uid)
        await q.message.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)
        return
    off = t.setdefault("off", {}).setdefault(str(user), [])
    toast = ""
    if kind == "pt" and rest in CAT:
        if rest in off:
            off.remove(rest)
            toast = f"{CAT[rest][1]}: ON ✅"
        else:
            off.append(rest)
            toast = f"{CAT[rest][1]}: OFF ❌"
    elif kind == "pa":
        off[:] = [] if rest == "1" else [k for k, _, _ in CATS]
        toast = "All ON ✅" if rest == "1" else "All OFF ❌"
    elif kind == "pd":
        await tstore_save()
        on = [f"{e} {n}" for k, e, n in CATS if k not in off]
        await q.answer("Saved ✅")
        body = "\n".join(f"• {esc(x)}" for x in on) if on else "• (nothing — all alerts are OFF)"
        try:
            await q.message.edit_text(f"💾 <b>{fx('Saved')}</b> — alerts you'll get for {dot_of(t)} <b>{esc(clean(t.get('name')) or uid)}</b>:\n{body}",
                                      parse_mode=ParseMode.HTML, reply_markup=track_kb(uid))
        except Exception:
            pass
        return
    await tstore_save()
    await q.answer(toast)
    text, kb = prefs_view(user, uid)
    try:
        await q.message.edit_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)
    except Exception as e:
        log.info("prefs edit skipped: %r", e)


def _free_color():
    used = {t.get("color") for t in TRACKS.values()}
    for i in range(len(DOTS)):
        if i not in used:
            return i
    return len(TRACKS) % len(DOTS)


async def handle_track(update, ctx, msg, cmd, arg):
    if msg.chat.type != ChatType.PRIVATE:
        kb = InlineKeyboardMarkup([[InlineKeyboardButton("🔒 Open private chat", url=f"https://t.me/{ctx.bot.username}")]])
        await rt(msg, f"🔒 <b>{fx('Private only')}</b>\nTracking works only in my private chat.", parse_mode=ParseMode.HTML, reply_markup=kb)
        return
    user = update.effective_user.id
    a = (arg or "").split()
    word = a[0].lower() if a else ""
    if cmd == "tracklist" or (cmd == "track" and (not a or word in ("list", "ls"))):
        text, kb = track_list_text(user)
        await rt(msg, text, parse_mode=ParseMode.HTML, reply_markup=kb)
        return
    if cmd == "untrack" or word in ("off", "stop", "remove", "del", "delete"):
        rest = a[1:] if cmd == "track" else a
        if not rest:
            text, kb = track_list_text(user)
            await rt(msg, "Usage: <code>/untrack &lt;uid&gt;</code> or <code>/untrack all</code>\n\n" + text, parse_mode=ParseMode.HTML, reply_markup=kb)
            return
        targets = mine(user) if rest[0].lower() == "all" else [rest[0]]
        done = []
        for u in targets:
            if u in TRACKS and user in TRACKS[u]["subs"]:
                TRACKS[u]["subs"].remove(user)
                (TRACKS[u].get("off") or {}).pop(str(user), None)
                if not TRACKS[u]["subs"]:
                    TRACKS.pop(u, None)
                done.append(u)
        if done:
            await tstore_save()
        await rt(msg, f"🛑 Stopped tracking: {', '.join(cp(u) for u in done)}" if done else "You weren't tracking that UID.", parse_mode=ParseMode.HTML)
        return
    uid = word
    if not UID_RE.match(uid):
        await rt(msg, "Usage: <code>/track &lt;uid&gt;</code>\nExample: <code>/track 6118588149</code>", parse_mode=ParseMode.HTML)
        return
    if limited(user):
        await rt(msg, "⏳ Slow down a little.")
        return
    if user in (TRACKS.get(uid) or {}).get("subs", []):
        await rt(msg, f"✅ Already tracking {cp(uid)}.", parse_mode=ParseMode.HTML, reply_markup=track_kb(uid))
        return
    if len(mine(user)) >= MAX_PER_USER:
        await rt(msg, f"You can track up to <b>{MAX_PER_USER}</b> players. Stop one first: /untrack &lt;uid&gt;", parse_mode=ParseMode.HTML)
        return
    if uid not in TRACKS and len(TRACKS) >= MAX_TOTAL:
        await rt(msg, "The tracker is full right now. Please try again later.")
        return
    await action(msg, ChatAction.TYPING)
    try:
        js = await fetch_once(uid)
    except Exception as e:
        await rt(msg, f"❌ Couldn't fetch this player ({why(e)}). Check the UID and try again.")
        return
    b = js.get("basic_info") or {}
    snap = flatten_player(js)
    now = time.time()
    t = TRACKS.setdefault(uid, {"subs": [], "snap": snap, "base": dict(snap), "since": now, "n": 0, "log": [], "off": {},
                                "color": _free_color(), "guild": (js.get("clan_basic_info") or {}).get("clan_name", ""),
                                "name": b.get("nickname", ""), "fails": 0,
                                "due": now + random.uniform(TRACK_MIN, TRACK_MAX), "busy": False, "warned": False})
    if user not in t["subs"]:
        t["subs"].append(user)
    await tstore_save()
    cur_login = snap.get("basic_info.last_login_at")
    await rt(msg, f"{em('🛰')} <b>{fx('Tracking started')}</b>\n"
                  f"{dot_of(t)} <b>{esc(clean(b.get('nickname')) or uid)}</b>\n"
                  f"├ 🆔 UID {cp(uid)}\n"
                  f"├ 🛡 {esc(clean(t.get('guild') or '') or '—')}\n"
                  f"├ 🟢 Last login: {cp(tss(cur_login) if cur_login else '—')}\n"
                  f"└ ⏱ Checking every <b>{TRACK_MIN:g}–{TRACK_MAX:g} s</b>",
             parse_mode=ParseMode.HTML, reply_markup=track_kb(uid))
    text, kb = prefs_view(user, uid)  # ask permission: which alerts do you want?
    await msg.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)


# ───────────────────────── main ─────────────────────────
def keep_alive():
    port = os.getenv("PORT")
    if not port:
        return

    class H(BaseHTTPRequestHandler):
        def do_GET(self):
            self.send_response(200)
            self.end_headers()
            self.wfile.write(b"ok")

        def log_message(self, *a):
            pass

    threading.Thread(target=HTTPServer(("0.0.0.0", int(port)), H).serve_forever, daemon=True).start()


COMMANDS = [
    ("start", "Welcome"),
    ("help", "All commands & how to use"),
    ("info", "Full player profile: /info <uid>"),
    ("level", "Level, EXP & likes"),
    ("bio", "Player bio"),
    ("outfit", "Equipped outfit & weapon skins"),
    ("rank", "BR & CS rank"),
    ("login", "Created & last login"),
    ("clan", "Guild details"),
    ("leader", "Guild leader details"),
    ("pet", "Pet details"),
    ("item", "Item lookup: /item <id or name>"),
    ("track", "Live profile alerts (private chat only)"),
    ("tracklist", "Players you are tracking"),
    ("untrack", "Stop tracking"),
]


async def post_init(app):
    global BOT_USER
    BOT_USER = app.bot.username or ""
    await tstore_load()
    app.bot_data["track_task"] = asyncio.create_task(track_loop(app))
    try:
        await app.bot.set_my_commands([BotCommand(c, d) for c, d in COMMANDS])
    except Exception as e:
        log.warning("set_my_commands failed: %r", e)


async def on_error(update, ctx):
    log.warning("handler error: %r", ctx.error)


def main():
    if not BOT_TOKEN:
        raise SystemExit("Set the BOT_TOKEN environment variable.")
    if not PIL_OK:
        log.warning("Pillow not installed - image cards disabled (pip install Pillow)")
    ensure_font()
    keep_alive()
    app = (
        Application.builder()
        .token(BOT_TOKEN)
        .concurrent_updates(True)
        .connect_timeout(20)
        .read_timeout(30)
        .write_timeout(30)
        .pool_timeout(20)
        .post_init(post_init)
        .build()
    )
    app.add_error_handler(on_error)
    app.add_handler(CommandHandler("start", start))
    app.add_handler(CommandHandler("help", help_cmd))
    app.add_handler(CallbackQueryHandler(on_cb))
    app.add_handler(MessageHandler(filters.TEXT, router))
    log.info("Bot started")
    app.run_polling(allowed_updates=Update.ALL_TYPES, drop_pending_updates=True)


if __name__ == "__main__":
    main()
