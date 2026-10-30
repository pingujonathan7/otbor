#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
ОТБОР — сбор кандидатов из Google Картинок и ручной выбор кадра.

Вкладка «Сбор»: вставляешь разметку (целиком, с заголовками ЦЕЛЕВЫЕ /
ФАКТУРА / ВИДЕО) — программа по очереди открывает запросы в Google Картинках
в отдельном окне твоего Chrome и качает по 8 картинок (по 12, если нужно
два кадра). Раздел ВИДЕО пропускается.

Вкладка «Выбор»: сетка кандидатов, клик или цифра — кадр сохраняется
в «<Фамилия> ОТБОР/ЦЕЛЕВЫЕ|ФАКТУРА/<запрос>.jpg» (второй — «<запрос> 2.jpg»),
открывается следующий запрос.

Один раз в Chrome: «Вид» → «Разработчик» → «Разрешить JavaScript из Apple Events».
Запуск без сборки: `python3 otbor.py`.
"""

import html as htmlmod
import json
import math
import os
import queue
import random
import re
import shlex
import shutil
import subprocess
import sys
import tempfile
import threading
import time
import urllib.parse
import urllib.request
from concurrent.futures import ThreadPoolExecutor
import tkinter as tk
from tkinter import font as tkfont
from tkinter import ttk

APP_NAME = "ОТБОР"

STATE_DIR = os.path.join(
    os.path.expanduser("~"), "Library", "Application Support", "OtborApp"
)
STATE_FILE = os.path.join(STATE_DIR, "state.json")
OVERRIDE_DIR = os.path.join(STATE_DIR, "app")
OVERRIDE_FILE = os.path.join(OVERRIDE_DIR, "otbor.py")

DEFAULT_GEOM = "1180x860+60+40"

APP_VERSION = "0.3.0"
GITHUB_REPO = "pingujonathan7/otbor"

# ---------- сбор ----------
DEFAULT_SEARCH_URL = "https://www.google.com/search?q={q}&udm=2"
JOB_SUFFIX = " ОТБОР"                # «Капица ОТБОР»
OUT_SECTIONS = ("ЦЕЛЕВЫЕ", "ФАКТУРА")
DEFAULT_SECTION = "ЦЕЛЕВЫЕ"          # для строк без заголовка
CAND_DIRNAME = "_кандидаты"
PAGES_DIRNAME = "_страницы"
SAVE_FIRST_PAGES = 5                 # первые выдачи сохраняются для проверки разбора
PLAN_FILE = "список.json"
PAUSE_BETWEEN = (2.0, 4.5)
PAGE_TIMEOUT = 30
DL_WORKERS = 6
MORE_STEP = 8                        # «Ещё 8»
KEEP_EXT = (".jpg", ".png")          # остальное переводим в jpg
JPEG_QUALITY = 92
DEFAULT_DOWNLOADS = os.path.join(os.path.expanduser("~"), "Downloads")

QUERY_HINT_SEP = "||"
HAND = "pointinghand" if sys.platform == "darwin" else "hand2"


def need_for(frames):
    """Сколько кандидатов качать: 8 на один кадр, +4 на каждый следующий."""
    return 8 + 4 * max(0, frames - 1)


# иконка приложения (PNG в base64) — пока та же, что у «Запросов»
ICON_B64 = "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"

THEMES = {
    "dark": {
        "bg": "#1c1d21", "bar": "#26282d", "row": "#2c2f35", "row_hover": "#363a42",
        "fg": "#e8e9ec", "muted": "#8b8f98", "accent": "#4c8dff",
        "ok": "#5cc98a", "warn": "#e0b252", "danger": "#e2645c",
        "border": "#34373e", "field": "#32363d", "cell": "#24262b",
    },
    "light": {
        "bg": "#f1f2f4", "bar": "#e4e6ea", "row": "#ffffff", "row_hover": "#dfe8f8",
        "fg": "#1d1f24", "muted": "#6f7680", "accent": "#2f6fe0",
        "ok": "#24985a", "warn": "#b07415", "danger": "#cf4239",
        "border": "#cfd3d9", "field": "#ffffff", "cell": "#e7e9ed",
    },
}
# живая палитра — меняется на месте при смене темы
C = dict(THEMES["dark"])


# =====================================================================
# Общие помощники
# =====================================================================

def split_line(line):
    if QUERY_HINT_SEP in line:
        head, _, tail = line.partition(QUERY_HINT_SEP)
        head = head.strip()
        if head:
            return head, tail.strip()
    return line.strip(), ""


def _utf8_env():
    env = dict(os.environ)
    env["LANG"] = "en_US.UTF-8"
    env["LC_ALL"] = "en_US.UTF-8"
    env["LC_CTYPE"] = "UTF-8"
    return env


def copy_to_clipboard(root, text):
    try:
        subprocess.run(["pbcopy"], input=text.encode("utf-8"),
                       env=_utf8_env(), check=True)
        return
    except Exception:
        pass
    try:
        root.clipboard_clear()
        root.clipboard_append(text)
        root.update_idletasks()
    except Exception:
        pass


def paste_from_clipboard(root):
    try:
        out = subprocess.run(["pbpaste"], capture_output=True,
                             env=_utf8_env(), check=True)
        return out.stdout.decode("utf-8", "replace")
    except Exception:
        pass
    try:
        return root.clipboard_get()
    except Exception:
        return ""


def set_app_icon(root):
    try:
        img = tk.PhotoImage(data=ICON_B64)
        root.iconphoto(True, img)
        root._app_icon = img
    except Exception:
        pass


def file_base(query):
    """Имя файла = запрос. Меняем только «/», которого не бывает в именах
    macOS, и укорачиваем, лишь если имя не влезет в предел системы."""
    name = query.strip().replace("/", "-")
    name = "".join(ch for ch in name if ch >= " ")
    name = " ".join(name.split())
    while len(name.encode("utf-8")) > 230:
        name = name[:-1]
    return name.strip() or "без названия"


def frame_name(query, k):
    """0 -> «запрос», 1 -> «запрос 2», 2 -> «запрос 3»…"""
    base = file_base(query)
    return base if k == 0 else "%s %d" % (base, k + 1)


def choose_folder(current, prompt):
    start = current if current and os.path.isdir(current) else os.path.expanduser("~")
    script = (
        'set startHere to POSIX file "%s"\n'
        'set theFolder to choose folder with prompt "%s" default location startHere\n'
        'return POSIX path of theFolder'
    ) % (start.replace('"', ''), prompt.replace('"', ''))
    try:
        res = subprocess.run(["/usr/bin/osascript", "-e", script],
                             capture_output=True, timeout=300)
        if res.returncode == 0:
            path = res.stdout.decode("utf-8", "replace").strip()
            if path:
                return path.rstrip("/")
    except Exception:
        pass
    return None


def short_path(path):
    home = os.path.expanduser("~")
    if path and path.startswith(home):
        path = "~" + path[len(home):]
    return path or ""


def write_json(path, data):
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False, indent=1)
    os.replace(tmp, path)


def read_json(path):
    try:
        with open(path, encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        return None


# Карточки кандидатов пишут и сборщик, и экран выбора — по очереди.
MANIFEST_LOCK = threading.RLock()


# ---------- обновления ----------

def version_tuple(text):
    parts = []
    for chunk in re.split(r"[.\-+_]", (text or "").lstrip("vV")):
        if chunk.isdigit():
            parts.append(int(chunk))
        else:
            break
    return tuple(parts) or (0,)


def file_version(path):
    try:
        with open(path, encoding="utf-8") as f:
            for _ in range(200):
                line = f.readline()
                if not line:
                    break
                if line.startswith("APP_VERSION"):
                    return line.split("=", 1)[1].strip().strip('"\'')
    except Exception:
        pass
    return "0"


def run_override():
    try:
        here = os.path.abspath(globals().get("__file__") or "")
    except Exception:
        here = ""
    if here and here == os.path.abspath(OVERRIDE_FILE):
        return False
    if not os.path.exists(OVERRIDE_FILE):
        return False
    if version_tuple(file_version(OVERRIDE_FILE)) <= version_tuple(APP_VERSION):
        return False
    try:
        import runpy
        runpy.run_path(OVERRIDE_FILE, run_name="__main__")
        return True
    except Exception:
        try:
            os.replace(OVERRIDE_FILE, OVERRIDE_FILE + ".broken")
        except Exception:
            pass
        return False


def app_bundle_path():
    if not getattr(sys, "frozen", False):
        return None
    parts = os.path.abspath(sys.executable).split(os.sep)
    for i in range(len(parts) - 1, -1, -1):
        if parts[i].endswith(".app"):
            return os.sep.join(parts[: i + 1])
    return None


def http_get(url, timeout=30):
    try:
        res = subprocess.run(
            ["/usr/bin/curl", "-fsSL", "--max-time", str(timeout),
             "-H", "User-Agent: OtborApp", url],
            capture_output=True, timeout=timeout + 10,
        )
        if res.returncode == 0:
            return res.stdout
        detail = (res.stderr or b"").decode("utf-8", "replace").strip()
        raise RuntimeError("curl %s: %s" % (res.returncode, detail or "нет ответа"))
    except FileNotFoundError:
        pass
    req = urllib.request.Request(url, headers={"User-Agent": "OtborApp"})
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        return resp.read()


def http_download(url, path, timeout=300):
    try:
        res = subprocess.run(
            ["/usr/bin/curl", "-fL", "--max-time", str(timeout),
             "-H", "User-Agent: OtborApp", "-o", path, url],
            capture_output=True, timeout=timeout + 15,
        )
        if res.returncode == 0 and os.path.getsize(path) > 0:
            return
        detail = (res.stderr or b"").decode("utf-8", "replace").strip()
        raise RuntimeError("curl %s: %s" % (res.returncode, detail or "пустой файл"))
    except FileNotFoundError:
        pass
    req = urllib.request.Request(url, headers={"User-Agent": "OtborApp"})
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        with open(path, "wb") as f:
            shutil.copyfileobj(resp, f)


def fetch_latest_release():
    url = "https://api.github.com/repos/%s/releases/latest" % GITHUB_REPO
    data = json.loads(http_get(url).decode("utf-8"))
    tag = data.get("tag_name") or ""
    # В релизе может лежать и зип-обновление (только otbor.py), и собранное
    # приложение. Берём обновление: оно маленькое и ставится за секунду.
    zips = [a for a in data.get("assets") or []
            if (a.get("name") or "").lower().endswith(".zip")]
    zips.sort(key=lambda a: (0 if "update" in (a.get("name") or "").lower() else 1,
                             a.get("size") or 0))
    link = zips[0].get("browser_download_url") if zips else None
    return tag, link


def install_update(zip_url, bundle):
    work = tempfile.mkdtemp(prefix="otbor-update-")
    archive = os.path.join(work, "update.zip")
    http_download(zip_url, archive)
    unpacked = os.path.join(work, "unpacked")
    os.makedirs(unpacked, exist_ok=True)
    subprocess.run(["ditto", "-x", "-k", archive, unpacked], check=True)
    new_app = None
    new_src = None
    for root_dir, dirs, files in os.walk(unpacked):
        for name in dirs:
            if name.endswith(".app"):
                new_app = os.path.join(root_dir, name)
                break
        for name in files:
            if name == "otbor.py":
                new_src = os.path.join(root_dir, name)
        if new_app:
            break
    if new_app is None and new_src is not None:
        os.makedirs(OVERRIDE_DIR, exist_ok=True)
        shutil.copyfile(new_src, OVERRIDE_FILE + ".new")
        os.replace(OVERRIDE_FILE + ".new", OVERRIDE_FILE)
        shutil.rmtree(work, ignore_errors=True)
        return bundle
    if new_app is None:
        raise RuntimeError("в архиве нет ни .app, ни otbor.py")
    parked = bundle + ".old"
    if os.path.exists(parked):
        shutil.rmtree(parked, ignore_errors=True)
    os.rename(bundle, parked)
    try:
        subprocess.run(["ditto", new_app, bundle], check=True)
    except Exception:
        if not os.path.exists(bundle):
            os.rename(parked, bundle)
        raise
    subprocess.Popen(["/bin/sh", "-c", "sleep 8; rm -rf %s" % shlex.quote(parked)],
                     start_new_session=True)
    shutil.rmtree(work, ignore_errors=True)
    return bundle


# =====================================================================
# Картинки: формат, перевод в jpg, миниатюры (встроенный в macOS sips)
# =====================================================================

def image_ext(path):
    """Расширение по первым байтам; None — это не картинка."""
    try:
        if os.path.getsize(path) < 400:
            return None
        with open(path, "rb") as f:
            head = f.read(16)
    except Exception:
        return None
    if head.startswith(b"\xff\xd8\xff"):
        return ".jpg"
    if head.startswith(b"\x89PNG\r\n\x1a\n"):
        return ".png"
    if head[:6] in (b"GIF87a", b"GIF89a"):
        return ".gif"
    if head[:4] == b"RIFF" and head[8:12] == b"WEBP":
        return ".webp"
    if head[:4] in (b"II*\x00", b"MM\x00*"):
        return ".tif"
    if head[:2] == b"BM":
        return ".bmp"
    if head[4:8] == b"ftyp":
        brand = head[8:12]
        if brand in (b"avif", b"avis"):
            return ".avif"
        if brand in (b"heic", b"heix", b"mif1", b"msf1", b"hevc"):
            return ".heic"
    return None


def to_jpeg(src, dst):
    """webp/avif/heic/gif/tif/bmp -> jpg высокого качества. True — получилось."""
    try:
        res = subprocess.run(
            ["/usr/bin/sips", "-s", "format", "jpeg",
             "-s", "formatOptions", str(JPEG_QUALITY), src, "--out", dst],
            capture_output=True, timeout=60,
        )
        return res.returncode == 0 and image_ext(dst) == ".jpg"
    except Exception:
        return False


def make_thumb(src, dst, size):
    """PNG-миниатюра с длинной стороной size (Tk сам jpg не показывает)."""
    try:
        res = subprocess.run(
            ["/usr/bin/sips", "-Z", str(int(size)), "-s", "format", "png",
             src, "--out", dst],
            capture_output=True, timeout=60,
        )
        return res.returncode == 0 and os.path.exists(dst)
    except Exception:
        return False


def to_png(src, dst):
    """Любая картинка -> PNG без потерь (из него Tk вырезает кадр)."""
    try:
        res = subprocess.run(["/usr/bin/sips", "-s", "format", "png", src, "--out", dst],
                             capture_output=True, timeout=120)
        return res.returncode == 0 and image_ext(dst) == ".png"
    except Exception:
        return False


def image_size(path):
    """(ширина, высота) из заголовка jpg/png; (0, 0) — не смогли."""
    try:
        with open(path, "rb") as f:
            data = f.read(256 * 1024)
    except Exception:
        return 0, 0
    if data.startswith(b"\x89PNG") and len(data) >= 24:
        return int.from_bytes(data[16:20], "big"), int.from_bytes(data[20:24], "big")
    if data.startswith(b"\xff\xd8"):
        i = 2
        while i + 9 < len(data):
            if data[i] != 0xFF:
                i += 1
                continue
            marker = data[i + 1]
            if marker in (0xD8, 0x01) or 0xD0 <= marker <= 0xD7:
                i += 2
                continue
            seg = int.from_bytes(data[i + 2:i + 4], "big")
            if marker in (0xC0, 0xC1, 0xC2, 0xC3, 0xC5, 0xC6, 0xC7,
                          0xC9, 0xCA, 0xCB, 0xCD, 0xCE, 0xCF):
                h = int.from_bytes(data[i + 5:i + 7], "big")
                w = int.from_bytes(data[i + 7:i + 9], "big")
                return w, h
            i += 2 + seg
    return 0, 0


def normalize_image(path):
    """Файл с любой картинкой -> путь к jpg/png рядом (оригинал удаляется).
    None — это не картинка или перевести не вышло."""
    ext = image_ext(path)
    if not ext:
        return None
    base = os.path.splitext(path)[0]
    if ext in KEEP_EXT:
        dst = base + ext
        if dst != path:
            os.replace(path, dst)
        return dst
    dst = base + ".jpg"
    if dst == path:
        tmp = base + ".conv.jpg"
        ok = to_jpeg(path, tmp)
        if ok:
            os.replace(tmp, dst)
            return dst
        return None
    ok = to_jpeg(path, dst)
    try:
        os.remove(path)
    except Exception:
        pass
    return dst if ok else None


# =====================================================================
# Chrome через AppleScript
# =====================================================================

class ChromeError(Exception):
    """Без вмешательства человека сбор не пойдёт."""


CHROME_OPEN = """
on run argv
    set theURL to item 1 of argv
    set wantId to (item 2 of argv) as integer
    tell application "Google Chrome"
        set foundTab to missing value
        repeat with w in windows
            repeat with t in tabs of w
                if (id of t) is wantId then
                    set foundTab to t
                    exit repeat
                end if
            end repeat
            if foundTab is not missing value then exit repeat
        end repeat
        if foundTab is missing value then
            set newWin to make new window
            set foundTab to active tab of newWin
        end if
        set URL of foundTab to theURL
        return (id of foundTab) as text
    end tell
end run
"""

CHROME_READ = """
on run argv
    set wantId to (item 1 of argv) as integer
    set js to item 2 of argv
    tell application "Google Chrome"
        repeat with w in windows
            repeat with t in tabs of w
                if (id of t) is wantId then
                    if loading of t then return "__LOADING__"
                    set u to URL of t
                    set r to execute t javascript js
                    if r is missing value then set r to ""
                    return u & linefeed & r
                end if
            end repeat
        end repeat
        return "__NOTAB__"
    end tell
end run
"""

CHROME_FRONT = """
on run argv
    set wantId to (item 1 of argv) as integer
    tell application "Google Chrome"
        repeat with w in windows
            set i to 0
            repeat with t in tabs of w
                set i to i + 1
                if (id of t) is wantId then
                    set active tab index of w to i
                    set index of w to 1
                    activate
                    return "ok"
                end if
            end repeat
        end repeat
    end tell
    return "no"
end run
"""

# Вкладка для ручного поиска: своя, в окне, где нет вкладки сборщика.
CHROME_USER = """
on run argv
    set theURL to item 1 of argv
    set wantId to (item 2 of argv) as integer
    set botId to (item 3 of argv) as integer
    tell application "Google Chrome"
        set foundTab to missing value
        set foundWin to missing value
        repeat with w in windows
            repeat with t in tabs of w
                if (id of t) is wantId then
                    set foundTab to t
                    set foundWin to w
                    exit repeat
                end if
            end repeat
            if foundTab is not missing value then exit repeat
        end repeat
        if foundTab is missing value then
            repeat with w in windows
                set hasBot to false
                repeat with t in tabs of w
                    if (id of t) is botId then set hasBot to true
                end repeat
                if not hasBot then
                    set foundWin to w
                    exit repeat
                end if
            end repeat
            if foundWin is missing value then set foundWin to make new window
            set foundTab to make new tab at end of tabs of foundWin with properties {URL:theURL}
        else
            set URL of foundTab to theURL
        end if
        set idx to 0
        repeat with i from 1 to count of tabs of foundWin
            if (id of (tab i of foundWin)) is (id of foundTab) then set idx to i
        end repeat
        if idx > 0 then set active tab index of foundWin to idx
        set index of foundWin to 1
        activate
        return (id of foundTab) as text
    end tell
end run
"""

# Страница целиком + адреса страниц-источников у плиток со значком
# «Licensable» (по-русски «Лицензия…»). Значок ищем по тексту и поднимаемся
# к плитке, у которой есть data-lpage или внешняя ссылка.
LIC_SEP = "\n@@OTBOR-PAGE@@\n"
JS_HTML = r"""(function(){
  var out = [], seen = {};
  var rx = /^(licensable|лицензи[а-яё]*|лицензируем[а-яё]*)$/i;
  var all = document.querySelectorAll('span,div,a');
  for (var i = 0; i < all.length; i++) {
    var el = all[i];
    if (el.children.length > 2) continue;
    var t = (el.textContent || '').trim();
    if (t.length > 24 || !rx.test(t)) continue;
    var n = el, page = '';
    for (var up = 0; up < 10 && n && !page; up++) {
      if (n.getAttribute) {
        page = n.getAttribute('data-lpage') || '';
        if (!page && n.querySelector) {
          var a = n.querySelector('[data-lpage]');
          if (a) page = a.getAttribute('data-lpage');
        }
        if (!page && n.querySelector) {
          var links = n.querySelectorAll('a[href^="http"]');
          for (var j = 0; j < links.length; j++) {
            var h = links[j].href;
            if (h.indexOf('google.') < 0) { page = h; break; }
          }
        }
      }
      n = n.parentNode;
    }
    if (page && !seen[page]) { seen[page] = 1; out.push(page); }
  }
  return JSON.stringify(out) + "@@OTBOR-PAGE@@" + document.documentElement.outerHTML;
})()"""
JS_HREF = "String(location.href)"

_script_paths = {}


def _osa(name, body, args, timeout=40):
    path = _script_paths.get(name)
    if path is None or not os.path.exists(path):
        path = os.path.join(tempfile.gettempdir(), "otbor_%s.applescript" % name)
        with open(path, "w", encoding="utf-8") as f:
            f.write(body)
        _script_paths[name] = path
    res = subprocess.run(["/usr/bin/osascript", path] + [str(a) for a in args],
                         capture_output=True, timeout=timeout, env=_utf8_env())
    out = res.stdout.decode("utf-8", "replace")
    err = (res.stderr or b"").decode("utf-8", "replace").strip()
    if res.returncode != 0:
        low = err.lower()
        if "javascript" in low and ("apple" in low or "turned off" in low
                                    or "отключ" in low or "выключ" in low):
            raise ChromeError(
                "В Chrome выключено выполнение JavaScript из Apple Events.\n\n"
                "Chrome → меню «Вид» → «Разработчик» → "
                "«Разрешить JavaScript из Apple Events». Потом нажми «Собрать» ещё раз.")
        if "-1743" in err or "not authorized" in low or "не разрешено" in low:
            raise ChromeError(
                "macOS не разрешила программе управлять Chrome.\n\n"
                "Системные настройки → Конфиденциальность и безопасность → "
                "Автоматизация → ОТБОР (или Терминал) → включи Google Chrome.")
        raise RuntimeError(err or "osascript вернул код %s" % res.returncode)
    return out


def chrome_open(url, tab_id):
    out = _osa("open", CHROME_OPEN, [url, int(tab_id or 0)]).strip()
    if not out.isdigit():
        raise RuntimeError("Chrome вернул: %s" % (out or "пусто"))
    return int(out)


def chrome_read(tab_id, js):
    out = _osa("read", CHROME_READ, [int(tab_id), js], timeout=60)
    if out.startswith("__LOADING__"):
        return "loading", "", ""
    if out.startswith("__NOTAB__"):
        return "notab", "", ""
    url, _, text = out.partition("\n")
    return "ok", url.strip(), text


def chrome_front(tab_id):
    try:
        _osa("front", CHROME_FRONT, [int(tab_id)])
    except Exception:
        pass


def chrome_user_open(url, tab_id, bot_id):
    """-> (id вкладки, ошибка)."""
    try:
        out = _osa("user", CHROME_USER, [url, int(tab_id or 0), int(bot_id or 0)]).strip()
        if out.isdigit():
            return int(out), None
        err = "Chrome вернул: %s" % (out or "пусто")
    except Exception as exc:
        err = str(exc)
    try:
        subprocess.Popen(["/usr/bin/open", url])
    except Exception:
        pass
    return tab_id, err


def is_blocked(url, page=""):
    u = (url or "").lower()
    if "google." in u and "/sorry/" in u:
        return "captcha"
    if "consent.google" in u:
        return "consent"
    if page and 'id="captcha-form"' in page:
        return "captcha"
    return None


# =====================================================================
# Разбор выдачи Google Картинок
# =====================================================================

RX_TRIPLE = re.compile(r'\["(https?:(?:[^"\\]|\\.){4,2000}?)",\s*(\d{1,5}),\s*(\d{1,5})\]')
RX_IMGURL = re.compile(r'[?&]imgurl=([^&"\'\s<>]+)')
RX_OU = re.compile(r'"ou":"((?:[^"\\]|\\.)+)"')

SKIP_HOST_PARTS = ("gstatic.com", "google.com", "google.ru", "googleapis.com",
                   "gvt1.com", "doubleclick", "googleadservices")
JUNK_SIDE = 64      # не фильтр по размеру: так отсеиваются только значки сайтов


def _json_unescape(s):
    try:
        return json.loads('"%s"' % s)
    except Exception:
        return s.replace("\\u003d", "=").replace("\\u0026", "&").replace("\\/", "/")


def _usable(url):
    if not url.startswith(("http://", "https://")):
        return False
    host = urllib.parse.urlsplit(url).netloc.lower()
    if not host:
        return False
    if any(p in host for p in SKIP_HOST_PARTS) and "googleusercontent" not in host:
        return False
    tail = url.split("?")[0].lower()
    if tail.endswith((".svg", ".ico")):
        return False
    return True


RX_URL = re.compile(r'"(https?:(?:[^"\\]|\\.){4,1500}?)"')
IMG_TAIL = (".jpg", ".jpeg", ".png", ".webp", ".gif", ".avif", ".heic", ".bmp", ".tif")


def norm_page(url):
    """Адрес страницы для сравнения: без схемы, www, хвостового «/» и #."""
    u = (url or "").strip().split("#")[0]
    u = re.sub(r"^https?://", "", u, flags=re.I)
    if u.lower().startswith("www."):
        u = u[4:]
    return u.rstrip("/").lower()


def source_after(text, pos, img_url):
    """Первая ссылка на обычную страницу после тройки — страница-источник."""
    for m in RX_URL.finditer(text, pos, min(len(text), pos + 2500)):
        u = _json_unescape(m.group(1))
        host = urllib.parse.urlsplit(u).netloc.lower()
        if not host or u == img_url or "gstatic" in host or "google." in host:
            continue
        if u.split("?")[0].lower().endswith(IMG_TAIL):
            continue
        return u
    return ""


def split_payload(raw):
    """Ответ JS_HTML -> (страница, множество страниц со значком Licensable)."""
    head, sep, page = raw.partition("@@OTBOR-PAGE@@")
    if not sep:
        return raw, set()
    try:
        lic = {norm_page(u) for u in json.loads(head) if u}
    except Exception:
        lic = set()
    return page, lic


def parse_results(page, licensed=None):
    """Оригиналы по порядку выдачи: [{url, w, h, how, page, lic}]."""
    found, seen = [], set()
    licensed = licensed or set()

    def add(url, w, h, how, src=""):
        url = url.strip()
        if not _usable(url):
            return
        key = url.split("#")[0]
        if key in seen:
            return
        seen.add(key)
        found.append({"url": url, "w": w, "h": h, "how": how, "page": src,
                      "lic": bool(src) and norm_page(src) in licensed})

    for text in (page, htmlmod.unescape(page)):
        for m in RX_TRIPLE.finditer(text):
            url = _json_unescape(m.group(1))
            h, w = int(m.group(2)), int(m.group(3))
            if max(h, w) <= JUNK_SIDE:
                continue
            add(url, w, h, "triple", source_after(text, m.end(), url))
        if found:
            break
    plain = htmlmod.unescape(page)
    for m in RX_IMGURL.finditer(plain):
        add(urllib.parse.unquote(m.group(1)), 0, 0, "imgurl")
    for m in RX_OU.finditer(page):
        add(_json_unescape(m.group(1)), 0, 0, "ou")
    return found


# =====================================================================
# Скачивание кандидатов
# =====================================================================

UA = ("Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/131.0 Safari/537.36")


def origin_of(url):
    parts = url.split("/")
    if len(parts) >= 3:
        return parts[0] + "//" + parts[2] + "/"
    return url


def download_to(url, tmp_base):
    """Качаем, проверяем, переводим в jpg при надобности. -> (путь, ошибка)."""
    part = tmp_base + ".part"
    try:
        res = subprocess.run(
            ["/usr/bin/curl", "-sL", "--compressed", "--max-time", "25",
             "--connect-timeout", "8", "--max-filesize", "60000000",
             "-A", UA, "-e", origin_of(url),
             "-H", "Accept: image/avif,image/webp,image/apng,image/*,*/*;q=0.8",
             "-o", part, "-w", "%{http_code}", url],
            capture_output=True, timeout=40,
        )
        code = res.stdout.decode("ascii", "replace").strip()
        if res.returncode != 0:
            return None, "curl %s" % res.returncode
        if not code.startswith("2"):
            return None, "код %s" % code
        ext = image_ext(part)
        if not ext:
            return None, "не картинка"
        raw = tmp_base + ".raw" + ext
        os.replace(part, raw)
        path = normalize_image(raw)
        if not path:
            return None, "не перевелось в jpg (%s)" % ext
        return path, None
    except subprocess.TimeoutExpired:
        return None, "долго"
    except Exception as exc:
        return None, str(exc)[:60]
    finally:
        for leftover in (part,):
            if os.path.exists(leftover):
                try:
                    os.remove(leftover)
                except Exception:
                    pass


def fetch_candidates(pool, start, folder, need, first_num, stop_event):
    """Качаем pool[start:] по порядку выдачи, пока не наберём need.
    -> (новые файлы, ошибки, позиция в pool, с которой продолжать)."""
    got = {}
    errors = []
    pos = start
    with ThreadPoolExecutor(max_workers=min(DL_WORKERS, need + 2)) as ex:
        while len(got) < need and pos < len(pool) and not stop_event.is_set():
            wave = pool[pos: pos + max(need - len(got) + 2, 3)]
            futures = []
            for k, cand in enumerate(wave):
                rank = pos + k
                base = os.path.join(folder, ".dl_%03d" % rank)
                futures.append((rank, cand, ex.submit(download_to, cand["url"], base)))
            pos += len(wave)
            for rank, cand, fut in futures:
                path, err = fut.result()
                if path:
                    got[rank] = (path, cand)
                else:
                    errors.append("%s — %s" % (urllib.parse.urlsplit(cand["url"]).netloc, err))
    files = []
    ranks = sorted(got)
    if len(ranks) > need:
        # лишнее не выбрасываем из выдачи: «Ещё 8» начнёт с них
        pos = min(pos, ranks[need])
    for n, rank in enumerate(ranks):
        path, cand = got[rank]
        if n >= need:
            os.remove(path)
            continue
        ext = os.path.splitext(path)[1]
        name = "%02d%s" % (first_num + n, ext)
        os.replace(path, os.path.join(folder, name))
        w, h = image_size(os.path.join(folder, name))
        files.append({"file": name, "url": cand["url"], "w": w or cand["w"],
                      "h": h or cand["h"], "rank": rank + 1,
                      "site": urllib.parse.urlsplit(cand["url"]).netloc})
    return files, errors, pos


# =====================================================================
# Разметка -> задания
# =====================================================================

RX_SECTION = re.compile(
    r"^(ГЕРОЙ|ЦЕЛЕВЫЕ|ЦЕЛЕВОЙ|ФАКТУРА|ВИДЕО)(?:\s+по\s+(\d+)\s+кадр\w*)?\s*:?$",
    re.IGNORECASE)
SKIP_SECTIONS = ("ВИДЕО", "ГЕРОЙ")


def section_of(line):
    bare = line.strip().strip("#*_`> ").strip()
    m = RX_SECTION.match(bare)
    if not m:
        return None
    name = m.group(1).upper()
    if name == "ЦЕЛЕВОЙ":
        name = "ЦЕЛЕВЫЕ"
    return name, int(m.group(2) or 1)


def plan_items(lines):
    """Строки -> (задания, пропущено строк ВИДЕО, строк без раздела).

    С заголовками берём только строки под ЦЕЛЕВЫЕ и ФАКТУРА. Без заголовков —
    всё в ЦЕЛЕВЫЕ. Повтор одного запроса в разделе = ещё один кадр.
    """
    has_sections = any(section_of(l) for l in lines)
    section, frames = (None, 1)
    items, by_key, skipped, loose = [], {}, 0, 0
    for raw in lines:
        line = raw.strip()
        if not line or line.startswith(QUERY_HINT_SEP) or line.startswith("```"):
            continue
        sec = section_of(line)
        if sec:
            section, frames = sec
            continue
        if has_sections and section is None:
            continue
        if section in SKIP_SECTIONS:
            skipped += 1
            continue
        query, hint = split_line(line)
        if not query:
            continue
        sec_name = section or DEFAULT_SECTION
        if section is None:
            loose += 1
        key = (sec_name, file_base(query).lower())
        if key in by_key:
            item = by_key[key]
            item["frames"] += frames
            item["need"] = need_for(item["frames"])
            continue
        item = {"query": query, "hint": hint, "section": sec_name, "frames": frames,
                "need": need_for(frames),
                "folder": os.path.join(sec_name, file_base(query))}
        by_key[key] = item
        items.append(item)
    return items, skipped, loose


def job_dir(parent, hero):
    hero = " ".join((hero or "").split())
    if not parent or not hero:
        return ""
    return os.path.join(parent, file_base(hero) + JOB_SUFFIX)


def cand_root(job):
    return os.path.join(job, CAND_DIRNAME)


def manifest_path(job, item):
    return os.path.join(cand_root(job), item["folder"], "candidates.json")


def load_manifest(job, item):
    return read_json(manifest_path(job, item))


def save_manifest(job, item, data):
    with MANIFEST_LOCK:
        write_json(manifest_path(job, item), data)


def item_state(man):
    """pending — ещё не собран; ready — ждёт выбора; done — выбран/пропущен."""
    if not man:
        return "pending"
    if man.get("picked") or man.get("skipped"):
        return "done"
    if man.get("done") or man.get("fail"):
        return "ready"
    return "pending"


# =====================================================================
# Сборщик
# =====================================================================

class Collector(threading.Thread):
    def __init__(self, items, job, search_url, out_q):
        super().__init__(daemon=True)
        self.items = items
        self.job = job
        self.root_dir = cand_root(job)
        self.search_url = search_url
        self.q = out_q
        self.stop_event = threading.Event()
        self.run_event = threading.Event()
        self.run_event.set()
        self.tab = 0
        self.results = []
        self.saved_pages = 0

    def post(self, kind, **data):
        self.q.put((kind, data))

    def wait_if_paused(self):
        while not self.run_event.is_set() and not self.stop_event.is_set():
            time.sleep(0.3)

    def sleep(self, sec):
        end = time.time() + sec
        while time.time() < end and not self.stop_event.is_set():
            time.sleep(0.2)

    def load_page(self, url):
        attempts = 0
        while not self.stop_event.is_set():
            try:
                self.tab = chrome_open(url, self.tab)
            except ChromeError:
                raise
            except Exception as exc:
                attempts += 1
                if attempts >= 3:
                    raise ChromeError("Не получается открыть адрес в Chrome:\n%s" % exc)
                self.sleep(2)
                continue
            self.sleep(1.2)
            state, cur, page = "loading", "", ""
            started = time.time()
            while time.time() - started < PAGE_TIMEOUT and not self.stop_event.is_set():
                state, cur, page = chrome_read(self.tab, JS_HTML)
                if state != "loading":
                    break
                self.sleep(0.7)
            if state == "notab":
                self.tab = 0
                continue
            if state == "loading":
                raise RuntimeError("выдача не загрузилась за %d с" % PAGE_TIMEOUT)
            block = is_blocked(cur, page)
            if block:
                self.wait_unblock(block)
                continue
            return cur, page
        return "", ""

    def wait_unblock(self, what):
        self.post("blocked", what=what)
        chrome_front(self.tab)
        while not self.stop_event.is_set():
            self.sleep(3)
            try:
                state, cur, _ = chrome_read(self.tab, JS_HREF)
            except ChromeError:
                raise
            except Exception:
                continue
            if state == "notab":
                self.tab = 0
                break
            if state == "ok" and not is_blocked(cur):
                break
        self.post("unblocked")
        self.sleep(1.5)

    def do_item(self, item):
        folder = os.path.join(self.root_dir, item["folder"])
        os.makedirs(folder, exist_ok=True)
        for name in os.listdir(folder):
            if name.startswith(".dl_") or re.match(r"^\d\d\.\w+$", name):
                try:
                    os.remove(os.path.join(folder, name))
                except Exception:
                    pass
        url = self.search_url.replace("{q}", urllib.parse.quote_plus(item["query"]))
        t0 = time.time()
        cur, page = self.load_page(url)
        if self.stop_event.is_set():
            return None
        page, licensed = split_payload(page)
        parsed = parse_results(page, licensed)
        pool = [c for c in parsed if not c["lic"]]
        lic_skipped = len(parsed) - len(pool)
        files, errors, pos = fetch_candidates(pool, 0, folder, item["need"], 1,
                                              self.stop_event)
        if self.stop_event.is_set() and len(files) < item["need"]:
            return None
        self.saved_pages += 1
        if len(pool) < item["need"] or self.saved_pages <= SAVE_FIRST_PAGES:
            pages = os.path.join(self.root_dir, PAGES_DIRNAME)
            os.makedirs(pages, exist_ok=True)
            try:
                with open(os.path.join(pages, file_base(item["query"]) + ".html"),
                          "w", encoding="utf-8") as f:
                    f.write(page)
            except Exception:
                pass
        info = {
            "query": item["query"], "hint": item["hint"], "section": item["section"],
            "frames": item["frames"], "need": item["need"],
            "search_url": cur or url, "found": len(pool),
            "parsed_by": sorted({c["how"] for c in pool}),
            "licensable_skipped": lic_skipped,
            "licensable_pages": sorted(licensed)[:50],
            "files": files, "pool": [{"url": c["url"], "w": c["w"], "h": c["h"],
                                      "page": c.get("page", "")} for c in pool],
            "next": pos, "errors": errors[:30], "done": True,
            "seconds": round(time.time() - t0, 1),
            "collected_at": time.strftime("%Y-%m-%d %H:%M:%S"),
        }
        save_manifest(self.job, item, info)
        return info

    def run(self):
        total = len(self.items)
        self.post("start", total=total)
        try:
            for idx, item in enumerate(self.items):
                self.wait_if_paused()
                if self.stop_event.is_set():
                    break
                prev = load_manifest(self.job, item)
                if prev and (prev.get("done") or item_state(prev) == "done"):
                    self.results.append((item, prev, True))
                    self.post("item", idx=idx, item=item, info=prev, skipped=True)
                    continue
                self.post("progress", idx=idx, item=item)
                try:
                    info = self.do_item(item)
                except ChromeError:
                    raise
                except Exception as exc:
                    info = {"query": item["query"], "hint": item["hint"],
                            "section": item["section"], "frames": item["frames"],
                            "need": item["need"], "found": 0, "files": [], "pool": [],
                            "next": 0, "errors": [str(exc)], "done": False,
                            "fail": str(exc)}
                    try:
                        os.makedirs(os.path.dirname(manifest_path(self.job, item)),
                                    exist_ok=True)
                        save_manifest(self.job, item, info)
                    except Exception:
                        pass
                if info is None:
                    break
                self.results.append((item, info, False))
                self.post("item", idx=idx, item=item, info=info, skipped=False)
                if idx < total - 1:
                    self.sleep(random.uniform(*PAUSE_BETWEEN))
        except ChromeError as exc:
            self.post("fatal", text=str(exc))
        finally:
            report = self.write_report()
            self.post("finish", stopped=self.stop_event.is_set(), report=report)

    def write_report(self):
        path = os.path.join(self.root_dir, "отчёт.txt")
        full = part = empty = 0
        lines = []
        for item, info, skipped in self.results:
            n = len(info.get("files") or [])
            need = item["need"]
            if n >= need:
                full += 1
            elif n:
                part += 1
            else:
                empty += 1
            mark = "OK " if n >= need else ("МАЛО" if n else "ПУСТО")
            row = "%-4s %2d/%-2d найдено %3s  %s · %s" % (
                mark, n, need, info.get("found", 0), item["section"], item["query"])
            if info.get("parsed_by"):
                row += "   [%s]" % ",".join(info["parsed_by"])
            if info.get("licensable_skipped"):
                row += "   licensable убрано: %d" % info["licensable_skipped"]
            if info.get("fail"):
                row += "   ошибка: %s" % info["fail"]
            if skipped:
                row += "   (собрано раньше)"
            lines.append(row)
        head = [
            "ОТБОР v%s — %s" % (APP_VERSION, time.strftime("%Y-%m-%d %H:%M")),
            "Запросов: %d   полных: %d   неполных: %d   пустых: %d"
            % (len(self.results), full, part, empty), "",
        ]
        try:
            with open(path, "w", encoding="utf-8") as f:
                f.write("\n".join(head + lines) + "\n")
            return path
        except Exception:
            return None


# =====================================================================
# Интерфейс: мелочи
# =====================================================================

class IconButton(tk.Label):
    def __init__(self, master, text, command, bg=None, fg=None, font=None,
                 pad=(10, 5), **kw):
        bg = bg if bg is not None else C["bar"]
        fg = fg if fg is not None else C["fg"]
        super().__init__(master, text=text, bg=bg, fg=fg, font=font,
                         padx=pad[0], pady=pad[1], cursor=HAND, **kw)
        self._bg = bg
        self._fg = fg
        self._command = command
        self.enabled = True
        self.bind("<Button-1>", lambda e: self._command() if self.enabled else None)
        self.bind("<Enter>", lambda e: self.configure(bg=C["row_hover"]) if self.enabled else None)
        self.bind("<Leave>", lambda e: self.configure(bg=self._bg))

    def restyle(self, bg=None, fg=None):
        if bg is not None:
            self._bg = bg
        if fg is not None:
            self._fg = fg
        self.configure(bg=self._bg, fg=self._fg if self.enabled else C["muted"])

    def set_enabled(self, on):
        self.enabled = on
        self.configure(fg=self._fg if on else C["muted"],
                       cursor=HAND if on else "arrow")


# =====================================================================
# Экран выбора
# =====================================================================

class Picker:
    """Вкладка «Выбор»: сетка кандидатов текущего запроса."""

    GAP = 10
    CAPTION_H = 34

    def __init__(self, app, parent):
        self.app = app
        self.root = app.root
        self.frame = tk.Frame(parent, bg=C["bg"])
        self.plan = []
        self.job = ""
        self.idx = None              # текущий запрос в self.plan
        self.man = None
        self.selected = []           # номера файлов в порядке клика
        self.active = 0              # рамка: одиночный клик / стрелки
        self._cols = 4
        self.cells = []
        self.images = {}
        self.undo_stack = []
        self.preview = None
        self.manual = None           # ожидание картинки в Загрузках
        self.user_tab = 0
        self._thumb_job = 0
        self._render_size = None
        self._resize_job = None
        self._poll_job = None
        self._busy_more = False
        self.build()

    # ---------- построение ----------
    def build(self):
        f = self.app
        top = tk.Frame(self.frame, bg=C["bg"])
        top.pack(side="top", fill="x", padx=14, pady=(12, 0))
        self.lbl_where = tk.Label(top, text="", bg=C["bg"], fg=C["muted"],
                                  font=f.f_small, anchor="w")
        self.lbl_where.pack(side="left")
        self.lbl_frames = tk.Label(top, text="", bg=C["bg"], fg=C["warn"],
                                   font=f.f_small, anchor="e")
        self.lbl_frames.pack(side="right")
        self.lbl_query = tk.Label(self.frame, text="", bg=C["bg"], fg=C["fg"],
                                  font=f.f_big, anchor="w", justify="left")
        self.lbl_query.pack(side="top", fill="x", padx=14, pady=(2, 0))
        self.lbl_hint = tk.Label(self.frame, text="", bg=C["bg"], fg=C["muted"],
                                 font=f.f_small, anchor="w", justify="left")
        self.lbl_hint.pack(side="top", fill="x", padx=14)

        bottom = tk.Frame(self.frame, bg=C["bar"])
        bottom.pack(side="bottom", fill="x")
        self.btn_undo = IconButton(bottom, "↺ Отменить  ⌘Z", self.undo, font=f.f_small,
                                   fg=C["muted"], pad=(10, 8))
        self.btn_undo.pack(side="left", padx=(6, 0))
        self.btn_done = IconButton(bottom, "Готово", self.commit_selected, bg=C["accent"],
                                   fg="#ffffff", font=f.f_ui, pad=(14, 6))
        self.btn_more = IconButton(bottom, "Ещё 8", self.more, font=f.f_ui, pad=(12, 6))
        self.btn_manual = IconButton(bottom, "Искать сам", self.manual_search,
                                     font=f.f_ui, pad=(12, 6))
        self.btn_skip = IconButton(bottom, "Пропустить", self.skip, font=f.f_ui,
                                   fg=C["muted"], pad=(12, 6))
        for b in (self.btn_skip, self.btn_manual, self.btn_more):
            b.pack(side="right", padx=(0, 6), pady=6)
        self.lbl_info = tk.Label(bottom, text="", bg=C["bar"], fg=C["muted"],
                                 font=f.f_small, anchor="w")
        self.lbl_info.pack(side="left", padx=10)

        self.grid = tk.Frame(self.frame, bg=C["bg"])
        self.grid.pack(side="top", fill="both", expand=True, padx=14, pady=10)
        self.grid.bind("<Configure>", self.on_grid_resize)

        # экран «всё выбрано» / «ждём сбор»
        self.msg = tk.Frame(self.frame, bg=C["bg"])
        self.msg_title = tk.Label(self.msg, text="", bg=C["bg"], fg=C["fg"], font=f.f_big)
        self.msg_title.pack(pady=(80, 8))
        self.msg_body = tk.Label(self.msg, text="", bg=C["bg"], fg=C["muted"],
                                 font=f.f_ui, justify="center")
        self.msg_body.pack()
        self.msg_btns = tk.Frame(self.msg, bg=C["bg"])
        self.msg_btns.pack(pady=18)

    # ---------- план и текущий запрос ----------
    def load(self, job):
        """Подхватываем список выбранного ролика."""
        self.job = job
        data = read_json(os.path.join(cand_root(job), PLAN_FILE)) if job else None
        self.plan = (data or {}).get("items") or []
        self.idx = None
        self.show_current()

    def counts(self):
        done = ready = pending = skipped = 0
        for it in self.plan:
            man = load_manifest(self.job, it)
            st = item_state(man)
            if st == "done":
                done += 1
                if man.get("skipped"):
                    skipped += 1
            elif st == "ready":
                ready += 1
            else:
                pending += 1
        return done, ready, pending, skipped

    def first_open(self):
        for i, it in enumerate(self.plan):
            st = item_state(load_manifest(self.job, it))
            if st != "done":
                return i, st
        return None, "finished"

    def show_current(self):
        if self._poll_job:
            self.root.after_cancel(self._poll_job)
            self._poll_job = None
        self.close_preview()
        if not self.plan:
            self.show_message("Списка пока нет",
                              "Вставь разметку на вкладке «Сбор» и нажми «Собрать».\n"
                              "Выбирать можно, не дожидаясь конца сбора.")
            return
        i, st = self.first_open()
        if st == "finished":
            self.idx = None
            self.show_finished()
            return
        if st == "pending":
            self.idx = None
            running = self.app.collector is not None and self.app.collector.is_alive()
            it = self.plan[i]
            self.show_message(
                "Собираю: %s" % it["query"] if running else "Не собрано: %s" % it["query"],
                "Картинки появятся, как только сборщик дойдёт до этого запроса."
                if running else
                "Сбор остановлен. Нажми «Собрать» на вкладке «Сбор» — "
                "собранное пропустится, продолжится отсюда.")
            self._poll_job = self.root.after(1000, self.show_current)
            return
        if self.idx != i:
            self.idx = i
            self.selected = []
            self.active = 0
        self.man = load_manifest(self.job, self.plan[i])
        self.hide_message()
        self.render()
        self.app.update_tabs()

    # ---------- сообщения ----------
    def show_message(self, title, body, buttons=()):
        for w in self.msg_btns.winfo_children():
            w.destroy()
        for text, cmd, primary in buttons:
            IconButton(self.msg_btns, "  %s  " % text, cmd,
                       bg=C["accent"] if primary else C["row"],
                       fg="#ffffff" if primary else C["fg"],
                       font=self.app.f_ui, pad=(12, 7)).pack(side="left", padx=5)
        self.msg_title.configure(text=title)
        self.msg_body.configure(text=body)
        self.grid.pack_forget()
        self.lbl_query.configure(text="")
        self.lbl_hint.configure(text="")
        self.lbl_where.configure(text="")
        self.lbl_frames.configure(text="")
        self.lbl_info.configure(text="")
        self.msg.pack(side="top", fill="both", expand=True)
        for b in (self.btn_more, self.btn_manual, self.btn_skip):
            b.set_enabled(False)
        self.btn_done.pack_forget()
        self.app.update_tabs()

    def hide_message(self):
        self.msg.pack_forget()
        if not self.grid.winfo_ismapped():
            self.grid.pack(side="top", fill="both", expand=True, padx=14, pady=10)
        for b in (self.btn_more, self.btn_manual, self.btn_skip):
            b.set_enabled(True)

    def skipped_queries(self):
        out = []
        for it in self.plan:
            man = load_manifest(self.job, it)
            if man and man.get("skipped"):
                out.append(it["query"])
        return out

    def show_finished(self):
        done, _, _, skipped = self.counts()
        frames = 0
        for it in self.plan:
            man = load_manifest(self.job, it) or {}
            frames += len(man.get("picked") or [])
        body = "Сохранено кадров: %d\nв %s" % (frames, short_path(self.job))
        btns = [("Открыть папку", self.app.open_job, True)]
        if skipped:
            body += "\n\nПропущено запросов: %d" % skipped
            btns.append(("Скопировать пропущенные", self.copy_skipped, False))
        btns.append(("Кандидатов в Корзину", self.trash_candidates, False))
        self.show_message("Всё выбрано", body, btns)

    def copy_skipped(self):
        qs = self.skipped_queries()
        if qs:
            copy_to_clipboard(self.root, "\n".join(qs))
            self.app.set_status("скопировано: %d" % len(qs))

    def trash_candidates(self):
        path = cand_root(self.job)
        if not os.path.isdir(path):
            return
        script = 'tell application "Finder" to delete (POSIX file "%s" as alias)' % (
            path.replace('"', '\\"'))
        try:
            res = subprocess.run(["/usr/bin/osascript", "-e", script],
                                 capture_output=True, timeout=60)
            if res.returncode == 0:
                self.app.set_status("кандидаты в Корзине")
                self.plan = []
                self.show_message("Готово", "Кандидаты убраны в Корзину.")
                return
            err = res.stderr.decode("utf-8", "replace")
        except Exception as exc:
            err = str(exc)
        self.app.show_message("Не получилось убрать в Корзину", err)

    # ---------- сетка ----------
    def files(self):
        return list((self.man or {}).get("files") or [])

    def layout(self, n):
        w = max(self.grid.winfo_width(), 400)
        h = max(self.grid.winfo_height(), 300)
        cols = 4 if n <= 8 else (4 if n <= 12 else 5)
        rows = max(1, math.ceil(n / cols))
        cell_w = (w - self.GAP * (cols - 1)) / cols
        cell_h = (h - self.GAP * (rows - 1)) / rows - self.CAPTION_H
        size = int(min(cell_w, cell_h) - 8)
        size = max(100, size - size % 20)
        return cols, rows, size

    def on_grid_resize(self, _e=None):
        if self.idx is None:
            return
        if self._resize_job:
            self.root.after_cancel(self._resize_job)
        self._resize_job = self.root.after(250, self.render_if_resized)

    def render_if_resized(self):
        self._resize_job = None
        if self.idx is None:
            return
        _, _, size = self.layout(len(self.files()))
        if size != self._render_size:
            self.render()

    def render(self):
        it = self.plan[self.idx]
        files = self.files()
        done, ready, pending, _ = self.counts()
        total = len(self.plan)
        self.lbl_where.configure(
            text="%s   ·   %d из %d   ·   осталось %d"
            % (it["section"], self.idx + 1, total, total - done))
        self.lbl_query.configure(text=it["query"])
        self.lbl_hint.configure(text=it.get("hint") or "")
        self.update_frames_label()
        self.btn_undo.set_enabled(bool(self.undo_stack))

        for w in self.grid.winfo_children():
            w.destroy()
        self.cells = []
        self.images = {}
        if not files:
            why = (self.man or {}).get("fail")
            tk.Label(self.grid, text="Картинок не нашлось" + (": " + why if why else ""),
                     bg=C["bg"], fg=C["muted"], font=self.app.f_ui).pack(pady=60)
            tk.Label(self.grid, text="«Ещё 8» — попробовать дальше по выдаче, "
                                     "«Искать сам» — открыть запрос в Chrome",
                     bg=C["bg"], fg=C["muted"], font=self.app.f_small).pack()
            self.update_info()
            return

        cols, rows, size = self.layout(len(files))
        self._render_size = size
        self._cols = cols
        if self.active >= len(files):
            self.active = 0
        for c in range(cols):
            self.grid.grid_columnconfigure(c, weight=1, uniform="cell")
        for k, fdata in enumerate(files):
            cell = tk.Frame(self.grid, bg=C["cell"], highlightthickness=3,
                            highlightbackground=C["bg"], cursor=HAND)
            cell.grid(row=k // cols, column=k % cols, padx=self.GAP // 2,
                      pady=self.GAP // 2, sticky="nsew")
            holder = tk.Frame(cell, bg=C["cell"], width=size, height=size)
            holder.pack_propagate(False)
            holder.pack(side="top", padx=4, pady=(4, 0))
            img = tk.Label(holder, text="…", bg=C["cell"], fg=C["muted"],
                           font=self.app.f_small)
            img.pack(expand=True, fill="both")
            cap = tk.Label(cell, text=self.caption(k, fdata), bg=C["cell"],
                           fg=C["muted"], font=self.app.f_small, anchor="w")
            cap.pack(side="top", fill="x", padx=6, pady=(2, 4))
            for w in (cell, holder, img, cap):
                w.bind("<Button-1>", lambda e, k=k: self.set_active(k))
                w.bind("<Double-Button-1>", lambda e, k=k: self.choose(k))
            self.cells.append({"cell": cell, "img": img, "cap": cap})
        self.paint_selection()
        self.update_info()
        self.load_thumbs(size)

    def caption(self, k, fdata):
        num = "%d" % (k + 1) if k < 9 else " "
        dims = "%d×%d" % (fdata["w"], fdata["h"]) if fdata.get("w") else ""
        site = fdata.get("site") or urllib.parse.urlsplit(fdata.get("url", "")).netloc
        if site.startswith("www."):
            site = site[4:]
        parts = [p for p in (dims, site) if p]
        return "%s   %s" % (num, " · ".join(parts))

    def thumb_path(self, fdata, size):
        folder = os.path.join(cand_root(self.job), self.plan[self.idx]["folder"])
        return (os.path.join(folder, fdata["file"]),
                os.path.join(folder, ".thumbs", str(size),
                             os.path.splitext(fdata["file"])[0] + ".png"))

    def load_thumbs(self, size):
        self._thumb_job += 1
        job_id = self._thumb_job
        idx = self.idx
        todo = [(k,) + self.thumb_path(f, size) for k, f in enumerate(self.files())]
        nxt = self.next_ready_after(idx)

        def worker():
            for k, src, dst in todo:
                if job_id != self._thumb_job:
                    return
                if not os.path.exists(dst):
                    os.makedirs(os.path.dirname(dst), exist_ok=True)
                    make_thumb(src, dst, size)
                self.app.call_soon(lambda k=k, dst=dst: self.set_thumb(job_id, k, dst))
            # заранее готовим следующий запрос того же размера
            if nxt is not None:
                it = self.plan[nxt]
                man = load_manifest(self.job, it) or {}
                folder = os.path.join(cand_root(self.job), it["folder"])
                for fdata in man.get("files") or []:
                    if job_id != self._thumb_job:
                        return
                    dst = os.path.join(folder, ".thumbs", str(size),
                                       os.path.splitext(fdata["file"])[0] + ".png")
                    if not os.path.exists(dst):
                        os.makedirs(os.path.dirname(dst), exist_ok=True)
                        make_thumb(os.path.join(folder, fdata["file"]), dst, size)

        threading.Thread(target=worker, daemon=True).start()

    def next_ready_after(self, idx):
        for j in range(idx + 1, len(self.plan)):
            st = item_state(load_manifest(self.job, self.plan[j]))
            if st == "ready":
                return j
            if st == "pending":
                return None
        return None

    def set_thumb(self, job_id, k, path):
        if job_id != self._thumb_job or k >= len(self.cells):
            return
        try:
            photo = tk.PhotoImage(file=path)
        except Exception:
            self.cells[k]["img"].configure(text="не открылась")
            return
        self.images[k] = photo
        self.cells[k]["img"].configure(image=photo, text="")

    def set_active(self, k):
        if 0 <= k < len(self.cells):
            self.active = k
            self.paint_selection()

    def move_active(self, dx, dy):
        n = len(self.cells)
        if not n:
            return
        k = self.active + dx + dy * self._cols
        if 0 <= k < n:
            self.set_active(k)

    def paint_selection(self):
        for k, c in enumerate(self.cells):
            if k in self.selected:
                color = C["ok"]
            elif k == self.active:
                color = C["accent"]
            else:
                color = C["bg"]
            c["cell"].configure(highlightbackground=color, highlightcolor=color)
            fdata = self.files()[k]
            text = self.caption(k, fdata)
            if k in self.selected and self.frames_needed() > 1:
                text = "✓%d  " % (self.selected.index(k) + 1) + text
            c["cap"].configure(text=text, fg=C["ok"] if k in self.selected else C["muted"])

    def frames_needed(self):
        if self.idx is None:
            return 1
        return int(self.plan[self.idx].get("frames") or 1)

    def update_frames_label(self):
        need = self.frames_needed()
        if need > 1:
            self.lbl_frames.configure(text="нужно кадров: %d   выбрано: %d"
                                      % (need, len(self.selected)))
            if not self.btn_done.winfo_ismapped():
                self.btn_done.pack(side="right", padx=(0, 6), pady=6,
                                   before=self.btn_skip)
            on = bool(self.selected)
            self.btn_done.restyle(bg=C["accent"] if on else C["row"],
                                  fg="#ffffff" if on else C["muted"])
            self.btn_done.set_enabled(on)
            self.btn_done.configure(text="Готово (%d из %d)" % (len(self.selected), need))
        else:
            self.lbl_frames.configure(text="")
            self.btn_done.pack_forget()

    def update_info(self):
        man = self.man or {}
        left = max(0, len(man.get("pool") or []) - int(man.get("next") or 0))
        self.btn_more.set_enabled(left > 0 and not self._busy_more)
        tip = ("двойной клик или цифра — взять   ·   клик + пробел — крупно и обрезка"
               "   ·   стрелки, Enter")
        if self.manual:
            tip = "жду картинку в Загрузках… сохрани её в Chrome   ·   Esc — отмена"
        self.lbl_info.configure(text=tip, fg=C["warn"] if self.manual else C["muted"])

    # ---------- выбор ----------
    def choose(self, k):
        """Взять картинку k (двойной клик, цифра, Enter)."""
        if self.idx is None or k >= len(self.files()):
            return
        self.active = k
        self.close_preview()
        need = self.frames_needed()
        if need <= 1:
            self.selected = [k]
            self.paint_selection()
            self.root.after(120, self.commit_selected)
            return
        if k in self.selected:
            self.selected.remove(k)
        else:
            self.selected.append(k)
        self.paint_selection()
        self.update_frames_label()
        if len(self.selected) >= need:
            self.root.after(250, self.commit_selected)

    def commit_selected(self):
        if self.idx is None or not self.selected:
            return
        it = self.plan[self.idx]
        files = self.files()
        out_dir = os.path.join(self.job, it["section"])
        os.makedirs(out_dir, exist_ok=True)
        cand_dir = os.path.join(cand_root(self.job), it["folder"])
        picked = []
        try:
            for n, k in enumerate(self.selected):
                fdata = files[k]
                ext = os.path.splitext(fdata["file"])[1].lower()
                name = frame_name(it["query"], n) + ext
                # тот же кадр с другим расширением — убрать, чтобы КАДР не задвоил
                for other in KEEP_EXT:
                    if other != ext:
                        twin = os.path.join(out_dir, frame_name(it["query"], n) + other)
                        if os.path.exists(twin):
                            os.remove(twin)
                shutil.copy2(os.path.join(cand_dir, fdata["file"]),
                             os.path.join(out_dir, name))
                picked.append({"file": fdata["file"],
                               "out": os.path.join(it["section"], name)})
        except Exception as exc:
            self.app.show_message("Не удалось сохранить кадр", str(exc))
            return
        with MANIFEST_LOCK:
            man = load_manifest(self.job, it) or self.man
            man["picked"] = picked
            man.pop("skipped", None)
            save_manifest(self.job, it, man)
        self.undo_stack.append(("pick", self.idx, picked))
        self.app.set_status("сохранено: " + ", ".join(p["out"] for p in picked))
        self.cancel_manual()
        self.idx = None
        self.selected = []
        self.show_current()

    def skip(self):
        if self.idx is None:
            return
        it = self.plan[self.idx]
        with MANIFEST_LOCK:
            man = load_manifest(self.job, it) or self.man or {}
            man["skipped"] = True
            save_manifest(self.job, it, man)
        self.undo_stack.append(("skip", self.idx, None))
        self.app.set_status("пропущено: " + it["query"])
        self.cancel_manual()
        self.idx = None
        self.selected = []
        self.show_current()

    def undo(self):
        if not self.undo_stack:
            return
        kind, idx, picked = self.undo_stack.pop()
        it = self.plan[idx]
        with MANIFEST_LOCK:
            man = load_manifest(self.job, it) or {}
            if kind == "pick":
                for p in picked or []:
                    try:
                        os.remove(os.path.join(self.job, p["out"]))
                    except Exception:
                        pass
                man.pop("picked", None)
            else:
                man.pop("skipped", None)
            save_manifest(self.job, it, man)
        self.cancel_manual()
        self.idx = None
        self.selected = []
        self.app.set_status("отменено: " + it["query"])
        self.show_current()

    # ---------- «Ещё 8» ----------
    def more(self):
        if self.idx is None or self._busy_more:
            return
        it = self.plan[self.idx]
        man = load_manifest(self.job, it) or {}
        pool = man.get("pool") or []
        start = int(man.get("next") or 0)
        if start >= len(pool):
            self.app.set_status("в выдаче больше ничего — попробуй «Искать сам»")
            return
        self._busy_more = True
        self.btn_more.set_enabled(False)
        self.btn_more.configure(text="Качаю…")
        idx = self.idx
        folder = os.path.join(cand_root(self.job), it["folder"])
        first = self.next_num(man)

        def worker():
            files, errors, pos = fetch_candidates(pool, start, folder, MORE_STEP, first,
                                                  threading.Event())
            self.app.call_soon(lambda: self.more_done(idx, it, files, pos))

        threading.Thread(target=worker, daemon=True).start()

    @staticmethod
    def next_num(man):
        nums = [int(re.match(r"(\d+)", f["file"]).group(1))
                for f in man.get("files") or [] if re.match(r"\d+", f["file"])]
        return (max(nums) + 1) if nums else 1

    def more_done(self, idx, it, files, pos):
        self._busy_more = False
        self.btn_more.configure(text="Ещё 8")
        with MANIFEST_LOCK:
            man = load_manifest(self.job, it) or {}
            man["files"] = (man.get("files") or []) + files
            man["next"] = pos
            save_manifest(self.job, it, man)
        if not files:
            self.app.set_status("ничего не скачалось — попробуй «Искать сам»")
        if self.idx == idx:
            self.man = man
            self.render()

    # ---------- «Искать сам» ----------
    def manual_search(self):
        if self.idx is None:
            return
        it = self.plan[self.idx]
        url = self.app.search_url.replace("{q}", urllib.parse.quote_plus(it["query"]))
        bot = self.app.collector.tab if self.app.collector else 0
        idx = self.idx
        folder = self.app.downloads_dir
        self.manual = {"idx": idx, "dir": folder, "seen": self.snapshot(folder),
                       "sizes": {}}
        self.update_info()

        def worker():
            tab, err = chrome_user_open(url, self.user_tab, bot)
            self.user_tab = tab
            if err:
                self.app.call_soon(lambda: self.app.set_status("Chrome: " + err[:80]))

        threading.Thread(target=worker, daemon=True).start()
        self.root.after(800, self.poll_manual)

    @staticmethod
    def snapshot(folder):
        try:
            return set(os.listdir(folder))
        except Exception:
            return set()

    def poll_manual(self):
        m = self.manual
        if not m or m["idx"] != self.idx:
            return
        now = self.snapshot(m["dir"])
        for name in sorted(now - m["seen"]):
            low = name.lower()
            if low.startswith(".") or low.endswith((".crdownload", ".download", ".part", ".tmp")):
                continue
            path = os.path.join(m["dir"], name)
            try:
                size = os.path.getsize(path)
            except Exception:
                continue
            if m["sizes"].get(name) != size:         # ещё пишется
                m["sizes"][name] = size
                continue
            m["seen"].add(name)
            if image_ext(path):
                self.take_manual(path)
                return
        self.root.after(700, self.poll_manual)

    def take_manual(self, path):
        it = self.plan[self.idx]
        folder = os.path.join(cand_root(self.job), it["folder"])
        os.makedirs(folder, exist_ok=True)
        with MANIFEST_LOCK:
            man = load_manifest(self.job, it) or self.man or {}
            num = self.next_num(man)
            raw = os.path.join(folder, ".manual_%02d%s" % (num, image_ext(path)))
            try:
                shutil.move(path, raw)
            except Exception as exc:
                self.app.show_message("Не удалось забрать картинку", str(exc))
                return
            done = normalize_image(raw)
            if not done:
                self.app.set_status("картинка не перевелась в jpg — сохрани другую")
                self.root.after(700, self.poll_manual)
                return
            name = "%02d%s" % (num, os.path.splitext(done)[1])
            os.replace(done, os.path.join(folder, name))
            w, h = image_size(os.path.join(folder, name))
            man.setdefault("files", []).append(
                {"file": name, "url": "", "w": w, "h": h, "rank": 0, "site": "вручную"})
            man["done"] = True
            man.pop("fail", None)
            save_manifest(self.job, it, man)
        self.man = man
        self.manual = None
        k = len(man["files"]) - 1
        self.render()
        self.choose(k)
        try:
            self.root.lift()
        except tk.TclError:
            pass

    def cancel_manual(self):
        if self.manual:
            self.manual = None
            self.update_info()

    # ---------- крупный просмотр ----------
    def toggle_preview(self):
        if self.preview:
            self.close_preview()
            return
        if self.idx is None or not self.cells:
            return
        k = self.active if self.active < len(self.cells) else 0
        self.preview = Preview(self, k)

    def close_preview(self):
        if self.preview:
            pv, self.preview = self.preview, None
            pv.destroy()
            try:
                self.frame.focus_set()
            except tk.TclError:
                pass

    # ---------- обрезка ----------
    def cand_folder(self):
        return os.path.join(cand_root(self.job), self.plan[self.idx]["folder"])

    def drop_thumbs(self, fdata):
        stem = os.path.splitext(fdata["file"])[0]
        tdir = os.path.join(self.cand_folder(), ".thumbs")
        for dp, _, fn in os.walk(tdir):
            for name in fn:
                if name == stem + ".png" or name.startswith(stem + "_"):
                    try:
                        os.remove(os.path.join(dp, name))
                    except Exception:
                        pass

    def _store_dims(self, k, path, cropped):
        w, h = image_size(path)
        it = self.plan[self.idx]
        with MANIFEST_LOCK:
            man = load_manifest(self.job, it) or self.man
            f = man["files"][k]
            f["w"], f["h"] = w, h
            if cropped:
                f["cropped"] = True
            else:
                f.pop("cropped", None)
            save_manifest(self.job, it, man)
        self.man = man

    def apply_crop(self, k, box):
        """Вырезать box=(x1, y1, x2, y2) в пикселях оригинала. Оригинал
        до первой обрезки сохраняется как .orig_NN, его можно вернуть."""
        fdata = self.files()[k]
        folder = self.cand_folder()
        src = os.path.join(folder, fdata["file"])
        ext = os.path.splitext(src)[1].lower()
        orig = os.path.join(folder, ".orig_" + fdata["file"])
        if not os.path.exists(orig):
            shutil.copy2(src, orig)
        work_in = os.path.join(folder, ".crop_in.png")
        work_out = os.path.join(folder, ".crop_out.png")
        try:
            if ext == ".png":
                shutil.copyfile(src, work_in)
            elif not to_png(src, work_in):
                raise RuntimeError("не получилось открыть картинку для обрезки")
            img = tk.PhotoImage(file=work_in)
            W, H = img.width(), img.height()
            x1, y1, x2, y2 = box
            x1, x2 = max(0, min(W, int(x1))), max(0, min(W, int(x2)))
            y1, y2 = max(0, min(H, int(y1))), max(0, min(H, int(y2)))
            if x2 - x1 < 8 or y2 - y1 < 8:
                raise RuntimeError("слишком маленькая рамка")
            img.write(work_out, format="png", from_coords=(x1, y1, x2, y2))
            del img
            if ext == ".png":
                os.replace(work_out, src)
            else:
                tmp = src + ".new.jpg"
                if not to_jpeg(work_out, tmp):
                    raise RuntimeError("не получилось сохранить jpg")
                os.replace(tmp, src)
        finally:
            for w in (work_in, work_out):
                if os.path.exists(w):
                    try:
                        os.remove(w)
                    except Exception:
                        pass
        self.drop_thumbs(fdata)
        self._store_dims(k, src, True)

    def has_original(self, k):
        fdata = self.files()[k]
        return os.path.exists(os.path.join(self.cand_folder(), ".orig_" + fdata["file"]))

    def restore_original(self, k):
        fdata = self.files()[k]
        folder = self.cand_folder()
        orig = os.path.join(folder, ".orig_" + fdata["file"])
        if not os.path.exists(orig):
            return
        src = os.path.join(folder, fdata["file"])
        os.replace(orig, src)
        self.drop_thumbs(fdata)
        self._store_dims(k, src, False)


class Preview:
    """Крупный просмотр активной картинки + обрезка рамкой."""

    BAR_H = 64
    HANDLE = 5
    GRAB = 12
    RATIOS = (("Свободно", None), ("16:9", 16 / 9), ("4:3", 4 / 3), ("1:1", 1.0))

    def __init__(self, picker, k):
        self.p = picker
        self.app = picker.app
        self.root = picker.root
        self.k = k
        self.cropping = False
        self.ratio = None
        self.rect = None
        self.drag = None
        self.photo = None
        self.scale = 1.0
        self.busy = False

        sw, sh = self.root.winfo_screenwidth(), self.root.winfo_screenheight()
        self.max_w, self.max_h = int(sw * 0.92), int(sh * 0.86) - self.BAR_H
        self.sw, self.sh = sw, sh

        win = tk.Toplevel(self.root)
        win.configure(bg="#000000")
        win.transient(self.root)
        win.protocol("WM_DELETE_WINDOW", self.p.close_preview)
        self.win = win
        self.canvas = tk.Canvas(win, bg="#000000", highlightthickness=0,
                                width=480, height=320, cursor="crosshair")
        self.canvas.pack(side="top")
        self.canvas.bind("<ButtonPress-1>", self.on_press)
        self.canvas.bind("<B1-Motion>", self.on_drag)
        self.canvas.bind("<ButtonRelease-1>", self.on_release)
        self.canvas.bind("<Double-Button-1>", lambda e: None if self.cropping
                         else self.p.choose(self.k))

        f = self.app
        self.bar = tk.Frame(win, bg=C["bar"], height=self.BAR_H)
        self.bar.pack(side="bottom", fill="x")
        self.lbl = tk.Label(self.bar, text="", bg=C["bar"], fg=C["muted"],
                            font=f.f_small, anchor="w")
        self.lbl.pack(side="left", padx=12)
        # обычный режим
        self.view_btns = tk.Frame(self.bar, bg=C["bar"])
        IconButton(self.view_btns, "Выбрать  ⏎", lambda: self.p.choose(self.k),
                   bg=C["accent"], fg="#ffffff", font=f.f_ui, pad=(12, 6)).pack(side="right", padx=(6, 10))
        IconButton(self.view_btns, "Обрезать  C", self.start_crop, bg=C["row"],
                   font=f.f_ui, pad=(12, 6)).pack(side="right", padx=6)
        self.btn_restore = IconButton(self.view_btns, "Вернуть исходник", self.restore,
                                      bg=C["bar"], fg=C["warn"], font=f.f_small, pad=(8, 6))
        IconButton(self.view_btns, "Закрыть  пробел", self.p.close_preview, bg=C["bar"],
                   fg=C["muted"], font=f.f_small, pad=(8, 6)).pack(side="right", padx=6)
        # режим обрезки
        self.crop_btns = tk.Frame(self.bar, bg=C["bar"])
        IconButton(self.crop_btns, "Обрезать  ⏎", self.apply, bg=C["accent"], fg="#ffffff",
                   font=f.f_ui, pad=(12, 6)).pack(side="right", padx=(6, 10))
        IconButton(self.crop_btns, "Отмена  Esc", self.cancel_crop, bg=C["row"],
                   font=f.f_ui, pad=(12, 6)).pack(side="right", padx=6)
        self.ratio_btns = []
        for name, r in reversed(self.RATIOS):
            b = IconButton(self.crop_btns, name, lambda r=r: self.set_ratio(r), bg=C["bar"],
                           fg=C["muted"], font=f.f_small, pad=(8, 6))
            b.pack(side="right", padx=2)
            self.ratio_btns.append((r, b))
        self.view_btns.pack(side="right")
        self.load()
        win.focus_set()

    # ---------- картинка ----------
    def fdata(self):
        return self.p.files()[self.k]

    def src(self):
        return os.path.join(self.p.cand_folder(), self.fdata()["file"])

    def load(self):
        src = self.src()
        ow, oh = image_size(src)
        if not ow:
            ow, oh = self.fdata().get("w") or 1600, self.fdata().get("h") or 1200
        sc = min(self.max_w / ow, self.max_h / oh, 1.0)
        long_side = max(1, int(round(max(ow, oh) * sc)))
        stem = os.path.splitext(self.fdata()["file"])[0]
        dst = os.path.join(self.p.cand_folder(), ".thumbs", "big",
                           "%s_%d.png" % (stem, long_side))
        self.orig_size = (ow, oh)
        self.lbl.configure(text="%d   %d×%d   загружаю…" % (self.k + 1, ow, oh))

        def worker():
            if not os.path.exists(dst):
                os.makedirs(os.path.dirname(dst), exist_ok=True)
                make_thumb(src, dst, long_side)
            self.app.call_soon(lambda: self.show(dst))

        threading.Thread(target=worker, daemon=True).start()

    def show(self, path):
        if self.p.preview is not self:
            return
        try:
            photo = tk.PhotoImage(file=path)
        except Exception:
            self.lbl.configure(text="не открылась")
            return
        self.photo = photo
        w, h = photo.width(), photo.height()
        self.scale = self.orig_size[0] / float(w)
        self.canvas.configure(width=w, height=h)
        self.canvas.delete("all")
        self.canvas.create_image(0, 0, image=photo, anchor="nw")
        self.update_caption()
        if self.p.has_original(self.k):
            self.btn_restore.pack(side="right", padx=6)
        else:
            self.btn_restore.pack_forget()
        self.win.update_idletasks()
        ww, wh = self.win.winfo_reqwidth(), self.win.winfo_reqheight()
        self.win.geometry("+%d+%d" % (max(0, (self.sw - ww) // 2),
                                      max(0, (self.sh - wh) // 2 - 20)))
        if self.cropping:
            self.reset_rect()

    def update_caption(self):
        f = self.fdata()
        ow, oh = self.orig_size
        site = f.get("site") or ""
        if site.startswith("www."):
            site = site[4:]
        text = "%d   %d×%d" % (self.k + 1, ow, oh)
        if site:
            text += "   ·   " + site
        if f.get("cropped"):
            text += "   ·   обрезана"
        if self.cropping and self.rect:
            x1, y1, x2, y2 = self.rect_px()
            text = "рамка %d×%d   ·   тяни углы и края, внутри — двигать" % (x2 - x1, y2 - y1)
        self.lbl.configure(text=text)

    def destroy(self):
        try:
            self.win.destroy()
        except tk.TclError:
            pass

    # ---------- режим обрезки ----------
    def start_crop(self):
        if self.cropping or not self.photo:
            return
        self.cropping = True
        self.view_btns.pack_forget()
        self.crop_btns.pack(side="right")
        self.set_ratio(self.ratio, keep=False)

    def cancel_crop(self):
        if not self.cropping:
            return
        self.cropping = False
        self.rect = None
        self.canvas.delete("crop")
        self.crop_btns.pack_forget()
        self.view_btns.pack(side="right")
        self.update_caption()

    def set_ratio(self, r, keep=False):
        self.ratio = r
        for rr, b in self.ratio_btns:
            b.restyle(fg=C["accent"] if rr == r else C["muted"])
        self.reset_rect()

    def bounds(self):
        return self.photo.width(), self.photo.height()

    def reset_rect(self):
        W, H = self.bounds()
        if self.ratio is None:
            self.rect = [0.0, 0.0, float(W), float(H)]
        else:
            w = min(W, H * self.ratio)
            h = w / self.ratio
            x = (W - w) / 2
            y = (H - h) / 2
            self.rect = [x, y, x + w, y + h]
        self.draw()

    def rect_px(self):
        x1, y1, x2, y2 = self.rect
        ow, oh = self.orig_size
        s = self.scale
        return (max(0, int(round(x1 * s))), max(0, int(round(y1 * s))),
                min(ow, int(round(x2 * s))), min(oh, int(round(y2 * s))))

    def draw(self):
        cv = self.canvas
        cv.delete("crop")
        if not self.rect:
            return
        W, H = self.bounds()
        x1, y1, x2, y2 = self.rect
        # затемнение снаружи рамки
        shade = {"fill": "#000000", "outline": "", "tags": "crop"}
        if sys.platform != "darwin":
            shade["stipple"] = "gray50"
            for box in ((0, 0, W, y1), (0, y2, W, H), (0, y1, x1, y2), (x2, y1, W, y2)):
                cv.create_rectangle(*box, **shade)
        # трети
        for i in (1, 2):
            gx = x1 + (x2 - x1) * i / 3
            gy = y1 + (y2 - y1) * i / 3
            cv.create_line(gx, y1, gx, y2, fill="#bfc4cc", dash=(3, 4), tags="crop")
            cv.create_line(x1, gy, x2, gy, fill="#bfc4cc", dash=(3, 4), tags="crop")
        cv.create_rectangle(x1, y1, x2, y2, outline="#000000", width=3, tags="crop")
        cv.create_rectangle(x1, y1, x2, y2, outline="#ffffff", width=1, tags="crop")
        hs = self.HANDLE
        mx, my = (x1 + x2) / 2, (y1 + y2) / 2
        for hx, hy in ((x1, y1), (x2, y1), (x1, y2), (x2, y2),
                       (mx, y1), (mx, y2), (x1, my), (x2, my)):
            cv.create_rectangle(hx - hs, hy - hs, hx + hs, hy + hs, fill="#ffffff",
                                outline="#000000", tags="crop")
        self.update_caption()

    def hit(self, x, y):
        x1, y1, x2, y2 = self.rect
        g = self.GRAB
        edges = set()
        inside_y = y1 - g <= y <= y2 + g
        inside_x = x1 - g <= x <= x2 + g
        if abs(x - x1) <= g and inside_y:
            edges.add("l")
        elif abs(x - x2) <= g and inside_y:
            edges.add("r")
        if abs(y - y1) <= g and inside_x:
            edges.add("t")
        elif abs(y - y2) <= g and inside_x:
            edges.add("b")
        if edges:
            return edges
        if x1 < x < x2 and y1 < y < y2:
            return "move"
        return "new"

    def on_press(self, e):
        if not self.cropping or not self.rect:
            return
        mode = self.hit(e.x, e.y)
        if mode == "new":
            self.rect = [e.x, e.y, e.x, e.y]
            mode = {"r", "b"}
        self.drag = {"mode": mode, "x": e.x, "y": e.y, "rect": list(self.rect)}

    def on_drag(self, e):
        if not self.drag:
            return
        W, H = self.bounds()
        d = self.drag
        x1, y1, x2, y2 = d["rect"]
        dx, dy = e.x - d["x"], e.y - d["y"]
        if d["mode"] == "move":
            w, h = x2 - x1, y2 - y1
            nx = min(max(0, x1 + dx), W - w)
            ny = min(max(0, y1 + dy), H - h)
            self.rect = [nx, ny, nx + w, ny + h]
        else:
            ed = d["mode"]
            ex, ey = min(max(0, e.x), W), min(max(0, e.y), H)
            if "l" in ed:
                x1 = ex
            if "r" in ed:
                x2 = ex
            if "t" in ed:
                y1 = ey
            if "b" in ed:
                y2 = ey
            if x2 < x1:
                x1, x2 = x2, x1
            if y2 < y1:
                y1, y2 = y2, y1
            if self.ratio:
                x1, y1, x2, y2 = self.fit_ratio(x1, y1, x2, y2, ed, W, H)
            x2 = max(x2, x1 + 10)
            y2 = max(y2, y1 + 10)
            self.rect = [x1, y1, min(x2, W), min(y2, H)]
        self.draw()

    def fit_ratio(self, x1, y1, x2, y2, ed, W, H):
        r = self.ratio
        w, h = x2 - x1, y2 - y1
        if ed & {"l", "r"}:
            h = w / r
            if "t" in ed:
                y1 = y2 - h
            else:
                y2 = y1 + h
        else:
            w = h * r
            if "l" in ed:
                x1 = x2 - w
            else:
                x2 = x1 + w
        # не вылезать за картинку: ужимаем, сохраняя пропорцию
        if x1 < 0 or y1 < 0 or x2 > W or y2 > H:
            x1, y1 = max(0, x1), max(0, y1)
            x2, y2 = min(W, x2), min(H, y2)
            w = min(x2 - x1, (y2 - y1) * r)
            h = w / r
            if "l" in ed:
                x1 = x2 - w
            else:
                x2 = x1 + w
            if "t" in ed:
                y1 = y2 - h
            else:
                y2 = y1 + h
        return x1, y1, x2, y2

    def on_release(self, _e):
        self.drag = None

    def apply(self):
        if not self.cropping or not self.rect or self.busy:
            return
        box = self.rect_px()
        ow, oh = self.orig_size
        if box == (0, 0, ow, oh):
            self.cancel_crop()
            return
        self.busy = True
        self.lbl.configure(text="обрезаю…", fg=C["fg"])
        self.win.update_idletasks()
        try:
            self.p.apply_crop(self.k, box)
        except Exception as exc:
            self.busy = False
            self.lbl.configure(text="не вышло: %s" % exc, fg=C["danger"])
            return
        self.busy = False
        self.lbl.configure(fg=C["muted"])
        self.cancel_crop()
        self.p.render()
        self.load()

    def restore(self):
        self.p.restore_original(self.k)
        self.p.render()
        self.load()


# =====================================================================
# Главное окно# =====================================================================
# Главное окно
# =====================================================================

class App:
    CMD_MAP = {
        "v": "paste", "м": "paste", "c": "copy", "с": "copy",
        "x": "cut", "ч": "cut", "a": "all", "ф": "all",
        "z": "undo", "я": "undo",
    }
    KEYSYM_ALIAS = {
        "cyrillic_em": "м", "cyrillic_es": "с", "cyrillic_che": "ч",
        "cyrillic_ef": "ф", "cyrillic_ya": "я",
    }

    def __init__(self, root):
        self.root = root
        self.q = queue.Queue()
        self.collector = None
        self.total = 0
        self.done_count = 0
        self._save_job = None
        self._upd_busy = False
        self._upd_pending = None
        self.tab = "collect"
        self._space_down = False
        self._space_job = None
        self._log_hist = []

        st = self.load_state()
        self.theme = st.get("theme") if st.get("theme") in THEMES else "dark"
        C.update(THEMES[self.theme])
        self.parent_dir = st.get("parent_dir") or os.path.join(os.path.expanduser("~"), "Desktop")
        self.search_url = st.get("search_url") or DEFAULT_SEARCH_URL
        self.downloads_dir = st.get("downloads_dir") or DEFAULT_DOWNLOADS

        root.title(APP_NAME)
        root.configure(bg=C["bg"])
        root.geometry(st.get("geometry", DEFAULT_GEOM))
        root.minsize(820, 620)
        root.protocol("WM_DELETE_WINDOW", self.on_close)
        if not getattr(sys, "frozen", False):
            set_app_icon(root)

        self.f_ui = tkfont.Font(family="Helvetica", size=13)
        self.f_small = tkfont.Font(family="Helvetica", size=11)
        self.f_big = tkfont.Font(family="Helvetica", size=20)
        self.f_tab = tkfont.Font(family="Helvetica", size=13, weight="bold")
        self.f_mono = tkfont.Font(family="Menlo", size=11)

        self.hero_var = tk.StringVar(value=st.get("hero", ""))
        self.build()
        self.txt.insert("1.0", st.get("list_text", ""))
        self.txt.edit_modified(False)
        self.paint_hints()
        self.update_plan()
        self.update_job_label()
        self.set_idle_buttons()
        self.show_tab(st.get("tab") or "collect")

        root.bind_all("<Command-KeyPress>", self.on_command_key)
        root.bind_all("<KeyPress>", self.on_key, add="+")
        root.bind_all("<KeyRelease>", self.on_key_release, add="+")
        root.bind("<Configure>", self.on_configure)
        self.hero_var.trace_add("write", lambda *a: self.on_hero_change())
        root.after(150, self.drain)
        root.after(4000, self.silent_update_check)

    # ---------- построение ----------
    def build(self):
        bar = tk.Frame(self.root, bg=C["bar"])
        bar.pack(side="top", fill="x")
        self.btn_tab_collect = IconButton(bar, "Сбор", lambda: self.show_tab("collect"),
                                          font=self.f_tab, pad=(16, 8))
        self.btn_tab_collect.pack(side="left", padx=(6, 0))
        self.btn_tab_pick = IconButton(bar, "Выбор", lambda: self.show_tab("pick"),
                                       font=self.f_tab, pad=(16, 8))
        self.btn_tab_pick.pack(side="left")
        self.btn_ver = IconButton(bar, "Обновления · v" + APP_VERSION, self.updates_click,
                                  fg=C["muted"], font=self.f_small, pad=(7, 4))
        self.btn_ver.pack(side="right", padx=(0, 6))
        self.btn_theme = IconButton(bar, "Светлая" if self.theme == "dark" else "Тёмная",
                                    self.toggle_theme, fg=C["muted"], font=self.f_small,
                                    pad=(8, 4))
        self.btn_theme.pack(side="right")
        self.lbl_job = tk.Label(bar, text="", bg=C["bar"], fg=C["muted"], font=self.f_small)
        self.lbl_job.pack(side="right", padx=8)
        tk.Frame(self.root, bg=C["border"], height=1).pack(side="top", fill="x")

        self.status = tk.Label(self.root, text="", bg=C["bar"], fg=C["muted"],
                               font=self.f_small, anchor="w")
        self.status.pack(side="bottom", fill="x", ipady=4, ipadx=8)

        self.body = tk.Frame(self.root, bg=C["bg"])
        self.body.pack(side="top", fill="both", expand=True)
        self.collect_frame = tk.Frame(self.body, bg=C["bg"])
        self.build_collect(self.collect_frame)
        self.picker = Picker(self, self.body)

    def build_collect(self, parent):
        # герой и место
        row = tk.Frame(parent, bg=C["bg"])
        row.pack(side="top", fill="x", padx=12, pady=(12, 4))
        tk.Label(row, text="Фамилия героя", bg=C["bg"], fg=C["muted"],
                 font=self.f_small).pack(side="left")
        self.ent_hero = tk.Entry(row, textvariable=self.hero_var, width=22, bg=C["field"],
                                 fg=C["fg"], insertbackground=C["fg"], font=self.f_ui,
                                 relief="flat", highlightthickness=1,
                                 highlightbackground=C["border"], highlightcolor=C["accent"])
        self.ent_hero.pack(side="left", padx=(8, 16), ipady=3)
        tk.Label(row, text="Где создать", bg=C["bg"], fg=C["muted"],
                 font=self.f_small).pack(side="left")
        self.btn_parent = IconButton(row, "", self.pick_parent, bg=C["bg"], fg=C["accent"],
                                     font=self.f_small, pad=(6, 4))
        self.btn_parent.pack(side="left", padx=(4, 0))

        head = tk.Frame(parent, bg=C["bg"])
        head.pack(side="top", fill="x", padx=12, pady=(10, 4))
        tk.Label(head, text="Разметка — можно вставить ответ целиком",
                 bg=C["bg"], fg=C["muted"], font=self.f_small, anchor="w").pack(side="left")
        self.lbl_plan = tk.Label(head, text="", bg=C["bg"], fg=C["fg"],
                                 font=self.f_small, anchor="e")
        self.lbl_plan.pack(side="right")

        self.txt = tk.Text(parent, bg=C["field"], fg=C["fg"], insertbackground=C["fg"],
                           font=self.f_small, wrap="none", bd=0, highlightthickness=1,
                           highlightbackground=C["border"], highlightcolor=C["accent"],
                           padx=8, pady=6, undo=True, height=14)
        self.txt.pack(side="top", fill="x", padx=12)
        self.txt.bind("<<Modified>>", self.on_text_modified)
        self.txt.tag_configure("hint", foreground=C["muted"])
        self.txt.tag_configure("head", foreground=C["accent"])
        self.txt.tag_configure("skip", foreground=C["muted"], overstrike=True)

        row = tk.Frame(parent, bg=C["bg"])
        row.pack(side="top", fill="x", padx=12, pady=10)
        self.btn_go = IconButton(row, "  Собрать  ", self.start, bg=C["accent"],
                                 fg="#ffffff", font=self.f_ui, pad=(12, 6))
        self.btn_go.pack(side="left")
        self.btn_pause = IconButton(row, "Пауза", self.toggle_pause, bg=C["row"],
                                    font=self.f_ui, pad=(12, 6))
        self.btn_pause.pack(side="left", padx=(8, 0))
        self.btn_stop = IconButton(row, "Стоп", self.stop, bg=C["row"],
                                   font=self.f_ui, pad=(12, 6))
        self.btn_stop.pack(side="left", padx=(8, 0))
        self.btn_open = IconButton(row, "Открыть папку", self.open_job, bg=C["bg"],
                                   fg=C["muted"], font=self.f_small, pad=(8, 6))
        self.btn_open.pack(side="right")

        self.lbl_now = tk.Label(parent, text="", bg=C["bg"], fg=C["fg"],
                                font=self.f_ui, anchor="w", justify="left")
        self.lbl_now.pack(side="top", fill="x", padx=12)
        self.lbl_now_hint = tk.Label(parent, text="", bg=C["bg"], fg=C["muted"],
                                     font=self.f_small, anchor="w", justify="left")
        self.lbl_now_hint.pack(side="top", fill="x", padx=12)
        style = ttk.Style(self.root)
        try:
            style.theme_use("default")
        except tk.TclError:
            pass
        style.configure("K.Horizontal.TProgressbar", troughcolor=C["row"],
                        background=C["accent"], bordercolor=C["bg"],
                        lightcolor=C["accent"], darkcolor=C["accent"])
        self.pbar = ttk.Progressbar(parent, style="K.Horizontal.TProgressbar",
                                    mode="determinate", maximum=1, value=0)
        self.pbar.pack(side="top", fill="x", padx=12, pady=(6, 8))

        wrap = tk.Frame(parent, bg=C["bg"])
        wrap.pack(side="top", fill="both", expand=True, padx=12, pady=(0, 10))
        self.log = tk.Text(wrap, bg=C["row"], fg=C["fg"], font=self.f_mono, wrap="none",
                           bd=0, highlightthickness=0, padx=8, pady=6, state="disabled")
        sb = tk.Scrollbar(wrap, orient="vertical", command=self.log.yview)
        self.log.configure(yscrollcommand=sb.set)
        sb.pack(side="right", fill="y")
        self.log.pack(side="left", fill="both", expand=True)
        for tag, col in (("ok", C["ok"]), ("warn", C["warn"]), ("bad", C["danger"]),
                         ("muted", C["muted"]), ("accent", C["accent"])):
            self.log.tag_configure(tag, foreground=col)

    # ---------- тема ----------
    def toggle_theme(self):
        """Светлая/тёмная: окно пересобирается с новой палитрой, всё
        состояние (список, журнал, текущий выбор, отмены) сохраняется."""
        keep = {
            "text": self.txt.get("1.0", "end-1c"),
            "now": self.lbl_now.cget("text"), "now_hint": self.lbl_now_hint.cget("text"),
            "pmax": float(self.pbar.cget("maximum")), "pval": float(self.pbar.cget("value")),
            "status": self.status.cget("text"), "pause": self.btn_pause.cget("text"),
            "undo": list(self.picker.undo_stack), "user_tab": self.picker.user_tab,
        }
        old = self.picker
        old.close_preview()
        old.manual = None
        for job in (old._poll_job, old._resize_job):
            if job:
                try:
                    self.root.after_cancel(job)
                except tk.TclError:
                    pass
        old._thumb_job += 1000
        self.theme = "light" if self.theme == "dark" else "dark"
        C.update(THEMES[self.theme])
        for w in self.root.winfo_children():
            w.destroy()
        self.root.configure(bg=C["bg"])
        self.build()
        self.txt.insert("1.0", keep["text"])
        self.txt.edit_modified(False)
        self.paint_hints()
        self.update_plan()
        self.update_job_label()
        hist, self._log_hist = self._log_hist, []
        for parts in hist:
            self.log_line(parts)
        self.lbl_now.configure(text=keep["now"])
        self.lbl_now_hint.configure(text=keep["now_hint"])
        self.pbar.configure(maximum=keep["pmax"], value=keep["pval"])
        self.set_status(keep["status"])
        if self.busy():
            self.set_busy_buttons()
            self.btn_pause.configure(text=keep["pause"])
        else:
            self.set_idle_buttons()
        self.picker.undo_stack = keep["undo"]
        self.picker.user_tab = keep["user_tab"]
        self.show_tab(self.tab)
        self.schedule_save()

    # ---------- вкладки ----------
    def show_tab(self, name):
        self.tab = name
        if name == "pick":
            self.collect_frame.pack_forget()
            self.picker.frame.pack(fill="both", expand=True)
            self.picker.frame.focus_set()
            self.picker.load(self.job())
        else:
            self.picker.close_preview()
            self.picker.frame.pack_forget()
            self.collect_frame.pack(fill="both", expand=True)
        self.update_tabs()
        self.schedule_save()

    def update_tabs(self):
        on, off = C["fg"], C["muted"]
        self.btn_tab_collect.restyle(bg=C["bg"] if self.tab == "collect" else C["bar"],
                                     fg=on if self.tab == "collect" else off)
        self.btn_tab_pick.restyle(bg=C["bg"] if self.tab == "pick" else C["bar"],
                                  fg=on if self.tab == "pick" else off)
        label = "Выбор"
        if self.picker.plan:
            done, ready, pending, _ = self.picker.counts()
            if ready:
                label = "Выбор · %d ждут" % ready
        self.btn_tab_pick.configure(text=label)

    # ---------- папка ролика ----------
    def job(self):
        return job_dir(self.parent_dir, self.hero_var.get())

    def update_job_label(self):
        self.btn_parent.configure(text=short_path(self.parent_dir) or "выбрать…")
        j = self.job()
        self.lbl_job.configure(text=("→ " + short_path(j)) if j else "впиши фамилию героя")

    def on_hero_change(self):
        self.update_job_label()
        self.schedule_save()

    def pick_parent(self):
        if self.busy():
            self.set_status("место можно менять, когда сбор остановлен")
            return
        path = choose_folder(self.parent_dir, "Где создать папку «Фамилия ОТБОР»?")
        if path:
            self.parent_dir = path
            self.update_job_label()
            self.schedule_save()

    def open_job(self):
        j = self.job()
        target = j if j and os.path.isdir(j) else self.parent_dir
        if target and os.path.isdir(target):
            subprocess.Popen(["/usr/bin/open", target])

    def busy(self):
        return self.collector is not None and self.collector.is_alive()

    # ---------- журнал ----------
    def log_line(self, parts):
        self._log_hist.append(parts)
        if len(self._log_hist) > 3000:
            del self._log_hist[:500]
        self.log.configure(state="normal")
        for text, tag in parts:
            self.log.insert("end", text, tag or ())
        self.log.insert("end", "\n")
        self.log.see("end")
        self.log.configure(state="disabled")

    def set_status(self, text):
        self.status.configure(text=text)

    def set_idle_buttons(self):
        self.btn_go.set_enabled(True)
        self.btn_pause.set_enabled(False)
        self.btn_stop.set_enabled(False)
        self.btn_pause.configure(text="Пауза")
        self.ent_hero.configure(state="normal")

    def set_busy_buttons(self):
        self.btn_go.set_enabled(False)
        self.btn_pause.set_enabled(True)
        self.btn_stop.set_enabled(True)
        self.ent_hero.configure(state="disabled")

    # ---------- сбор ----------
    def start(self):
        if self.busy():
            return
        if not self.hero_var.get().strip():
            self.set_status("впиши фамилию героя — так будет называться папка")
            self.ent_hero.focus_set()
            return
        if not os.path.isdir(self.parent_dir):
            self.pick_parent()
            if not os.path.isdir(self.parent_dir):
                return
        items, _, _ = plan_items(self.txt.get("1.0", "end").splitlines())
        if not items:
            self.set_status("в разметке нет запросов для сбора")
            return
        job = self.job()
        try:
            for sec in OUT_SECTIONS:
                os.makedirs(os.path.join(job, sec), exist_ok=True)
            os.makedirs(cand_root(job), exist_ok=True)
            write_json(os.path.join(cand_root(job), PLAN_FILE),
                       {"version": 1, "hero": self.hero_var.get().strip(), "items": items})
        except Exception as exc:
            self.show_message("Не удалось создать папку", str(exc))
            return
        self.save_state()
        self.total = len(items)
        self.done_count = 0
        self.pbar.configure(maximum=max(1, self.total), value=0)
        self.log_line([("— сбор: %d запросов → %s" % (self.total, short_path(job)), "accent")])
        self.collector = Collector(items, job, self.search_url, self.q)
        self.set_busy_buttons()
        self.collector.start()
        if self.tab == "pick":
            self.picker.load(job)

    def toggle_pause(self):
        c = self.collector
        if not self.busy():
            return
        if c.run_event.is_set():
            c.run_event.clear()
            self.btn_pause.configure(text="Продолжить")
            self.set_status("пауза — текущий запрос докачается и сбор встанет")
        else:
            c.run_event.set()
            self.btn_pause.configure(text="Пауза")
            self.set_status("продолжаю")

    def stop(self):
        if self.busy():
            self.collector.stop_event.set()
            self.collector.run_event.set()
            self.set_status("останавливаю…")

    def call_soon(self, fn):
        """Из фоновых потоков в окно — только через очередь: Tk не любит,
        когда его трогают не из главного потока."""
        self.q.put(("call", {"fn": fn}))

    def drain(self):
        try:
            while True:
                kind, d = self.q.get_nowait()
                self.handle(kind, d)
        except queue.Empty:
            pass
        self.root.after(60, self.drain)

    def handle(self, kind, d):
        if kind == "call":
            try:
                d["fn"]()
            except tk.TclError:
                pass
            return
        if kind == "start":
            self.set_status("иду по списку…")
        elif kind == "progress":
            item = d["item"]
            self.lbl_now.configure(text="%d / %d   %s" % (d["idx"] + 1, self.total, item["query"]))
            self.lbl_now_hint.configure(text=item["section"] + (
                "   " + item["hint"] if item.get("hint") else ""))
        elif kind == "item":
            self.done_count += 1
            self.pbar.configure(value=self.done_count)
            info, item = d["info"], d["item"]
            n = len(info.get("files") or [])
            need = item["need"]
            num = "%3d " % (d["idx"] + 1)
            sec = "Ц " if item["section"] == "ЦЕЛЕВЫЕ" else "Ф "
            two = "  ×%d" % item["frames"] if item["frames"] > 1 else ""
            if d["skipped"]:
                self.log_line([(num, "muted"), (sec, "muted"), ("·  %2d  " % n, "muted"),
                               (item["query"], "muted"), ("  уже собрано", "muted")])
            elif info.get("fail"):
                self.log_line([(num, "muted"), (sec, "muted"), ("✗   0  ", "bad"),
                               (item["query"], None), ("  " + info["fail"][:80], "bad")])
            else:
                tag = "ok" if n >= need else ("warn" if n else "bad")
                mark = "✓" if n >= need else ("!" if n else "✗")
                extra = "" if n >= need else "  (нашёл %d)" % info.get("found", 0)
                if info.get("licensable_skipped"):
                    extra += "  licensable −%d" % info["licensable_skipped"]
                self.log_line([(num, "muted"), (sec, "muted"), ("%s %2d  " % (mark, n), tag),
                               (item["query"], None), (two, "accent"), (extra, "muted")])
            self.update_tabs()
        elif kind == "blocked":
            what = "капчу" if d["what"] == "captcha" else "согласие с условиями"
            self.set_status("Google просит %s — пройди в окне Chrome, я жду" % what)
            self.log_line([("     ⏸ Google просит %s — жду, пока пройдёшь в Chrome" % what, "warn")])
            try:
                self.root.bell()
            except tk.TclError:
                pass
        elif kind == "unblocked":
            self.set_status("продолжаю")
            self.log_line([("     ▶ продолжаю", "muted")])
        elif kind == "fatal":
            self.log_line([("✗ сбор остановлен", "bad")])
            self.show_message("Сбор остановлен", d["text"])
        elif kind == "finish":
            self.set_idle_buttons()
            self.lbl_now.configure(text="Остановлено" if d["stopped"] else "Сбор закончен")
            self.lbl_now_hint.configure(text="")
            if d.get("report"):
                self.set_status("отчёт: " + short_path(d["report"]))
            self.log_line([("— %s" % ("остановлено" if d["stopped"] else "готово"), "accent")])
            self.update_tabs()

    # ---------- текст разметки ----------
    def on_text_modified(self, _e=None):
        if self.txt.edit_modified():
            self.txt.edit_modified(False)
            self.paint_hints()
            self.update_plan()
            self.schedule_save()

    def paint_hints(self):
        for tag in ("hint", "head", "skip"):
            self.txt.tag_remove(tag, "1.0", "end")
        lines = self.txt.get("1.0", "end-1c").split("\n")
        has = any(section_of(l) for l in lines)
        section = None
        for n, line in enumerate(lines, 1):
            sec = section_of(line)
            if sec:
                section = sec[0]
                self.txt.tag_add("head", "%d.0" % n, "%d.end" % n)
                continue
            if line.strip() and ((has and section is None) or section in SKIP_SECTIONS):
                self.txt.tag_add("skip", "%d.0" % n, "%d.end" % n)
                continue
            pos = line.find(QUERY_HINT_SEP)
            if pos >= 0:
                self.txt.tag_add("hint", "%d.%d" % (n, pos), "%d.end" % n)

    def update_plan(self):
        items, skipped, loose = plan_items(self.txt.get("1.0", "end").splitlines())
        if not items:
            self.lbl_plan.configure(text="")
            return
        c = sum(1 for i in items if i["section"] == "ЦЕЛЕВЫЕ")
        f = len(items) - c
        frames = sum(i["frames"] for i in items)
        parts = ["запросов %d (целевые %d, фактура %d)" % (len(items), c, f),
                 "кадров %d" % frames]
        if skipped:
            parts.append("видео пропущено %d" % skipped)
        if loose:
            parts.append("без заголовка → ЦЕЛЕВЫЕ")
        self.lbl_plan.configure(text="  ·  ".join(parts))

    # ---------- клавиши ----------
    def on_key(self, event):
        if self.tab != "pick":
            return None
        w = event.widget
        if isinstance(w, (tk.Entry, tk.Text, tk.Spinbox)):
            return None
        if sys.platform == "darwin" and event.state & 0x8:    # с Cmd — не наше
            return None
        p = self.picker
        pv = p.preview
        ks = event.keysym
        ch = event.char or ""
        if ks == "space":
            # зажатый пробел шлёт повторы — открываем/закрываем один раз
            if self._space_job is not None:
                self.root.after_cancel(self._space_job)
                self._space_job = None
                return "break"
            if self._space_down:
                return "break"
            self._space_down = True
            if pv and pv.cropping:
                return "break"
            p.toggle_preview()
            return "break"
        if ks == "Escape":
            if pv and pv.cropping:
                pv.cancel_crop()
            elif pv:
                p.close_preview()
            else:
                p.cancel_manual()
            return "break"
        if ks in ("Return", "KP_Enter"):
            if pv and pv.cropping:
                pv.apply()
            elif pv:
                p.choose(pv.k)
            elif p.selected and p.frames_needed() > 1 and p.active in p.selected:
                p.commit_selected()
            else:
                p.choose(p.active)
            return "break"
        if pv:
            if ks.lower() in ("c", "cyrillic_es") and not pv.cropping:
                pv.start_crop()
                return "break"
            return None
        if ch and ch in "123456789":
            p.choose(int(ch) - 1)
            return "break"
        moves = {"Left": (-1, 0), "Right": (1, 0), "Up": (0, -1), "Down": (0, 1)}
        if ks in moves:
            p.move_active(*moves[ks])
            return "break"
        return None

    def on_key_release(self, event):
        if event.keysym != "space":
            return None
        if self._space_job is not None:
            self.root.after_cancel(self._space_job)

        def clear():
            self._space_job = None
            self._space_down = False

        self._space_job = self.root.after(90, clear)
        return None

    def on_command_key(self, event):
        key = (event.char or "").lower()
        if key not in self.CMD_MAP:
            ks = (event.keysym or "").lower()
            key = self.KEYSYM_ALIAS.get(ks, ks)
        action = self.CMD_MAP.get(key)
        w = event.widget
        is_entry = isinstance(w, (tk.Entry, tk.Spinbox))
        is_text = isinstance(w, tk.Text)
        if action == "undo" and self.tab == "pick" and not (is_entry or is_text):
            self.picker.undo()
            return "break"
        if action is None or not (is_entry or is_text):
            return None
        if action == "paste":
            data = paste_from_clipboard(self.root)
            if data:
                self.drop_selection(w, is_entry)
                w.insert("insert", data)
            return "break"
        if action in ("copy", "cut"):
            sel = self.get_selection(w, is_entry)
            if sel:
                copy_to_clipboard(self.root, sel)
                if action == "cut" and w is not self.log:
                    self.drop_selection(w, is_entry)
            return "break"
        if action == "all":
            if is_text:
                w.tag_add("sel", "1.0", "end-1c")
            else:
                w.selection_range(0, "end")
            return "break"
        if action == "undo" and is_text:
            try:
                w.edit_undo()
            except tk.TclError:
                pass
            return "break"
        return None

    @staticmethod
    def get_selection(w, is_entry):
        try:
            if is_entry:
                if not w.selection_present():
                    return ""
                return w.selection_get()
            return w.get("sel.first", "sel.last")
        except tk.TclError:
            return ""

    @staticmethod
    def drop_selection(w, is_entry):
        try:
            if is_entry:
                if w.selection_present():
                    w.delete("sel.first", "sel.last")
            else:
                w.delete("sel.first", "sel.last")
        except tk.TclError:
            pass

    # ---------- сообщения ----------
    def show_message(self, title, body):
        win = tk.Toplevel(self.root)
        win.title(title)
        win.configure(bg=C["bg"])
        win.transient(self.root)
        frame = tk.Frame(win, bg=C["bg"])
        frame.pack(fill="both", expand=True, padx=18, pady=16)
        tk.Label(frame, text=title, bg=C["bg"], fg=C["fg"], font=self.f_ui,
                 anchor="w").pack(anchor="w")
        txt = tk.Text(frame, bg=C["field"], fg=C["fg"], font=self.f_small, wrap="word",
                      bd=0, highlightthickness=1, highlightbackground=C["border"],
                      width=56, height=7, padx=8, pady=8)
        txt.pack(fill="both", expand=True, pady=(10, 12))
        txt.insert("1.0", body)
        IconButton(frame, "  Закрыть  ", win.destroy, bg=C["row"], font=self.f_ui,
                   pad=(10, 6)).pack(anchor="e")

    # ---------- обновления ----------
    def silent_update_check(self):
        if app_bundle_path() is None or self._upd_busy:
            return
        self._upd_busy = True
        threading.Thread(target=self._check_worker, args=(True,), daemon=True).start()

    def updates_click(self):
        if self._upd_pending:
            self.offer_update(*self._upd_pending)
            return
        if app_bundle_path() is None:
            self.set_status("обновления работают в собранном приложении, не при запуске из Терминала")
            return
        if self._upd_busy:
            return
        self._upd_busy = True
        self.btn_ver.configure(text="проверяю…")
        threading.Thread(target=self._check_worker, args=(False,), daemon=True).start()

    def _check_worker(self, silent):
        try:
            tag, link = fetch_latest_release()
            err = None
        except Exception as exc:
            tag, link, err = None, None, str(exc)
        self.call_soon(lambda: self._check_done(tag, link, err, silent))

    def _check_done(self, tag, link, err, silent):
        self._upd_busy = False
        self.btn_ver.configure(text="Обновления · v" + APP_VERSION)
        if err is not None:
            if not silent:
                self.show_message("Не удалось проверить обновления", err)
            return
        if not tag or version_tuple(tag) <= version_tuple(APP_VERSION):
            if not silent:
                self.show_message("Обновлений нет", "Установлена последняя версия: v%s" % APP_VERSION)
            return
        if not link:
            if not silent:
                self.set_status("в релизе нет файла")
            return
        self._upd_pending = (tag, link)
        self.btn_ver.restyle(fg=C["accent"])
        self.btn_ver.configure(text="Обновить до " + tag)
        if not silent:
            self.offer_update(tag, link)

    def offer_update(self, tag, link):
        if self.busy():
            self.set_status("обновиться можно после сбора")
            return
        win = tk.Toplevel(self.root)
        win.title("Обновление")
        win.configure(bg=C["bg"])
        win.resizable(False, False)
        win.transient(self.root)
        body = tk.Frame(win, bg=C["bg"])
        body.pack(fill="both", expand=True, padx=18, pady=16)
        tk.Label(body, text="Доступна версия " + tag, bg=C["bg"], fg=C["fg"],
                 font=self.f_ui).pack(anchor="w")
        state = tk.Label(body, text="Сейчас установлена v" + APP_VERSION,
                         bg=C["bg"], fg=C["muted"], font=self.f_small)
        state.pack(anchor="w", pady=(4, 14))
        btns = tk.Frame(body, bg=C["bg"])
        btns.pack(fill="x")

        def go():
            state.configure(text="Загружаю…", fg=C["fg"])
            for child in btns.winfo_children():
                child.destroy()
            win.update_idletasks()
            threading.Thread(target=self._install_worker, args=(link, state),
                             daemon=True).start()

        IconButton(btns, "  Обновить  ", go, bg=C["accent"], fg="#ffffff",
                   font=self.f_ui, pad=(10, 6)).pack(side="right")
        IconButton(btns, "  Позже  ", win.destroy, bg=C["bg"], fg=C["muted"],
                   font=self.f_ui, pad=(10, 6)).pack(side="right", padx=(0, 8))

    def _install_worker(self, link, state):
        bundle = app_bundle_path()
        try:
            install_update(link, bundle)
            err = None
        except Exception as exc:
            err = str(exc)
        self.call_soon(lambda: self._install_done(err, bundle, state))

    def _install_done(self, err, bundle, state):
        if err is not None:
            try:
                state.configure(text="Не вышло: " + err[:60], fg=C["danger"])
            except tk.TclError:
                pass
            return
        try:
            state.configure(text="Готово, перезапускаю…")
        except tk.TclError:
            pass
        self.save_state()
        try:
            subprocess.Popen(["open", "-n", bundle])
        except Exception:
            pass
        self.root.after(400, lambda: os._exit(0))

    # ---------- сохранение ----------
    def load_state(self):
        data = read_json(STATE_FILE)
        return data if isinstance(data, dict) else {}

    def save_state(self):
        self._save_job = None
        data = {
            "geometry": self.root.winfo_geometry(),
            "hero": self.hero_var.get(),
            "parent_dir": self.parent_dir,
            "search_url": self.search_url,
            "downloads_dir": self.downloads_dir,
            "list_text": self.txt.get("1.0", "end-1c"),
            "tab": self.tab,
            "theme": self.theme,
        }
        try:
            os.makedirs(STATE_DIR, exist_ok=True)
            write_json(STATE_FILE, data)
        except Exception:
            pass

    def schedule_save(self):
        if self._save_job is not None:
            self.root.after_cancel(self._save_job)
        self._save_job = self.root.after(500, self.save_state)

    def on_configure(self, event):
        if event.widget is self.root:
            self.schedule_save()

    def on_close(self):
        if self.busy():
            self.collector.stop_event.set()
        if self._save_job is not None:
            self.root.after_cancel(self._save_job)
        self.save_state()
        self.root.destroy()


def main():
    if run_override():
        return
    root = tk.Tk()
    App(root)
    root.mainloop()


if __name__ == "__main__":
    main()
