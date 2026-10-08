"""
Multi Roblox Manager (Windows)

- Keeps a list of your accounts.
- Each account gets its own isolated browser profile, so you sign in ONCE per
  account and stay signed in (like separate browsers).
- Enables Roblox multi-instance so several Roblox windows can run together.
- "Open Game View" shows a panel on the right side of this window with each
  account's browser AND running Roblox game. Click an account in the list to
  switch the panel to that account's window, and play without leaving the app.
  The button at the top hides/shows the accounts side so the game gets the whole window;
  the game keeps following the window while you drag or resize it.
- Anti-AFK (in Game View): each game has its own timer and presses Space on its own
  schedule, with a real key press: "When I'm away" (only while you've been idle) or
  "Immediately". so Roblox's 20-minute idle kick doesn't disconnect you.
- Auto-reconnect: per account, watches Roblox's own log for its "lost connection" message
  (rejoins within seconds) and, as a backup, Roblox's presence info, and relaunches the
  game if you drop out of it (needs the account's cookie and a Game ID). Every status
  change is written to error.log.
  It can also switch Anti-AFK back on for the rejoined game automatically.
- Recorder (top-bar button shows/hides it under the accounts): a TinyTask-style macro recorder.
  Records your mouse and keyboard, plays them back (repeat / forever / speed), and saves / loads
  recordings. F7 = record or stop, F8 = play or stop (while the panel is open). It records
  everything you type, so don't type passwords.
- The accounts are listed in two columns; click one to select it, double-click to launch it.
- Storage: "Free up space" (and an automatic clean-up at start-up) deletes the browser
  caches inside each account's profile while keeping the logins; browsers are also
  started with settings that stop those caches from growing back.
- Dark mode: tick "Dark mode" at the bottom of the accounts panel (remembered).
- Optionally saves each account's username/password, encrypted with Windows
  DPAPI (only your Windows user on this PC can decrypt them).

Roblox puts some accounts on test release channels, each with its own version, but its
launcher only keeps ONE "current" version per PC. Launching accounts from different channels
through the launcher therefore makes Roblox switch (update) every time. So by default the app
starts each account's player directly, using the installed version that matches THAT account's
channel (no launcher, no switching). Untick the setting to use Roblox's launcher instead; it is
then given the account's channel. The Launch
panel shows how the last launch was started. If the installed Roblox is older than the current
version the app updates it ONCE (it lets go of the multi-instance lock, because Roblox can't
finish updating while the lock is held, runs Roblox's updater, then launches the game). Each
target version is only ever tried once, so it can't ask or update again and again.

Game View toolbar: one row of window controls (Viewing, Browser/Game, Close Window, More, Fullscreen)
and the Anti-AFK strip. "Compact" hides everything except the Anti-AFK strip (and the window's top
bar); "Expand" brings it back. Rarely used options live in the "More" menu.
"Grid" (on the Anti-AFK strip) shows up to 12 games at once (2 side by side, 3-4 in 2x2,
5-6 in 3x2, 7-9 in 3x3, 10-12 in 4x3);
click a game to make it the one the account list and Anti-AFK controls refer to. "Single" goes
back to one game at a time. Browsers are always shown on their own.

Frozen games: a game in Game View that stays "Not Responding" for 30 s (a crash) is closed, and
auto-reconnect rejoins it (More menu: "Close games that stop responding" turns this off).

Leftover processes: when you close a Roblox game, Roblox sometimes leaves RobloxPlayerBeta.exe
running in Task Manager. The app notices a Roblox process whose window is gone and ends just
that process (never one that still has a window, including games in hidden Game View tabs).
It also ends the background "--launch-to-tray" process Roblox starts after a game closes.

Each account remembers its own Game ID / private-server link: the box shows the link for the
account selected in the list, and what you type is saved to THAT account only.

Direct launch (no browser): save an account's .ROBLOSECURITY cookie with
"Set Cookie" (stored encrypted with Windows DPAPI). "Launch Selected Account"
then asks Roblox for a one-time login ticket and starts the game client
directly for that account (joins the Game ID if you entered one, otherwise
just opens the Roblox app). The Game ID box also accepts a game link or a
private-server link, so you can join (and auto-rejoin) a private server. Accounts without a cookie can still use the browser.

Workflow:
  1. Click "Add Account", give it a name.
  2. Click "Log in" -> a browser window opens on the Roblox login page. Sign in
     normally (this app never sees or stores your password or cookies).
  3. Select the account and click "Launch" (optionally enter a Game ID first).
     The browser opens Roblox in that account's profile; press Play.
  4. Repeat for the next account. Each one opens its own Roblox window.

Tip: launch accounts one at a time and wait for each Roblox window to open
before starting the next.
"""

import base64
import calendar
import csv
import ctypes
import datetime
from ctypes import wintypes
import json
import math
import os
import queue
import random
import re
import shutil
import subprocess
import sys
import threading
import time
import traceback
import urllib.error
import urllib.parse
import urllib.request
import tkinter as tk
from tkinter import colorchooser, filedialog, messagebox, simpledialog, ttk

APP_DIR = os.path.join(os.environ.get("APPDATA", os.path.expanduser("~")), "MultiRoblox")
PROFILES_DIR = os.path.join(APP_DIR, "profiles")
DATA_FILE = os.path.join(APP_DIR, "accounts.json")
CRED_FILE = os.path.join(APP_DIR, "credentials.json")
SETTINGS_FILE = os.path.join(APP_DIR, "settings.json")

AFK_MODES = [("away", "When I'm away"), ("now", "Immediately")]
AWAY_IDLE = 20               # seconds without keyboard/mouse that count as "away"
AWAY_MAX_WAIT = 12 * 60      # give up waiting for you to be away after this (Roblox kicks at 20 min)

RECONNECT_CHECK_EVERY = 30   # seconds between presence checks per account
RECONNECT_GRACE = 150        # seconds after a launch before "not in game" counts
RECONNECT_MISSES = 3         # consecutive "not in game" checks before rejoining
RECONNECT_MAX_TRIES = 5      # rejoin attempts per 30 minutes before pausing
RECONNECT_LOST_WAIT = 8      # seconds after Roblox says "lost connection" before rejoining
GRID_MAX = 12                # games shown at once in Game View's grid
FROZEN_CLOSE_AFTER = 30      # seconds a game may stay "Not Responding" before it is closed
GRID_BORDER = 3              # pixels of coloured border around each game in the grid (drag it
GRID_BORDER_SELECTED = 6     # onto another game to swap them)... and around the one you're on
BORDER_PALETTE = ["#2f8cff", "#ff5c5c", "#3ccf6e", "#ffb020", "#b26bff", "#20c5d5",
                  "#ff7ac8", "#9ccc3c", "#ff8a3d", "#6c8cff", "#e0d040", "#40e0b0"]
GRID_GAP = 3                 # pixels between games in the grid

THEMES = {
    "light": dict(bg="SystemButtonFace", fg="SystemButtonText", field="SystemWindow",
                  ffg="SystemWindowText", btn="SystemButtonFace", btn_active="SystemButtonFace",
                  muted="#000000", sel_bg="SystemHighlight", sel_fg="SystemHighlightText",
                  border="#b5b5b5", relief="raised", bd=2, disabled="SystemGrayText",
                  check="SystemWindow"),
    "dark": dict(bg="#1e1e1e", fg="#e6e6e6", field="#2b2b2b", ffg="#e6e6e6", btn="#3a3a3a",
                 btn_active="#4a4a4a", muted="#ffffff", sel_bg="#0a64c8", sel_fg="#ffffff",
                 border="#555555", relief="flat", bd=1, disabled="#777777", check="#2b2b2b"),
}


def load_settings():
    try:
        with open(SETTINGS_FILE, "r", encoding="utf-8") as f:
            return json.load(f)
    except (OSError, ValueError):
        return {}


def save_settings(data):
    try:
        os.makedirs(APP_DIR, exist_ok=True)
        with open(SETTINGS_FILE, "w", encoding="utf-8") as f:
            json.dump(data, f, indent=2)
    except OSError:
        pass

MUTEX_NAME = "ROBLOX_singletonMutex"
ERROR_ALREADY_EXISTS = 183

BROWSER_CANDIDATES = [
    r"%ProgramFiles%\Google\Chrome\Application\chrome.exe",
    r"%ProgramFiles(x86)%\Google\Chrome\Application\chrome.exe",
    r"%LocalAppData%\Google\Chrome\Application\chrome.exe",
    r"%ProgramFiles(x86)%\Microsoft\Edge\Application\msedge.exe",
    r"%ProgramFiles%\Microsoft\Edge\Application\msedge.exe",
    r"%ProgramFiles%\BraveSoftware\Brave-Browser\Application\brave.exe",
]


def find_browser():
    for p in BROWSER_CANDIDATES:
        path = os.path.expandvars(p)
        if os.path.isfile(path):
            return path
    return None


class DATA_BLOB(ctypes.Structure):
    _fields_ = [("cbData", wintypes.DWORD), ("pbData", ctypes.POINTER(ctypes.c_char))]


def _make_blob(data):
    buf = ctypes.create_string_buffer(data, len(data))
    return DATA_BLOB(len(data), ctypes.cast(buf, ctypes.POINTER(ctypes.c_char))), buf


def _read_and_free(blob):
    data = ctypes.string_at(blob.pbData, blob.cbData)
    ctypes.windll.kernel32.LocalFree(ctypes.cast(blob.pbData, ctypes.c_void_p))
    return data


def encrypt_text(text):
    """Encrypt with Windows DPAPI (tied to your Windows user account)."""
    blob_in, _buf = _make_blob(text.encode("utf-8"))
    blob_out = DATA_BLOB()
    if not ctypes.windll.crypt32.CryptProtectData(
            ctypes.byref(blob_in), None, None, None, None, 0, ctypes.byref(blob_out)):
        raise ctypes.WinError()
    return base64.b64encode(_read_and_free(blob_out)).decode("ascii")


def decrypt_text(token):
    blob_in, _buf = _make_blob(base64.b64decode(token))
    blob_out = DATA_BLOB()
    if not ctypes.windll.crypt32.CryptUnprotectData(
            ctypes.byref(blob_in), None, None, None, None, 0, ctypes.byref(blob_out)):
        raise ctypes.WinError()
    return _read_and_free(blob_out).decode("utf-8")


def safe_name(name):
    return re.sub(r"[^A-Za-z0-9_-]", "_", name)


# ---------------------------------------------------------------------------
# Win32 helpers for embedding Roblox windows
# ---------------------------------------------------------------------------
GWL_STYLE = -16
WS_POPUP = 0x80000000
WS_CHILD = 0x40000000
WS_VISIBLE = 0x10000000
WS_CAPTION = 0x00C00000
WS_THICKFRAME = 0x00040000
WS_SYSMENU = 0x00080000
WS_MINIMIZEBOX = 0x00020000
WS_MAXIMIZEBOX = 0x00010000
SW_SHOW = 5
WM_CLOSE = 0x0010
GWLP_HWNDPARENT = -8
SW_HIDE = 0
SWP_NOZORDER = 0x0004
SWP_NOMOVE = 0x0002
SWP_NOSIZE = 0x0001
SWP_NOACTIVATE = 0x0010
SWP_SHOWWINDOW = 0x0040
VK_LBUTTON = 0x01
VK_RBUTTON = 0x02
GA_ROOT = 2
SW_RESTORE = 9
SWP_FLAGS_FRAMECHANGE = 0x0001 | 0x0002 | 0x0004 | 0x0010 | 0x0020  # nosize|nomove|nozorder|noactivate|framechanged
# Moving another program's window normally waits for that program to answer; a crashed/frozen
# game never answers, which would freeze this app too. ASYNC posts the move instead of waiting.
SWP_ASYNCWINDOWPOS = 0x4000

if sys.platform == "win32":
    user32 = ctypes.WinDLL("user32", use_last_error=True)
    kernel32 = ctypes.WinDLL("kernel32", use_last_error=True)
    WNDENUMPROC = ctypes.WINFUNCTYPE(wintypes.BOOL, wintypes.HWND, wintypes.LPARAM)
    HOOKPROC = ctypes.WINFUNCTYPE(ctypes.c_ssize_t, ctypes.c_int, wintypes.WPARAM, wintypes.LPARAM)

    user32.EnumWindows.argtypes = [WNDENUMPROC, wintypes.LPARAM]
    user32.EnumWindows.restype = wintypes.BOOL
    user32.IsWindow.argtypes = [wintypes.HWND]
    user32.IsWindowVisible.argtypes = [wintypes.HWND]
    user32.IsIconic.argtypes = [wintypes.HWND]
    user32.GetClassNameW.argtypes = [wintypes.HWND, wintypes.LPWSTR, ctypes.c_int]
    user32.GetWindowTextW.argtypes = [wintypes.HWND, wintypes.LPWSTR, ctypes.c_int]
    user32.GetWindowThreadProcessId.argtypes = [wintypes.HWND, ctypes.POINTER(wintypes.DWORD)]
    user32.GetWindowRect.argtypes = [wintypes.HWND, ctypes.POINTER(wintypes.RECT)]
    user32.SetParent.argtypes = [wintypes.HWND, wintypes.HWND]
    user32.SetParent.restype = wintypes.HWND
    user32.MoveWindow.argtypes = [wintypes.HWND, ctypes.c_int, ctypes.c_int,
                                  ctypes.c_int, ctypes.c_int, wintypes.BOOL]
    user32.ShowWindow.argtypes = [wintypes.HWND, ctypes.c_int]
    user32.ShowWindowAsync.argtypes = [wintypes.HWND, ctypes.c_int]
    user32.IsHungAppWindow.argtypes = [wintypes.HWND]
    user32.IsHungAppWindow.restype = wintypes.BOOL
    user32.SetWindowPos.argtypes = [wintypes.HWND, wintypes.HWND, ctypes.c_int, ctypes.c_int,
                                    ctypes.c_int, ctypes.c_int, wintypes.UINT]
    _get_long = getattr(user32, "GetWindowLongPtrW", None) or user32.GetWindowLongW
    _set_long = getattr(user32, "SetWindowLongPtrW", None) or user32.SetWindowLongW
    _get_long.argtypes = [wintypes.HWND, ctypes.c_int]
    _get_long.restype = ctypes.c_ssize_t
    _set_long.argtypes = [wintypes.HWND, ctypes.c_int, ctypes.c_ssize_t]
    _set_long.restype = ctypes.c_ssize_t
    kernel32.OpenProcess.argtypes = [wintypes.DWORD, wintypes.BOOL, wintypes.DWORD]
    kernel32.OpenProcess.restype = wintypes.HANDLE
    kernel32.QueryFullProcessImageNameW.argtypes = [wintypes.HANDLE, wintypes.DWORD,
                                                    wintypes.LPWSTR, ctypes.POINTER(wintypes.DWORD)]
    kernel32.CloseHandle.argtypes = [wintypes.HANDLE]
    kernel32.GetCurrentThreadId.restype = wintypes.DWORD
    user32.GetWindowThreadProcessId.restype = wintypes.DWORD
    user32.AttachThreadInput.argtypes = [wintypes.DWORD, wintypes.DWORD, wintypes.BOOL]
    user32.AttachThreadInput.restype = wintypes.BOOL
    user32.SetFocus.argtypes = [wintypes.HWND]
    user32.SetFocus.restype = wintypes.HWND
    user32.GetFocus.restype = wintypes.HWND
    user32.GetForegroundWindow.restype = wintypes.HWND
    user32.GetAncestor.argtypes = [wintypes.HWND, wintypes.UINT]
    user32.GetAncestor.restype = wintypes.HWND
    user32.IsChild.argtypes = [wintypes.HWND, wintypes.HWND]
    user32.IsZoomed.argtypes = [wintypes.HWND]
    user32.SetForegroundWindow.argtypes = [wintypes.HWND]
    user32.GetClientRect.argtypes = [wintypes.HWND, ctypes.POINTER(wintypes.RECT)]
    user32.ClientToScreen.argtypes = [wintypes.HWND, ctypes.POINTER(wintypes.POINT)]
    user32.MapVirtualKeyW.argtypes = [wintypes.UINT, wintypes.UINT]
    user32.MapVirtualKeyW.restype = wintypes.UINT
    user32.keybd_event.argtypes = [wintypes.BYTE, wintypes.BYTE, wintypes.DWORD, ctypes.c_size_t]
    user32.GetLastInputInfo.argtypes = [ctypes.POINTER(ctypes.c_uint * 2)]
    kernel32.GetTickCount.restype = wintypes.DWORD
    user32.PostMessageW.argtypes = [wintypes.HWND, wintypes.UINT, wintypes.WPARAM, wintypes.LPARAM]
    user32.PostMessageW.restype = wintypes.BOOL
    user32.GetCursorPos.argtypes = [ctypes.POINTER(wintypes.POINT)]
    user32.SetWindowsHookExW.argtypes = [ctypes.c_int, HOOKPROC, wintypes.HINSTANCE, wintypes.DWORD]
    user32.SetWindowsHookExW.restype = ctypes.c_void_p
    user32.CallNextHookEx.argtypes = [ctypes.c_void_p, ctypes.c_int, wintypes.WPARAM, wintypes.LPARAM]
    user32.CallNextHookEx.restype = ctypes.c_ssize_t
    user32.UnhookWindowsHookEx.argtypes = [ctypes.c_void_p]
    user32.GetMessageW.argtypes = [ctypes.POINTER(wintypes.MSG), wintypes.HWND, wintypes.UINT, wintypes.UINT]
    user32.PostThreadMessageW.argtypes = [wintypes.DWORD, wintypes.UINT, wintypes.WPARAM, wintypes.LPARAM]
    user32.GetSystemMetrics.argtypes = [ctypes.c_int]
    kernel32.GetModuleHandleW.argtypes = [wintypes.LPCWSTR]
    kernel32.GetModuleHandleW.restype = wintypes.HMODULE
    user32.GetAsyncKeyState.argtypes = [ctypes.c_int]
    user32.GetAsyncKeyState.restype = ctypes.c_short


def process_exe(hwnd):
    pid = wintypes.DWORD(0)
    user32.GetWindowThreadProcessId(hwnd, ctypes.byref(pid))
    handle = kernel32.OpenProcess(0x1000, False, pid.value)  # QUERY_LIMITED_INFORMATION
    if not handle:
        return ""
    try:
        buf = ctypes.create_unicode_buffer(520)
        size = wintypes.DWORD(520)
        if kernel32.QueryFullProcessImageNameW(handle, 0, buf, ctypes.byref(size)):
            return os.path.basename(buf.value).lower()
        return ""
    finally:
        kernel32.CloseHandle(handle)


def find_roblox_windows():
    """Return handles of visible top-level Roblox game windows."""
    found = []

    def callback(hwnd, _lparam):
        if user32.IsWindowVisible(hwnd):
            cls = ctypes.create_unicode_buffer(256)
            title = ctypes.create_unicode_buffer(256)
            user32.GetClassNameW(hwnd, cls, 256)
            user32.GetWindowTextW(hwnd, title, 256)
            if cls.value == "WINDOWSCLIENT" or title.value == "Roblox":
                exe = process_exe(hwnd)
                if exe in ("", "robloxplayerbeta.exe", "windows10universal.exe"):
                    found.append(hwnd)
        return True

    proc = WNDENUMPROC(callback)
    user32.EnumWindows(proc, 0)
    return found


def find_orphaned_games():
    """Hidden Roblox game windows that still have the borderless style Game View gives docked
    games: left behind by an earlier session that hid them (single view) and then closed without
    giving them back. Nothing else would ever show or end them."""
    found = []

    def callback(hwnd, _lparam):
        if not user32.IsWindowVisible(hwnd):
            cls = ctypes.create_unicode_buffer(64)
            user32.GetClassNameW(hwnd, cls, 64)
            if (cls.value == "WINDOWSCLIENT" and _get_long(hwnd, GWL_STYLE) & WS_POPUP
                    and process_exe(hwnd) == "robloxplayerbeta.exe"):
                found.append(hwnd)
        return True

    proc = WNDENUMPROC(callback)
    user32.EnumWindows(proc, 0)
    return found


def get_pid(hwnd):
    pid = wintypes.DWORD(0)
    user32.GetWindowThreadProcessId(hwnd, ctypes.byref(pid))
    return pid.value


def find_browser_windows(exe):
    """Visible top-level main windows of a Chromium browser (Chrome/Edge/Brave)."""
    found = []

    def callback(hwnd, _lparam):
        if user32.IsWindowVisible(hwnd):
            cls = ctypes.create_unicode_buffer(256)
            user32.GetClassNameW(hwnd, cls, 256)
            if cls.value == "Chrome_WidgetWin_1":
                style = _get_long(hwnd, GWL_STYLE)
                title = ctypes.create_unicode_buffer(256)
                user32.GetWindowTextW(hwnd, title, 256)
                rect = wintypes.RECT()
                user32.GetWindowRect(hwnd, ctypes.byref(rect))
                big = (rect.right - rect.left) >= 300 and (rect.bottom - rect.top) >= 200
                if (not (style & (WS_CHILD | WS_POPUP)) and title.value and big
                        and process_exe(hwnd) == exe):
                    found.append(hwnd)
        return True

    proc = WNDENUMPROC(callback)
    user32.EnumWindows(proc, 0)
    return found


# ---------------------------------------------------------------------------
# Roblox login ticket + direct client launch
# ---------------------------------------------------------------------------
class RobloxError(Exception):
    pass


class AuthExpired(RobloxError):
    """The account's cookie is no longer valid."""


def clean_cookie(raw):
    c = raw.strip().strip('"').strip("'").strip(";")
    if c.upper().startswith(".ROBLOSECURITY="):
        c = c.split("=", 1)[1]
    return c.strip()


def _open(req):
    try:
        return urllib.request.urlopen(req, timeout=15)
    except urllib.error.HTTPError as e:      # HTTPError doubles as the response object
        return e
    except (urllib.error.URLError, OSError) as e:
        raise RobloxError(f"Network error: {e}")


def whoami(cookie):
    """Return {"id": ..., "name": ...} for the account this cookie belongs to."""
    req = urllib.request.Request(
        "https://users.roblox.com/v1/users/authenticated",
        headers={"Cookie": f".ROBLOSECURITY={cookie}", "User-Agent": "Mozilla/5.0"})
    resp = _open(req)
    if resp.code == 200:
        return json.loads(resp.read().decode("utf-8"))
    if resp.code == 401:
        raise AuthExpired("That cookie isn't valid (expired, logged out, or copied wrong).")
    raise RobloxError(f"Roblox returned HTTP {resp.code} while checking the cookie.")


def check_cookie(cookie):
    """Return the Roblox username this cookie belongs to (raises RobloxError if invalid)."""
    return whoami(cookie).get("name", "?")


def roblox_post_json(url, cookie, payload):
    """POST JSON as this account (handles Roblox's CSRF handshake) and return the JSON reply."""
    body = json.dumps(payload).encode("utf-8")
    base = {"Cookie": f".ROBLOSECURITY={cookie}", "Content-Type": "application/json",
            "User-Agent": "Mozilla/5.0"}
    csrf = ""
    for _ in range(3):
        headers = dict(base)
        if csrf:
            headers["X-CSRF-TOKEN"] = csrf
        resp = _open(urllib.request.Request(url, data=body, headers=headers, method="POST"))
        if resp.code == 200:
            return json.loads(resp.read().decode("utf-8"))
        if resp.code == 403 and resp.headers.get("x-csrf-token") and not csrf:
            csrf = resp.headers["x-csrf-token"]
            continue
        if resp.code == 401:
            raise AuthExpired("This account's cookie has expired.")
        raise RobloxError(f"Roblox returned HTTP {resp.code}.")
    raise RobloxError("Roblox rejected the request.")


def get_presence(cookie, user_id):
    """Return (presence_type, place_id). Types: 0 offline, 1 online, 2 in game, 3 in Studio."""
    data = roblox_post_json("https://presence.roblox.com/v1/presence/users", cookie,
                            {"userIds": [user_id]})
    entry = (data.get("userPresences") or [{}])[0]
    return entry.get("userPresenceType", 0), (entry.get("rootPlaceId") or entry.get("placeId"))


def parse_target(text):
    """What the Game ID box holds. Returns None (no game), or (kind, place_id, code) where kind is
    'public', 'private' (old-style link with privateServerLinkCode) or 'share' (roblox.com/share)."""
    t = text.strip()
    if not t:
        return None
    if t.isdigit():
        return ("public", t, None)
    if "://" not in t:
        t = "https://" + t
    u = urllib.parse.urlparse(t)
    if "roblox.com" not in (u.netloc or ""):
        raise RobloxError("Enter a game ID, or paste a roblox.com game / private-server link.")
    query = urllib.parse.parse_qs(u.query)
    m = re.search(r"/games/(\d+)", u.path)
    if m and query.get("privateServerLinkCode"):
        return ("private", m.group(1), query["privateServerLinkCode"][0])
    if u.path.rstrip("/").endswith("/share") and query.get("code"):
        return ("share", None, query["code"][0])
    if m:
        return ("public", m.group(1), None)
    raise RobloxError("Couldn't understand that link. Paste a game ID or a private-server link.")


def resolve_share_link(cookie, code):
    """roblox.com/share?code=...&type=Server  ->  (place_id, private-server link code)."""
    data = roblox_post_json("https://apis.roblox.com/sharelinks/v1/resolve-link", cookie,
                            {"linkId": code, "linkType": "Server"})
    info = data.get("privateServerInviteData") or {}
    if not info.get("placeId") or not info.get("linkCode") or info.get("status") not in (None, "Valid"):
        raise RobloxError("That private-server invite link isn't valid any more.")
    return str(info["placeId"]), info["linkCode"]


def get_private_access_code(cookie, place_id, link_code):
    """Open the private-server link as this account and read the access code Roblox issues."""
    url = (f"https://www.roblox.com/games/{place_id}"
           f"?privateServerLinkCode={urllib.parse.quote(link_code)}")
    resp = _open(urllib.request.Request(
        url, headers={"Cookie": f".ROBLOSECURITY={cookie}", "User-Agent": "Mozilla/5.0"}))
    if resp.code == 401:
        raise AuthExpired("This account's cookie has expired. Use 'Set Cookie' to update it.")
    if resp.code != 200:
        raise RobloxError(f"Roblox returned HTTP {resp.code} for the private-server link.")
    html = resp.read().decode("utf-8", "replace")
    m = (re.search(r"joinPrivateGame\(\s*\d+\s*,\s*'([0-9a-fA-F-]{36})'", html)
         or re.search(r"accessCode[\"']?\s*[:=]\s*[\"']([0-9a-fA-F-]{36})", html))
    if not m:
        raise RobloxError("Couldn't join that private server. The link may have been reset, or "
                          "this account doesn't have access to it.")
    return m.group(1)


def _roblox_version_roots():
    roots = []
    for var in ("LOCALAPPDATA", "ProgramFiles(x86)", "ProgramFiles"):
        base = os.environ.get(var)
        if base:
            roots.append(os.path.join(base, "Roblox", "Versions"))
    local = os.environ.get("LOCALAPPDATA")
    if local:                                  # custom launchers keep their own copy of Roblox
        for launcher in ("Bloxstrap", "Fishstrap", "Voidstrap"):
            roots.append(os.path.join(local, launcher, "Versions"))
    return roots


def installed_players():
    """Every installed player: list of (modified time, path to RobloxPlayerBeta.exe, 'version-xxxx')."""
    found = []
    for root in _roblox_version_roots():
        if not os.path.isdir(root):
            continue
        for name in os.listdir(root):
            exe = os.path.join(root, name, "RobloxPlayerBeta.exe")
            if name.startswith("version-") and os.path.isfile(exe):
                found.append((os.path.getmtime(exe), exe, name))
    return found


def find_roblox_player(prefer=None):
    """The player to start: the exact version Roblox wants if it's installed, else the newest.
    Returns (path to RobloxPlayerBeta.exe, 'version-xxxx') or None."""
    players = installed_players()
    if prefer:
        for _modified, exe, name in players:
            if name == prefer:
                return exe, name
    if not players:
        return None
    best = max(players)
    return best[1], best[2]


def roblox_version_installed(version):
    return any(name == version for _m, _e, name in installed_players())


def get_user_channel(cookie):
    """The Roblox release channel this account is assigned to ('' = the normal/default one)."""
    try:
        resp = _open(urllib.request.Request(
            "https://clientsettings.roblox.com/v2/user-channel?binaryType=WindowsPlayer",
            headers={"Cookie": f".ROBLOSECURITY={cookie}", "User-Agent": "Mozilla/5.0"}))
        if resp.code == 200:
            name = (json.loads(resp.read().decode("utf-8")).get("channelName") or "").strip()
            if name.lower() not in ("", "live", "production"):
                return name
    except (RobloxError, ValueError):
        pass
    return ""


def latest_roblox_version(channel=""):
    """The version Roblox requires on this channel (e.g. 'version-abc123'), or None if unknown."""
    url = "https://clientsettings.roblox.com/v2/client-version/WindowsPlayer"
    if channel:
        url += "/channel/" + urllib.parse.quote(channel)
    try:
        resp = _open(urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"}))
        if resp.code == 200:
            return json.loads(resp.read().decode("utf-8")).get("clientVersionUpload")
    except (RobloxError, ValueError):
        pass
    return None


def build_update_url(channel=""):
    """Open the Roblox app through Roblox's launcher, which updates Roblox first if needed."""
    return ("roblox-player:1+launchmode:app"
            f"+launchtime:{int(time.time() * 1000)}"
            f"+robloxLocale:en_us+gameLocale:en_us+channel:{channel}+LaunchExp:InApp")


def roblox_running():
    try:
        out = subprocess.run(["tasklist", "/FI", "IMAGENAME eq RobloxPlayerBeta.exe", "/NH"],
                             capture_output=True, text=True, creationflags=0x08000000).stdout
        return "RobloxPlayerBeta.exe" in out
    except OSError:
        return False


def roblox_installer_running():
    """True while Roblox's installer/launcher is still working (it must finish its update)."""
    try:
        out = subprocess.run(["tasklist", "/NH"], capture_output=True, text=True,
                             creationflags=0x08000000).stdout
        return "RobloxPlayerInstaller.exe" in out or "RobloxPlayerLauncher.exe" in out
    except OSError:
        return False


def close_roblox_windows():
    """Ask every Roblox window to close normally (like clicking its X)."""
    for hwnd in find_roblox_windows():
        user32.PostMessageW(hwnd, WM_CLOSE, 0, 0)


def roblox_player_pids():
    """PIDs of all running RobloxPlayerBeta.exe processes."""
    try:
        out = subprocess.run(["tasklist", "/FI", "IMAGENAME eq RobloxPlayerBeta.exe", "/FO", "CSV", "/NH"],
                             capture_output=True, text=True, creationflags=0x08000000).stdout
    except OSError:
        return set()
    pids = set()
    for row in csv.reader(out.splitlines()):
        if len(row) >= 2 and row[0].lower() == "robloxplayerbeta.exe":
            try:
                pids.add(int(row[1]))
            except ValueError:
                pass
    return pids


def roblox_window_pids():
    """PIDs that still own a Roblox game window, visible or hidden (a game in a Game View tab you
    aren't looking at is hidden but very much alive)."""
    owners = set()

    def callback(hwnd, _lparam):
        cls = ctypes.create_unicode_buffer(256)
        title = ctypes.create_unicode_buffer(256)
        user32.GetClassNameW(hwnd, cls, 256)
        user32.GetWindowTextW(hwnd, title, 256)
        if cls.value == "WINDOWSCLIENT" or title.value == "Roblox":
            owners.add(get_pid(hwnd))
        return True

    proc = WNDENUMPROC(callback)
    user32.EnumWindows(proc, 0)
    return owners


def roblox_command_lines():
    """{pid: command line} for running RobloxPlayerBeta.exe processes (PowerShell, so used sparingly)."""
    try:
        out = subprocess.run(
            ["powershell", "-NoProfile", "-Command",
             "Get-CimInstance Win32_Process | Where-Object { $_.Name -eq 'RobloxPlayerBeta.exe' } | "
             "ForEach-Object { '{0}|{1}' -f $_.ProcessId, $_.CommandLine }"],
            capture_output=True, text=True, timeout=25, creationflags=0x08000000).stdout
    except (OSError, subprocess.SubprocessError):
        return {}
    lines = {}
    for line in out.splitlines():
        pid, _, command = line.partition("|")
        if pid.strip().isdigit():
            lines[int(pid.strip())] = command
    return lines


class RobloxLogWatcher:
    """Reads Roblox's own player logs to spot a disconnect right away, instead of waiting for
    Roblox's website to stop saying "in game". Each log is matched to an account by the user ID
    Roblox writes when it joins a game (userid:...)."""

    JOIN = re.compile(r"\[FLog::GameJoinLoadTime\].*?\buserid:(\d+)")
    WHERE = re.compile(r"\bplaceid:(\d+).*?\buniverseid:(\d+), referral_page:([^,]*)")
    LOST = re.compile(r"Lost connection with reason\s*:\s*(.*)")
    HEAD = 2 * 1024 * 1024          # how much of a new log to read to find whose it is
    TAIL = 4 * 1024 * 1024          # then only the end of a big log matters (~25 min of logging)

    def __init__(self, log_dir=None):
        self.log_dir = log_dir or os.path.join(os.environ.get("LOCALAPPDATA", ""), "Roblox", "logs")
        self.owner = {}             # path -> user id ("" until a join line is seen)
        self.pos = {}               # path -> bytes read so far
        self.ctime = {}             # path -> when the log was created (newest log = current game)
        self.lost = {}              # path -> (epoch, reason) while that game is disconnected
        self.place = {}             # path -> (place id, universe id) of the last join
        self.private_universe = {}  # path -> universe of the private server it joined

    @staticmethod
    def line_time(line):
        try:
            return calendar.timegm(time.strptime(line[:19], "%Y-%m-%dT%H:%M:%S"))
        except ValueError:
            return time.time()

    def feed(self, path, text):
        for line in text.splitlines():
            m = self.JOIN.search(line)
            if m:
                self.owner[path] = self.owner[path] or m.group(1)
                self.lost.pop(path, None)               # (re)joined a server: connected again
                w = self.WHERE.search(line)
                if w:
                    self.place[path] = (w.group(1), w.group(2))
                    if w.group(3).strip() == "RequestPrivateGame":
                        self.private_universe[path] = w.group(2)
                continue
            m = self.LOST.search(line)
            if m:
                self.lost[path] = (self.line_time(line), m.group(1).strip()[:120])

    def read(self, path, size):
        start = self.pos[path]
        if size <= start:
            return
        with open(path, "rb") as f:
            if start == 0 and size > self.HEAD + self.TAIL:   # big log seen for the first time
                head = f.read(self.HEAD)
                self.feed(path, head.decode("utf-8", "ignore"))
                start = size - self.TAIL
            f.seek(start)
            data = f.read(size - start)
        cut = data.rfind(b"\n") + 1                   # leave a half-written last line for later
        self.pos[path] = start + cut
        self.feed(path, data[:cut].decode("utf-8", "ignore"))

    def scan(self, user_ids):
        """{user_id: (epoch, reason)} for watched accounts whose current game shows Roblox's
        "lost connection" message."""
        try:
            names = os.listdir(self.log_dir)
        except OSError:
            return {}
        now = time.time()
        present = set()
        for name in names:
            if "_Player_" not in name or not name.endswith("_last.log") or "CrashHandler" in name:
                continue
            path = os.path.join(self.log_dir, name)
            present.add(path)
            try:
                st = os.stat(path)
            except OSError:
                continue
            if path not in self.pos:
                if now - st.st_mtime > 600:            # nothing written lately: an old game
                    continue
                self.pos[path], self.owner[path], self.ctime[path] = 0, "", st.st_ctime
            try:
                self.read(path, st.st_size)
            except OSError:
                pass
        for path in [p for p in self.pos if p not in present]:      # deleted by a clean-up
            for d in (self.pos, self.owner, self.ctime, self.lost, self.place, self.private_universe):
                d.pop(path, None)
        newest = self.newest(user_ids)
        return {uid: self.lost[p] for uid, p in newest.items() if p in self.lost}

    def newest(self, user_ids):
        """user id -> path of that account's most recent log."""
        newest = {}
        for path, uid in self.owner.items():
            if uid in user_ids and (uid not in newest or self.ctime[path] > self.ctime[newest[uid]]):
                newest[uid] = path
        return newest

    def where(self, user_ids):
        """user id -> {"place": id, "private": bool}: the game each account is in (call after
        scan). private = still inside the private server it joined (same game universe)."""
        out = {}
        for uid, path in self.newest(user_ids).items():
            if path in self.place:
                place, universe = self.place[path]
                out[uid] = {"place": place, "private": self.private_universe.get(path) == universe}
        return out


def process_running(image):
    try:
        out = subprocess.run(["tasklist", "/FI", f"IMAGENAME eq {image}", "/NH"],
                             capture_output=True, text=True, creationflags=0x08000000).stdout
        return image.lower() in out.lower()
    except OSError:
        return False


def kill_pid(pid):
    try:
        subprocess.run(["taskkill", "/PID", str(pid), "/F"], capture_output=True, creationflags=0x08000000)
    except OSError:
        pass


class ProcessReaper:
    """Decides which Roblox processes to end: ones that HAD a game window and no longer do.
    A process that is still starting (never had a window) or still has a window is left alone."""
    GRACE = 6.0        # seconds a process may take to exit by itself after its window closes
    RETRY = 10.0       # seconds between attempts if it refuses to die
    MAX_TRIES = 3

    def __init__(self):
        self.state = {}

    def step(self, running, with_window, now, tray=frozenset()):
        """tray = PIDs of Roblox's background '--launch-to-tray' processes. They never have a game
        window, but they are exactly the leftovers to end, so they follow the same countdown."""
        for pid in [p for p in self.state if p not in running]:
            del self.state[pid]                              # it exited by itself
        kills = []
        for pid in running:
            st = self.state.setdefault(pid, {"seen": False, "gone": None, "tries": 0, "last": 0.0})
            if pid in with_window:
                st["seen"], st["gone"] = True, None
                continue
            if pid in tray:
                st["seen"] = True
            if st["seen"]:
                if st["gone"] is None:
                    st["gone"] = now
                elif (now - st["gone"] >= self.GRACE and st["tries"] < self.MAX_TRIES
                        and now - st["last"] >= self.RETRY):
                    st["tries"] += 1
                    st["last"] = now
                    kills.append(pid)
        return kills


def kill_roblox():
    try:
        subprocess.run(["taskkill", "/IM", "RobloxPlayerBeta.exe", "/F"],
                       capture_output=True, creationflags=0x08000000)
    except OSError:
        pass


def prepare_launch(cookie, text, direct=True, skip_update=(), prefer_version=None):
    """Turn the Game ID box text into how to start Roblox for this account. Returns a dict:
    {"mode": "exe", "args": [...]} (start the player directly), {"mode": "url", "url": ...}
    (hand it to Roblox's launcher) or {"mode": "update", ...} (installed Roblox is out of date).
    skip_update holds 'installed|latest' pairs the user chose not to update."""
    target = parse_target(text)
    place, link, access = "", None, None
    if target:
        kind, place, code = target
        if kind == "share":
            place, code = resolve_share_link(cookie, code)
            kind = "private"
        if kind == "private":
            link = code
            access = get_private_access_code(cookie, place, code)

    channel = get_user_channel(cookie)                # which release channel this account is on
    latest = latest_roblox_version(channel)           # checked BEFORE the ticket: tickets expire fast
    found = find_roblox_player(prefer=latest or prefer_version)   # this account's own version
    chan = f" [channel: {channel or 'default'}]"
    stale = ""
    if found and latest and latest != found[1]:
        pair = f"{found[1]}|{latest}"
        if pair not in skip_update and f"latest:{latest}" not in skip_update:
            # out of date: nothing launched yet, no ticket spent
            return {"mode": "update", "installed": found[1], "latest": latest, "pair": pair,
                    "channel": channel, "how": f"Roblox needs updating ({found[1]} -> {latest}){chan}"}
        stale = f" (Roblox reports {latest}, update skipped)"

    player = None
    if not place:
        how = "opened the Roblox app through Roblox's launcher (no game ID given)"
    elif not direct:
        how = "used Roblox's launcher" + (f" (installed: {found[1]})" if found else "") + chan + stale
    elif not found:
        how = "used Roblox's launcher (couldn't find an installed player to start directly)"
    else:
        player = found[0]
        how = f"started the player directly ({found[1]})" + chan + stale

    ticket = get_auth_ticket(cookie, place)      # one-time ticket: fetch it last so it's fresh
    tracker = random.randint(10 ** 10, 10 ** 11 - 1)
    url = build_launch_url(ticket, place, link, access, tracker, channel)
    if player:
        # Exactly how Roblox's own launcher starts the player (seen in a real launch): the whole
        # roblox-player: link as the first argument, then these flags.
        args = [player, url, "-app", "-installerLaunchTimeEpochMs", "0",
                "-clientLaunchTimeEpochMs", str(int(time.time() * 1000)),
                "-isInstallerLaunch", str(os.getpid())]
        return {"mode": "exe", "args": args, "url": url, "note": "", "how": how, "version": found[1]}
    return {"mode": "url", "url": url, "note": "", "how": how, "version": found[1] if found else ""}


def get_auth_ticket(cookie, place_id):
    """Ask Roblox for a one-time ticket that lets the game client log in as this account."""
    url = "https://auth.roblox.com/v1/authentication-ticket"
    base = {
        "Cookie": f".ROBLOSECURITY={cookie}",
        "Content-Type": "application/json",
        "Referer": f"https://www.roblox.com/games/{place_id}" if place_id else "https://www.roblox.com/home",
        "Origin": "https://www.roblox.com",
        "User-Agent": "Mozilla/5.0",
    }
    csrf = ""
    for _ in range(3):
        headers = dict(base)
        if csrf:
            headers["X-CSRF-TOKEN"] = csrf
        resp = _open(urllib.request.Request(url, data=b"", headers=headers, method="POST"))
        if resp.code == 200:
            ticket = resp.headers.get("rbx-authentication-ticket")
            if ticket:
                return ticket
            raise RobloxError("Roblox didn't return a login ticket.")
        if resp.code == 403 and resp.headers.get("x-csrf-token") and not csrf:
            csrf = resp.headers["x-csrf-token"]   # Roblox hands out the CSRF token on the first try
            continue
        if resp.code == 401:
            raise AuthExpired("This account's cookie has expired. Use 'Set Cookie' to update it.")
        raise RobloxError(f"Roblox returned HTTP {resp.code}.")
    raise RobloxError("Roblox rejected the login request.")


def placelauncher_url(place_id, link_code, access_code, tracker):
    if access_code:   # private server
        return ("https://assetgame.roblox.com/game/PlaceLauncher.ashx?request=RequestPrivateGame"
                f"&browserTrackerId={tracker}&placeId={place_id}"
                f"&accessCode={access_code}&linkCode={link_code}")
    return ("https://assetgame.roblox.com/game/PlaceLauncher.ashx?request=RequestGame"
            f"&browserTrackerId={tracker}&placeId={place_id}&isPlayTogetherGame=false")


def build_launch_url(ticket, place_id, link_code=None, access_code=None, tracker=None, channel=""):
    tracker = tracker or random.randint(10 ** 10, 10 ** 11 - 1)
    if not place_id:   # no game chosen: just open the Roblox app, logged in as this account
        return ("roblox-player:1+launchmode:app"
                f"+gameinfo:{ticket}"
                f"+launchtime:{int(time.time() * 1000)}"
                f"+robloxLocale:en_us+gameLocale:en_us+channel:{channel}+LaunchExp:InApp")
    launcher = placelauncher_url(place_id, link_code, access_code, tracker)
    return ("roblox-player:1+launchmode:play"
            f"+gameinfo:{ticket}"
            f"+launchtime:{int(time.time() * 1000)}"
            f"+placelauncherurl:{urllib.parse.quote(launcher, safe='')}"
            f"+browsertrackerid:{tracker}"
            f"+robloxLocale:en_us+gameLocale:en_us+channel:{channel}+LaunchExp:InApp")


class KEYBDINPUT(ctypes.Structure):
    _fields_ = [("wVk", wintypes.WORD), ("wScan", wintypes.WORD), ("dwFlags", wintypes.DWORD),
                ("time", wintypes.DWORD), ("dwExtraInfo", ctypes.c_size_t)]


class MOUSEINPUT(ctypes.Structure):
    _fields_ = [("dx", wintypes.LONG), ("dy", wintypes.LONG), ("mouseData", wintypes.DWORD),
                ("dwFlags", wintypes.DWORD), ("time", wintypes.DWORD),
                ("dwExtraInfo", ctypes.c_size_t)]


class _INPUT_UNION(ctypes.Union):
    _fields_ = [("ki", KEYBDINPUT), ("mi", MOUSEINPUT)]


class INPUT(ctypes.Structure):
    _fields_ = [("type", wintypes.DWORD), ("u", _INPUT_UNION)]


def send_key(vk, down):
    """Send one real keyboard event to whatever window is in the foreground."""
    ki = KEYBDINPUT(vk, user32.MapVirtualKeyW(vk, 0), 0 if down else 0x0002, 0, 0)
    inp = INPUT(1, _INPUT_UNION(ki=ki))
    user32.SendInput(1, ctypes.byref(inp), ctypes.sizeof(INPUT))


def force_foreground(hwnd):
    if user32.IsIconic(hwnd):
        user32.ShowWindow(hwnd, SW_RESTORE)
    user32.keybd_event(0x12, 0, 0, 0)        # tap Alt: lets Windows allow the focus switch
    user32.keybd_event(0x12, 0, 0x0002, 0)
    user32.SetForegroundWindow(hwnd)


def idle_seconds():
    """Seconds since the user last touched the keyboard or mouse."""
    info = (ctypes.c_uint * 2)(8, 0)   # LASTINPUTINFO {cbSize, dwTime}
    if not user32.GetLastInputInfo(ctypes.byref(info)):
        return 999.0
    return ((kernel32.GetTickCount() - info[1]) & 0xFFFFFFFF) / 1000.0


# Things inside a Chromium profile that are safe to delete (caches, downloaded components, crash
# reports, on-device AI models). Logins live in Default/Network/Cookies and are NOT touched.
PROFILE_JUNK = [
    "Default/Cache", "Default/Code Cache", "Default/GPUCache", "Default/DawnCache",
    "Default/GrShaderCache", "Default/Service Worker/CacheStorage",
    "Default/Service Worker/ScriptCache", "Default/blob_storage", "Default/Storage/ext",
    "GrShaderCache", "ShaderCache", "GraphiteDawnCache", "component_crx_cache",
    "extensions_crx_cache", "OptGuideOnDeviceModel", "optimization_guide_model_store",
    "OnDeviceHeadSuggestModel", "BrowserMetrics", "Crashpad", "Safe Browsing", "SafetyTips",
    "Subresource Filter", "MEIPreload", "WidevineCdm", "screen_ai", "Webstore Downloads",
    "CertificateRevocation", "OriginTrials", "TrustTokenKeyCommitments", "hyphen-data",
]


def folder_size(path):
    total = 0
    stack = [path]
    while stack:
        current = stack.pop()
        try:
            with os.scandir(current) as entries:
                for entry in entries:
                    try:
                        if entry.is_dir(follow_symlinks=False):
                            stack.append(entry.path)
                        else:
                            total += entry.stat(follow_symlinks=False).st_size
                    except OSError:
                        pass
        except OSError:
            pass
    return total


def human_size(n):
    for unit in ("B", "KB", "MB"):
        if n < 1024:
            return f"{n:.0f} {unit}" if unit == "B" else f"{n:.1f} {unit}"
        n /= 1024
    return f"{n:.2f} GB"


def profile_in_use(profile_dir):
    """True if a browser still has this profile open (it keeps 'lockfile' locked)."""
    lock = os.path.join(profile_dir, "lockfile")
    if not os.path.exists(lock):
        return False
    try:
        with open(lock, "ab"):
            return False
    except OSError:
        return True


def clean_profile(profile_dir):
    for rel in PROFILE_JUNK:
        path = os.path.join(profile_dir, *rel.split("/"))
        if os.path.isdir(path):
            shutil.rmtree(path, ignore_errors=True)


def trim_log(limit=256 * 1024, keep=64 * 1024):
    path = os.path.join(APP_DIR, "error.log")
    try:
        if os.path.getsize(path) > limit:
            with open(path, "rb") as f:
                f.seek(-keep, os.SEEK_END)
                tail = f.read()
            with open(path, "wb") as f:
                f.write(tail)
    except OSError:
        pass


def run_cleanup():
    """Delete regrowable junk from every profile that isn't open. Returns (before, after, skipped)."""
    before = folder_size(APP_DIR)
    skipped = 0
    if os.path.isdir(PROFILES_DIR):
        for entry in os.scandir(PROFILES_DIR):
            if entry.is_dir():
                if profile_in_use(entry.path):
                    skipped += 1
                    continue
                clean_profile(entry.path)
    trim_log()
    return before, folder_size(APP_DIR), skipped


def log_player_command_lines(how):
    """After a launch, watch the Roblox processes for ~80 s and note their command lines in
    error.log (login ticket and private-server codes hidden) so a launch that doesn't join can
    be diagnosed. Only changes are logged."""
    seen = None
    for _ in range(8):
        time.sleep(10)
        try:
            out = subprocess.run(
                ["powershell", "-NoProfile", "-Command",
                 "Get-CimInstance Win32_Process | Where-Object { $_.Name -like 'Roblox*' } | "
                 "ForEach-Object { \"$($_.Name) [$($_.ProcessId)] $($_.CommandLine)\" }"],
                capture_output=True, text=True, timeout=20, creationflags=0x08000000).stdout.strip()
        except (OSError, subprocess.SubprocessError):
            return
        out = re.sub(r"(-t\s+)\S+", r"\1<hidden>", out)
        out = re.sub(r"(gameinfo:)[^+\s\"]+", r"\1<hidden>", out)
        out = re.sub(r"(accessCode=)[^&\"\s]+", r"\1<hidden>", out)
        out = re.sub(r"(linkCode=)[^&\"\s]+", r"\1<hidden>", out)
        if out != seen:
            seen = out
            log_error(f"Launch ({how}). Roblox processes:\n{out or '(none running)'}")


def log_error(text):
    """Append a problem to %APPDATA%\\MultiRoblox\\error.log so it can be diagnosed later."""
    try:
        os.makedirs(APP_DIR, exist_ok=True)
        with open(os.path.join(APP_DIR, "error.log"), "a", encoding="utf-8") as f:
            f.write(time.strftime("%Y-%m-%d %H:%M:%S") + "\n" + text + "\n")
    except OSError:
        pass


def afk_safe(method):
    """If a step of the anti-AFK cycle crashes, log it and reset instead of getting stuck."""
    def wrapper(self, *args, **kwargs):
        try:
            return method(self, *args, **kwargs)
        except Exception:
            log_error(traceback.format_exc())
            self.afk_abort()
    wrapper.__name__ = method.__name__
    return wrapper


def account_border(settings, accounts, name):
    """(on, colour) of an account's border, also used for its name in the account list.
    Saved per account; by default on, with a colour from BORDER_PALETTE by list position."""
    cfg = settings.get("borders", {}).get(name, {})
    color = cfg.get("color")
    if not color:
        color = BORDER_PALETTE[accounts.index(name) % len(BORDER_PALETTE) if name in accounts else 0]
    return bool(cfg.get("on", True)), color


class FlowRow(tk.Frame):
    """A toolbar row that wraps onto more lines when the window is too narrow. Build it like a
    normal Frame (children packed side="left"/"right"), then call adopt(): the left items flow in
    order and the right items stay together at the right edge of the last line."""

    def __init__(self, parent, **kw):
        super().__init__(parent, **kw)
        self.lefts, self.rights = [], []
        self._pending = False
        self.bind("<Configure>", lambda _e: self.relayout_soon())

    @staticmethod
    def _pads(info):
        pad = info.get("padx", 0)
        if isinstance(pad, (tuple, list)):
            pad = [int(p) for p in pad]
        else:
            pad = [int(p) for p in str(pad).split()] or [0]
        return pad[0], pad[1] if len(pad) > 1 else pad[0]

    def adopt(self):
        for child in self.pack_slaves():
            info = child.pack_info()
            item = (child, *self._pads(info))
            (self.rights if info.get("side") == "right" else self.lefts).append(item)
            child.pack_forget()
            child.bind("<Configure>", lambda _e: self.relayout_soon(), add="+")
        self.rights.reverse()                    # pack puts the first "right" item rightmost
        self.relayout()

    def relayout_soon(self):
        if not self._pending:
            self._pending = True
            self.after_idle(self.relayout)

    def relayout(self):
        self._pending = False
        width = max(self.winfo_width(), 1)
        lines, line, x = [], [], 0
        for child, pl, pr in self.lefts:
            w = child.winfo_reqwidth() + pl + pr
            if line and x + w > width:
                lines.append(line)
                line, x = [], 0
            line.append((child, x + pl))
            x += w
        group = sum(c.winfo_reqwidth() + pl + pr for c, pl, pr in self.rights)
        if self.rights and line and x + group > width:
            lines.append(line)
            line, x = [], 0
        gx = max(x, width - group)
        for child, pl, pr in self.rights:
            line.append((child, gx + pl))
            gx += child.winfo_reqwidth() + pl + pr
        if line:
            lines.append(line)
        y = 0
        for items in lines:
            h = max(c.winfo_reqheight() for c, _x in items)
            for child, cx in items:
                child.place(x=cx, y=y + (h - child.winfo_reqheight()) // 2)
            y += h + 2
        height = max(y - 2, 1)
        if int(self.cget("height")) != height:
            self.configure(height=height)


class GameView(tk.Frame):
    """Panel on the right side of the main window that hosts each account's browser and
    Roblox game as tabs."""

    BORDER_ON_LABEL = "Coloured border on this game (grid)"
    BORDER_COLOR_LABEL = "Border colour for this game..."

    def __init__(self, app, parent=None):
        super().__init__(parent or app, highlightthickness=1, highlightbackground="#b5b5b5")
        self.app = app

        # hwnd -> {"frame", "style", "rect", "kind" ("browser"/"game"), "account", "tid"}
        self.embedded = {}
        self.released = set()   # windows the user detached; don't auto-grab again
        self.failed = set()     # windows that couldn't be embedded
        self.expected = []      # browser windows we are waiting for after a launch
        self.counter = 0
        self.alive = True
        self.ui_tid = kernel32.GetCurrentThreadId()
        self.follow = {"root": None, "items": []}     # items: [(hwnd, margins)] of games on screen

        self.compact = tk.BooleanVar(value=bool(app.settings.get("gameview_compact", False)))
        self.grid_on = tk.BooleanVar(value=bool(app.settings.get("gameview_grid", False)))

        # Row 1: what you do with the windows (hidden in compact mode)
        self.row_actions = FlowRow(self)
        self.row_actions.pack(fill="x", padx=8, pady=(6, 2))
        tk.Label(self.row_actions, text="Viewing:").pack(side="left")
        self.picker_hwnds = []
        self.picker = ttk.Combobox(self.row_actions, state="readonly", width=26)
        self.picker.pack(side="left", padx=(4, 6))
        self.picker.bind("<<ComboboxSelected>>", self.on_picker)
        self.kind_btn = tk.Button(self.row_actions, text="Browser \u21C4 Game", state="disabled",
                                  command=self.toggle_kind)
        self.kind_btn.pack(side="left")
        tk.Button(self.row_actions, text="Close Window", command=self.close_current).pack(
            side="left", padx=(12, 0))
        tk.Button(self.row_actions, text="Fullscreen", command=self.toggle_fullscreen).pack(side="right")
        self.options_btn = tk.Menubutton(self.row_actions, text="More \u25BE", relief="raised")
        self.options_btn.pack(side="right", padx=(0, 6))
        self.options_menu = tk.Menu(self.options_btn, tearoff=0)
        self.options_btn.config(menu=self.options_menu)
        self.auto = tk.BooleanVar(value=True)
        self.dock_mode = tk.BooleanVar(value=True)
        self.options_menu.add_checkbutton(label="Auto-embed new Roblox windows", variable=self.auto)
        self.options_menu.add_checkbutton(label="Dock mode (recommended)", variable=self.dock_mode)
        self.kill_hung = tk.BooleanVar(value=bool(app.settings.get("close_frozen_games", True)))
        self.hung_since = {}                 # hwnd -> when it was first seen not responding
        self.options_menu.add_checkbutton(
            label=f"Close games that stop responding (after {FROZEN_CLOSE_AFTER} s)",
            variable=self.kill_hung, command=self.save_kill_hung)
        self.options_menu.add_separator()
        self.border_on = tk.BooleanVar(value=True)
        self.options_menu.add_checkbutton(label=self.BORDER_ON_LABEL, variable=self.border_on,
                                          command=self.toggle_border)
        self.options_menu.add_command(label=self.BORDER_COLOR_LABEL, command=self.pick_border_color)
        self.options_menu.config(postcommand=self.refresh_border_menu)
        self.options_menu.add_separator()
        self.options_menu.add_command(label="Grab Roblox windows now", command=self.scan)
        self.popped = {}                     # hwnd -> account: games popped out into their own window
        self.options_menu.add_command(label="Pop out this game (move it anywhere)",
                                      command=self.pop_out_current)
        self.options_menu.add_command(label="Put popped-out games back", command=self.put_back)
        self.options_menu.add_command(label="Detach this window", command=self.detach_current)
        self.options_menu.add_command(label="Detach all windows", command=self.detach_all)
        self.options_menu.add_separator()
        self.options_menu.add_command(label="Close this panel", command=self.close)
        self.row_actions.adopt()

        self.afk_on = tk.BooleanVar(value=False)
        self.afk_minutes = tk.StringVar(value="10")
        self.afk_status = tk.StringVar(value="Anti-AFK: off")
        self.afk_pending = []
        self.afk_running = False
        self.afk_ctx = None
        self.afk_wait_start = 0.0
        self.afk_started = 0.0
        saved_mode = app.settings.get("afk_mode", "away")
        self.afk_mode = tk.StringVar(value=saved_mode if saved_mode in dict(AFK_MODES) else "away")

        # Row 2: the Anti-AFK strip (always visible, also in compact mode)
        self.row_afk = FlowRow(self)
        self.row_afk.pack(fill="x", padx=8, pady=(2, 2))
        self.afk_check = tk.Checkbutton(self.row_afk, text="Anti-AFK: jump every",
                                        variable=self.afk_on, command=self.afk_toggled)
        self.afk_check.pack(side="left")
        self.afk_spin = tk.Spinbox(self.row_afk, from_=1, to=15, width=3, textvariable=self.afk_minutes,
                                   command=self.afk_minutes_changed)
        self.afk_spin.pack(side="left")
        self.afk_spin.bind("<Return>", lambda _e: self.afk_minutes_changed())
        self.afk_spin.bind("<FocusOut>", lambda _e: self.afk_minutes_commit())
        tk.Label(self.row_afk, text="min").pack(side="left", padx=(2, 8))
        self.afk_now_btn = tk.Button(self.row_afk, text="Jump Now", command=self.afk_jump_current)
        self.afk_now_btn.pack(side="left")
        tk.Label(self.row_afk, textvariable=self.afk_status, fg="#555").pack(side="left", padx=10)
        self.compact_btn = tk.Button(self.row_afk, text="\u25B4 Compact", command=self.toggle_compact)
        self.compact_btn.pack(side="right")
        self.grid_btn = tk.Button(self.row_afk, command=self.toggle_grid)
        self.grid_btn.pack(side="right", padx=(0, 6))
        self.grid_btn.config(text="▣ Single" if self.grid_on.get() else "⊞ Grid")
        self.row_afk.adopt()

        # Row 3: Anti-AFK extras (hidden in compact mode)
        self.row_afk_more = FlowRow(self)
        self.row_afk_more.pack(fill="x", padx=8)
        tk.Label(self.row_afk_more, text="Method:").pack(side="left")
        self.afk_mode_box = ttk.Combobox(self.row_afk_more, state="readonly", width=20,
                                         values=[label for _key, label in AFK_MODES])
        self.afk_mode_box.set(dict(AFK_MODES)[self.afk_mode.get()])
        self.afk_mode_box.pack(side="left", padx=(4, 10))
        self.afk_mode_box.bind("<<ComboboxSelected>>", self.on_afk_mode)
        tk.Button(self.row_afk_more, text="Jump All", command=self.afk_jump_all).pack(side="left")
        self.row_afk_more.adopt()

        # Tab strip is hidden: you switch by clicking accounts in the main list
        # (or with the "Viewing" box above).
        style = ttk.Style(self)
        try:
            style.layout("Tabless.TNotebook.Tab", [])
            style.configure("Tabless.TNotebook", tabmargins=0, borderwidth=0)
        except tk.TclError:
            pass
        self.nb = ttk.Notebook(self, style="Tabless.TNotebook")
        self.nb.pack(fill="both", expand=True, padx=6, pady=(0, 6))
        self.nb.bind("<<NotebookTabChanged>>", self.on_tab_changed)
        # coloured frames drawn just behind each game in the grid (Canvases, so the theme pass
        # leaves their colour alone): hwnd -> Canvas
        self.border_canvases = {}
        self.empty = tk.Frame(self.nb)
        tk.Label(
            self.empty, fg="#666", font=("Segoe UI", 11), justify="center",
            text="Nothing to show for this account yet.\n\n"
                 "Select an account on the left and click 'Launch' (or 'Log in').\n"
                 "Its game appears here; click any account to switch to it.\n"
                 "(Don't press F11 inside Roblox; use the Fullscreen button here.)"
        ).pack(expand=True)
        self.nb.add(self.empty, text="")
        app.bind("<Activate>", self.on_activate, add="+")
        app.bind("<Configure>", lambda e: self.sync_docks() if e.widget is app else None, add="+")
        self.after(300, self.watch_input)
        self.after(100, self.dock_loop)
        threading.Thread(target=self.follow_loop, daemon=True).start()
        self.after(1000, self.afk_tick)
        self.load_afk_controls()
        self.refresh_picker()
        self.set_compact(self.compact.get(), save=False)

        self.after(1000, self.poll)

    # ----- housekeeping -----
    def update_layout(self):
        self.load_afk_controls()
        self.refresh_picker()

    def poll(self):
        if not self.alive:
            return
        try:
            self.prune_dead()
            if self.auto.get():
                self.scan()
            self.match_browsers()
            self.close_frozen_games()
        except Exception:
            log_error(traceback.format_exc())
        self.after(500 if self.expected else 1500, self.poll)

    def save_kill_hung(self):
        self.app.settings["close_frozen_games"] = bool(self.kill_hung.get())
        save_settings(self.app.settings)
        if not self.kill_hung.get():
            self.hung_since.clear()

    def close_frozen_games(self):
        """End a game that has stayed 'Not Responding' for FROZEN_CLOSE_AFTER seconds (a crash),
        then let auto-reconnect rejoin it."""
        now = time.time()
        games = {h: i for h, i in self.embedded.items() if i["kind"] == "game" and user32.IsWindow(h)}
        for h in [h for h in self.hung_since if h not in games]:
            del self.hung_since[h]
        if not self.kill_hung.get():
            return
        for hwnd, info in games.items():
            if not user32.IsHungAppWindow(hwnd):
                self.hung_since.pop(hwnd, None)
                continue
            since = self.hung_since.setdefault(hwnd, now)
            if now - since < FROZEN_CLOSE_AFTER:
                continue
            del self.hung_since[hwnd]
            pid = get_pid(hwnd)
            subprocess.Popen(["taskkill", "/PID", str(pid), "/T", "/F"],
                             creationflags=0x08000000)  # CREATE_NO_WINDOW
            name = info["account"]
            log_error(f"Closed frozen Roblox game (process {pid}, account {name or 'unknown'}): "
                      f"not responding for {int(now - since)} s.")
            if name:
                self.after(3000, lambda n=name: self.app.rejoin_after_crash(n))

    def prune_dead(self):
        removed = False
        for hwnd in list(self.embedded):
            if not user32.IsWindow(hwnd):
                info = self.embedded.pop(hwnd)
                self.release_input(info)
                self.nb.forget(info["frame"])
                info["frame"].destroy()
                removed = True
        self.released = {h for h in self.released if user32.IsWindow(h)}
        self.failed = {h for h in self.failed if user32.IsWindow(h)}
        if removed:
            self.show_for_selected_account()
        self.update_layout()

    def release_input(self, info):
        tid = info.get("tid")
        if tid:
            user32.AttachThreadInput(self.ui_tid, tid, False)

    # ----- finding windows -----
    def scan(self):
        """Grab Roblox game windows."""
        for hwnd in find_roblox_windows():
            if (hwnd in self.embedded or hwnd in self.released or hwnd in self.failed
                    or user32.IsHungAppWindow(hwnd)):
                continue
            self.counter += 1
            name = self.app.claim_account_name()
            label = f"{name} \u00b7 Game" if name else f"Roblox {self.counter}"
            self.embed(hwnd, label, "game", name)
            minutes = self.app.take_afk_resume(name) if name else None
            if minutes is None and name:
                minutes = self.app.saved_afk(name)    # Anti-AFK was on for this account last time
            info = self.embedded.get(hwnd)
            saved_minutes = self.app.settings.get("afk_minutes", {}).get(name) if name else None
            if info and saved_minutes:                # its own interval, even while AFK is off
                info["afk"]["minutes"] = saved_minutes
            if minutes and info:                      # AFK back on (rejoin / relaunch / reopen)
                info["afk"].update(on=True, minutes=minutes)
                self.afk_reschedule(info)
                self.refresh_tab_label(info)
                self.load_afk_controls()
        for hwnd in find_orphaned_games():          # hidden games an earlier session left behind
            if (hwnd in self.embedded or hwnd in self.released or hwnd in self.failed
                    or user32.IsHungAppWindow(hwnd)):
                continue
            log_error(f"Brought back a hidden Roblox game left by an earlier session (process {get_pid(hwnd)}).")
            self.embed(hwnd, "Recovered game", "game", None)

    def expect_browser(self, account, pid, snapshot, exe):
        self.expected.append({"account": account, "pid": pid, "snapshot": snapshot,
                              "exe": exe, "t0": time.time()})

    def select_browser(self, account):
        """If this account's browser is already embedded, show its tab."""
        for hwnd, info in self.embedded.items():
            if info["kind"] == "browser" and info["account"] == account and user32.IsWindow(hwnd):
                self.nb.select(info["frame"])
                return True
        return False

    def match_browsers(self):
        now = time.time()
        for exp in list(self.expected):
            if now - exp["t0"] > 45:
                self.expected.remove(exp)
                continue
            candidates = [h for h in find_browser_windows(exp["exe"])
                          if h not in self.embedded and h not in self.failed]
            pick = next((h for h in candidates if get_pid(h) == exp["pid"]), None)
            if pick is None and now - exp["t0"] > 6:
                # fallback: any brand-new browser window that appeared since launch
                pick = next((h for h in candidates if h not in exp["snapshot"]), None)
            if pick is not None:
                self.expected.remove(exp)
                self.embed(pick, f"{exp['account']} \u00b7 Browser", "browser", exp["account"])
                info = self.embedded.get(pick)
                if info and self.app.current_account() == exp["account"]:
                    self.nb.select(info["frame"])

    # ----- embedding -----
    def embed(self, hwnd, label, kind, account=None):
        self._embed_window(hwnd, label, kind, account)
        info = self.embedded.get(hwnd)
        if not info or not self.alive:
            return
        if account is None and self.current_hwnd() is None:
            self.nb.select(info["frame"])        # unknown window and nothing shown: show it
        else:
            self.show_for_selected_account()
        self.refresh_picker()

    def _embed_window(self, hwnd, label, kind, account=None):
        frame = tk.Frame(self.nb, bg="black")
        self.nb.add(frame, text=f"  {label}  ")
        self.embedded[hwnd] = {"frame": frame, "style": None, "rect": None, "label": label,
                               "kind": kind, "account": account, "tid": None, "mode": "embed",
                               "afk": {"on": False, "minutes": 10, "next": 0.0}}
        self.update_layout()
        self.update_idletasks()

        rect = wintypes.RECT()
        user32.GetWindowRect(hwnd, ctypes.byref(rect))
        style = _get_long(hwnd, GWL_STYLE)
        if user32.IsIconic(hwnd):
            user32.ShowWindow(hwnd, SW_RESTORE)

        if self.dock_mode.get():
            self.dock(hwnd, frame, style, rect)
            return

        ctypes.set_last_error(0)
        user32.SetParent(hwnd, frame.winfo_id())
        if ctypes.get_last_error() != 0:
            self.failed.add(hwnd)
            self.nb.forget(frame)
            frame.destroy()
            self.embedded.pop(hwnd, None)
            self.update_layout()
            messagebox.showwarning(
                "Couldn't embed window",
                "Windows refused to embed that window (it may be running as a "
                "different user or with higher privileges). Try running this app the "
                "same way you run the browser and Roblox.", parent=self)
            return

        new_style = ((style & ~(WS_CAPTION | WS_THICKFRAME | WS_SYSMENU | WS_MINIMIZEBOX
                                | WS_MAXIMIZEBOX | WS_POPUP)) | WS_CHILD | WS_VISIBLE)
        _set_long(hwnd, GWL_STYLE, new_style)
        user32.SetWindowPos(hwnd, None, 0, 0, 0, 0, SWP_FLAGS_FRAMECHANGE)

        # Share an input queue so keyboard typing / game controls reach the embedded window.
        tid = user32.GetWindowThreadProcessId(hwnd, None)
        if tid and tid != self.ui_tid:
            user32.AttachThreadInput(self.ui_tid, tid, True)

        self.embedded[hwnd].update(style=style, tid=tid,
                                   rect=(rect.left, rect.top, rect.right, rect.bottom))
        frame.bind("<Configure>", lambda _e, h=hwnd: self.fit(h))
        user32.ShowWindow(hwnd, SW_SHOW)
        self.fit(hwnd)
        self.after(200, self.focus_current)

    # ----- dock mode: real top-level window, kept exactly over the tab area -----
    def root_hwnd(self):
        return user32.GetAncestor(self.winfo_id(), GA_ROOT)

    def dock(self, hwnd, frame, style, rect):
        info = self.embedded[hwnd]
        info.update(style=style, mode="dock", rect=(rect.left, rect.top, rect.right, rect.bottom))
        if user32.IsZoomed(hwnd):
            user32.ShowWindow(hwnd, SW_RESTORE)
        # Borderless, and owned by Game View so it always stays on top of it (and follows
        # minimise/restore), while remaining a normal window that gets real input.
        docked = style & ~(WS_CAPTION | WS_THICKFRAME | WS_SYSMENU | WS_MINIMIZEBOX | WS_MAXIMIZEBOX)
        if info["kind"] == "game":
            # Windows enforces Roblox's minimum window size on normal windows, but not on popups:
            # this lets a game shrink into a small grid cell or a small app window.
            docked |= WS_POPUP
        _set_long(hwnd, GWL_STYLE, docked)
        _set_long(hwnd, GWLP_HWNDPARENT, self.root_hwnd())
        user32.SetWindowPos(hwnd, None, 0, 0, 0, 0, SWP_FLAGS_FRAMECHANGE)
        frame.bind("<Configure>", lambda _e: self.sync_docks())
        self.sync_docks()
        self.after(250, self.focus_current)

    def dock_loop(self):
        if not self.alive:
            return
        try:
            self.sync_docks()
        except Exception:
            pass
        self.after(60, self.dock_loop)

    def sync_docks(self):
        if not self.alive:
            return
        docks = [(h, i) for h, i in self.embedded.items() if i.get("mode") == "dock"]
        if not docks:
            self.follow["items"] = []
            self.update_borders({})
            return
        showing = self.app.state() in ("normal", "zoomed") and bool(self.winfo_viewable())
        current = self.current_hwnd()
        root = self.root_hwnd()
        places = {}                               # hwnd -> (x, y, w, h) on screen
        if showing:
            slots = self.grid_slots(current)
            if slots:
                places = dict(zip(slots, self.grid_cells(len(slots))))
            elif current in self.embedded and self.embedded[current].get("mode") == "dock":
                frame = self.embedded[current]["frame"]
                places[current] = (frame.winfo_rootx(), frame.winfo_rooty(),
                                   max(frame.winfo_width(), 1), max(frame.winfo_height(), 1))
        shown = []
        area = None                               # the whole rectangle the games share
        if places:
            rects = list(places.values())
            left, top = min(r[0] for r in rects), min(r[1] for r in rects)
            area = (left, top, max(r[0] + r[2] for r in rects) - left,
                    max(r[1] + r[3] for r in rects) - top)
        insets = {}                                # hwnd -> border width, for games with a border
        self.cell_rects = dict(places) if len(places) > 1 else {}   # for dragging a border onto a game
        if len(places) > 1:                        # grid: each game framed in its own colour
            for hwnd in list(places):
                on, color = self.border_for(self.embedded.get(hwnd))
                if not on:
                    continue
                b = GRID_BORDER_SELECTED if hwnd == current else GRID_BORDER
                x, y, w, h = places[hwnd]
                insets[hwnd] = (b, color, (x, y, w, h))
                places[hwnd] = (x + b, y + b, max(w - 2 * b, 1), max(h - 2 * b, 1))
        # tell the follow thread the new border sizes before moving anything, so it can't put a
        # game back to its old size in between
        self.follow["insets"] = {h: v[0] for h, v in insets.items()}
        self.update_borders(insets)
        for hwnd, info in docks:
            if not user32.IsWindow(hwnd):
                continue
            if user32.IsHungAppWindow(hwnd):           # crashed/frozen game: don't touch it, or
                if hwnd in places:                     # this app would freeze waiting on it
                    shown.append(hwnd)
                continue
            # Tk can recreate its outer window (e.g. when toggling fullscreen), which leaves
            # the game owned by a dead handle and hidden behind Game View (= black screen).
            if root and _get_long(hwnd, GWLP_HWNDPARENT) != root:
                _set_long(hwnd, GWLP_HWNDPARENT, root)
                user32.SetWindowPos(hwnd, None, 0, 0, 0, 0, SWP_NOMOVE | SWP_NOSIZE | SWP_NOACTIVATE
                                    | SWP_ASYNCWINDOWPOS)               # raise above owner
            if info["kind"] == "game":                 # keep it a popup (no minimum size) if Roblox
                style = _get_long(hwnd, GWL_STYLE)      # rewrote its own style
                if not style & WS_POPUP:
                    _set_long(hwnd, GWL_STYLE, (style | WS_POPUP) & ~(WS_CAPTION | WS_THICKFRAME))
                    user32.SetWindowPos(hwnd, None, 0, 0, 0, 0, SWP_FLAGS_FRAMECHANGE | SWP_ASYNCWINDOWPOS)
            if hwnd in places:
                x, y, w, h = places[hwnd]
                rect = wintypes.RECT()
                user32.GetWindowRect(hwnd, ctypes.byref(rect))
                actual = (rect.left, rect.top, rect.right - rect.left, rect.bottom - rect.top)
                if actual != (x, y, w, h) or not user32.IsWindowVisible(hwnd):
                    user32.SetWindowPos(hwnd, None, x, y, w, h, SWP_NOZORDER | SWP_NOACTIVATE
                                        | SWP_SHOWWINDOW | SWP_ASYNCWINDOWPOS)
                shown.append(hwnd)
            elif user32.IsWindowVisible(hwnd):
                user32.ShowWindowAsync(hwnd, SW_HIDE)
        if shown and root:
            self.update_follow(root, area, [h for h in places if h in shown],
                               {h: v[0] for h, v in insets.items()})
        else:
            self.follow["items"] = []

    # ----- grid: several games on screen at once -----
    def grid_slots(self, current):
        """Games shown together in grid view (up to GRID_MAX, always including the one you're
        on). Empty when the grid is off, there's only one game, or you're looking at a browser."""
        games = [h for h, i in self.embedded.items()
                 if i["kind"] == "game" and i.get("mode") == "dock" and user32.IsWindow(h)]
        # same order as the account list, so moving accounts there moves their games here
        order = {n: k for k, n in enumerate(getattr(self.app, "accounts", []))}
        games.sort(key=lambda h: order.get(self.embedded[h].get("account"), len(order)))
        cur = self.embedded.get(current)
        if not self.grid_on.get() or len(games) < 2 or (cur and cur["kind"] != "game"):
            return []
        slots = games[:GRID_MAX]
        if current in games and current not in slots:
            slots[-1] = current
        return slots

    @staticmethod
    def split_area(x, y, w, h, n):
        """Screen rectangles for n games in an area: 1 fills it, 2 side by side, 3-4 in 2x2,
        5-6 in 3x2, 7-9 in 3x3, 10-12 in 4x3 (filled row by row)."""
        cols = math.ceil(math.sqrt(n))
        rows = math.ceil(n / cols)
        cw = (w - GRID_GAP * (cols - 1)) // cols
        ch = (h - GRID_GAP * (rows - 1)) // rows
        return [(x + (k % cols) * (cw + GRID_GAP), y + (k // cols) * (ch + GRID_GAP), cw, ch)
                for k in range(n)]

    def grid_cells(self, n):
        return self.split_area(self.nb.winfo_rootx(), self.nb.winfo_rooty(),
                               max(self.nb.winfo_width(), 2), max(self.nb.winfo_height(), 2), n)

    # ----- coloured borders (grid view), on/off and colour per account -----
    def border_for(self, info):
        """(on, colour) for a game's border; saved per account, default on with its own colour."""
        return account_border(self.app.settings, list(getattr(self.app, "accounts", [])),
                              (info or {}).get("account") or "")

    def update_borders(self, insets):
        """Show a coloured Canvas behind each bordered game; hide/remove the rest."""
        edge = int(self.cget("highlightthickness")) + int(self.cget("bd"))   # place() starts inside it
        for hwnd, (_b, color, (x, y, w, h)) in insets.items():
            canvas = self.border_canvases.get(hwnd)
            if canvas is None:
                canvas = self.border_canvases[hwnd] = tk.Canvas(self, highlightthickness=0, bd=0,
                                                                cursor="fleur")
                canvas.bind("<ButtonPress-1>", lambda e, h=hwnd: self.border_press(h))
                canvas.bind("<B1-Motion>", self.border_motion)
                canvas.bind("<ButtonRelease-1>", self.border_release)
            drag = getattr(self, "border_drag", None)
            if drag and drag.get("target") == hwnd:
                color = "#ffffff"                 # where a dragged game would go
            if str(canvas.cget("bg")) != color:
                canvas.configure(bg=color)
            canvas.place(x=x - self.winfo_rootx() - edge, y=y - self.winfo_rooty() - edge,
                         width=w, height=h)
            canvas.tk.call("raise", canvas._w)    # Canvas.lift() would mean tag_raise
        for hwnd in list(self.border_canvases):
            if hwnd not in insets:
                if hwnd in self.embedded:
                    self.border_canvases[hwnd].place_forget()
                else:
                    self.border_canvases.pop(hwnd).destroy()

    # ----- drag a game's border onto another game to swap their places -----
    def game_at(self, x_root, y_root):
        for hwnd, (x, y, w, h) in getattr(self, "cell_rects", {}).items():
            if x <= x_root < x + w and y <= y_root < y + h:
                return hwnd
        return None

    def border_press(self, hwnd):
        self.border_drag = {"src": hwnd, "target": None}
        info = self.embedded.get(hwnd)
        if info:                                   # clicking a border also selects that game
            self.nb.select(info["frame"])
            if info["account"]:
                self.app.select_account(info["account"])
                self.app.refresh_reconnect_ui()

    def border_motion(self, event):
        drag = getattr(self, "border_drag", None)
        if not drag:
            return
        target = self.game_at(event.x_root, event.y_root)
        target = target if target != drag["src"] else None
        if target != drag["target"]:
            if drag["target"] in self.border_canvases:      # un-mark the previous target
                self.border_canvases[drag["target"]].configure(bg=self.border_for(self.embedded.get(drag["target"]))[1])
            drag["target"] = target
            if target in self.border_canvases:              # mark where it would go
                self.border_canvases[target].configure(bg="#ffffff")

    def border_release(self, _event):
        drag, self.border_drag = getattr(self, "border_drag", None), None
        if not drag or not drag["target"]:
            return
        a = (self.embedded.get(drag["src"]) or {}).get("account")
        b = (self.embedded.get(drag["target"]) or {}).get("account")
        if a and b:
            self.app.swap_accounts(a, b)            # the grid follows the account list order
        self.sync_docks()

    # ----- pop a game out into its own window, and put it back -----
    def pop_out(self, hwnd):
        info = self.embedded.get(hwnd)
        if not info or info["kind"] != "game":
            return
        self.popped[hwnd] = info["account"]
        self.detach(hwnd)                           # a normal window again: move it anywhere

    def pop_out_current(self):
        hwnd = self.current_hwnd()
        if hwnd:
            self.pop_out(hwnd)

    def popped_for(self, name):
        return [h for h, n in self.popped.items() if n == name and user32.IsWindow(h)]

    def put_back(self, only=None):
        """Bring popped-out games back into Game View (all, or just this account's)."""
        for hwnd, name in list(self.popped.items()):
            if only is not None and name != only:
                continue
            del self.popped[hwnd]
            if user32.IsWindow(hwnd) and not user32.IsHungAppWindow(hwnd):
                self.released.discard(hwnd)
                self.embed(hwnd, f"{name} · Game" if name else "Roblox", "game", name)

    def border_key(self):
        """The account (settings key) of the game you're on, or None if it isn't a game."""
        _hwnd, info = self.current_info()
        if not info or info["kind"] != "game":
            return None
        return info["account"] or ""

    def refresh_border_menu(self):
        key = self.border_key()
        state = "normal" if key is not None else "disabled"
        for label in (self.BORDER_ON_LABEL, self.BORDER_COLOR_LABEL):
            self.options_menu.entryconfig(self.options_menu.index(label), state=state)
        if key is not None:
            self.border_on.set(self.border_for(self.embedded[self.current_hwnd()])[0])

    def save_border(self, key, **changes):
        self.app.settings.setdefault("borders", {}).setdefault(key, {}).update(changes)
        save_settings(self.app.settings)
        self.sync_docks()
        self.app.listbox.paint()                 # account names use the same colours

    def toggle_border(self):
        key = self.border_key()
        if key is not None:
            self.save_border(key, on=bool(self.border_on.get()))

    def pick_border_color(self):
        key = self.border_key()
        if key is None:
            return
        _on, color = self.border_for(self.embedded[self.current_hwnd()])
        picked = colorchooser.askcolor(color=color, parent=self,
                                       title=f"Border colour for {key or 'this game'}")[1]
        if picked:
            self.save_border(key, color=picked, on=True)

    def toggle_grid(self):
        on = not self.grid_on.get()
        self.grid_on.set(on)
        self.grid_btn.config(text="▣ Single" if on else "⊞ Grid")
        self.app.settings["gameview_grid"] = on
        save_settings(self.app.settings)
        self.sync_docks()
        self.after(150, self.focus_current)

    def grid_follow_focus(self):
        """In grid view, clicking a game makes it the one you're on (account list, Anti-AFK)."""
        if self.afk_ctx is not None or not self.grid_on.get():
            return
        fg = user32.GetForegroundWindow()
        info = self.embedded.get(fg)
        if info and info["kind"] == "game" and fg != self.current_hwnd():
            self.nb.select(info["frame"])
            if info["account"]:
                self.app.select_account(info["account"])
                self.app.refresh_reconnect_ui()

    def update_follow(self, root, area, order, insets=None):
        """Record where the games' shared area sits relative to the window's client area
        (margins); `order` is the games in their grid order, `insets` their border widths."""
        self.follow["insets"] = insets or {}
        pt = wintypes.POINT(0, 0)
        rc = wintypes.RECT()
        user32.ClientToScreen(root, ctypes.byref(pt))
        user32.GetClientRect(root, ctypes.byref(rc))
        if rc.right < 50 or rc.bottom < 50:       # minimised
            return
        x, y, w, h = area
        self.follow.update(root=root, items=list(order), margins=(
            x - pt.x, y - pt.y, (pt.x + rc.right) - (x + w), (pt.y + rc.bottom) - (y + h)))

    def follow_once(self):
        root, items, m = self.follow["root"], self.follow["items"], self.follow.get("margins")
        if not root or not items or not m:
            return
        pt = wintypes.POINT(0, 0)
        rc = wintypes.RECT()
        user32.ClientToScreen(root, ctypes.byref(pt))
        user32.GetClientRect(root, ctypes.byref(rc))
        aw, ah = rc.right - m[0] - m[2], rc.bottom - m[1] - m[3]
        if aw < 50 or ah < 50:
            return
        for hwnd, (x, y, w, h) in zip(items, self.split_area(pt.x + m[0], pt.y + m[1], aw, ah,
                                                              len(items))):
            if not user32.IsWindow(hwnd) or user32.IsHungAppWindow(hwnd):
                continue
            b = self.follow.get("insets", {}).get(hwnd)
            if b:                                       # leave room for its coloured border
                x, y, w, h = x + b, y + b, max(w - 2 * b, 1), max(h - 2 * b, 1)
            cur = wintypes.RECT()
            user32.GetWindowRect(hwnd, ctypes.byref(cur))
            if ((cur.left, cur.top, cur.right - cur.left, cur.bottom - cur.top) != (x, y, w, h)
                    and user32.IsWindowVisible(hwnd)):
                user32.SetWindowPos(hwnd, None, x, y, w, h,
                                    SWP_NOZORDER | SWP_NOACTIVATE | SWP_ASYNCWINDOWPOS)

    def follow_loop(self):
        """Keeps the game glued to the window while you drag or resize it. Tk's own timers
        pause during Windows' move/resize loop, so this runs on a separate thread."""
        while self.alive:
            time.sleep(0.015)
            try:
                self.follow_once()
            except Exception:
                pass

    def fit(self, hwnd):
        info = self.embedded.get(hwnd)
        if info and user32.IsWindow(hwnd):
            frame = info["frame"]
            user32.MoveWindow(hwnd, 0, 0, max(frame.winfo_width(), 1),
                              max(frame.winfo_height(), 1), True)

    def current_hwnd(self):
        current = str(self.nb.select())
        for hwnd, info in self.embedded.items():
            if str(info["frame"]) == current and user32.IsWindow(hwnd):
                return hwnd
        return None

    def focus_current(self):
        if not self.alive:
            return
        hwnd = self.current_hwnd()
        if not hwnd:
            return
        if self.embedded[hwnd].get("mode") == "dock":
            self.sync_docks()
            user32.SetForegroundWindow(hwnd)   # so keys/mouse go straight to the game
        else:
            user32.SetFocus(hwnd)

    def on_activate(self, event):
        # Coming back to this window (e.g. Alt-Tab): hand keyboard focus to the game/browser.
        if self.alive and event.widget is self.app:
            self.after(100, self.focus_current)

    def watch_input(self):
        """Clicking inside an embedded window gives it keyboard focus (needed to play)."""
        if not self.alive:
            return
        try:
            self.grid_follow_focus()
            pressed = (user32.GetAsyncKeyState(VK_LBUTTON) & 0x8000) or \
                      (user32.GetAsyncKeyState(VK_RBUTTON) & 0x8000)
            hwnd = self.current_hwnd() if pressed else None
            if hwnd and self.embedded[hwnd].get("mode") == "embed" and user32.GetForegroundWindow() == user32.GetAncestor(self.winfo_id(), GA_ROOT):
                focus = user32.GetFocus()
                if not focus or (focus != hwnd and not user32.IsChild(hwnd, focus)):
                    pt = wintypes.POINT()
                    rect = wintypes.RECT()
                    user32.GetCursorPos(ctypes.byref(pt))
                    user32.GetWindowRect(hwnd, ctypes.byref(rect))
                    if rect.left <= pt.x < rect.right and rect.top <= pt.y < rect.bottom:
                        user32.SetFocus(hwnd)
        except Exception:
            pass
        self.after(80, self.watch_input)

    def toggle_compact(self):
        self.set_compact(not self.compact.get())

    def set_compact(self, on, save=True):
        """Compact: show only the Anti-AFK strip (the Hide accounts button stays)."""
        self.compact.set(on)
        if on:
            self.row_actions.pack_forget()
            self.row_afk_more.pack_forget()
            self.compact_btn.config(text="\u25BE Expand")
        else:
            self.row_actions.pack(fill="x", padx=8, pady=(6, 2), before=self.row_afk)
            self.row_afk_more.pack(fill="x", padx=8, after=self.row_afk)
            self.compact_btn.config(text="\u25B4 Compact")
        self.app.set_topbar_visible(not on)
        if save:
            self.app.settings["gameview_compact"] = bool(on)
            save_settings(self.app.settings)
        self.after(80, self.sync_docks)

    def toggle_fullscreen(self):
        # Let go of the games while Tk rebuilds its window, so they can't be closed or lost.
        for hwnd, info in self.embedded.items():
            if (info.get("mode") == "dock" and user32.IsWindow(hwnd)
                    and not user32.IsHungAppWindow(hwnd)):
                _set_long(hwnd, GWLP_HWNDPARENT, 0)
        self.app.attributes("-fullscreen", not bool(self.app.attributes("-fullscreen")))
        for delay in (100, 300, 700):
            self.after(delay, self.sync_docks)
        self.after(400, self.focus_current)

    # ----- anti-AFK (each game tab has its own timer) -----
    def current_info(self):
        hwnd = self.current_hwnd()
        return (hwnd, self.embedded[hwnd]) if hwnd else (None, None)

    def on_tab_changed(self, _event):
        self.load_afk_controls()
        self.refresh_picker()
        self.after(150, self.focus_current)

    def load_afk_controls(self):
        """Show the selected tab's AFK settings in the toolbar."""
        _hwnd, info = self.current_info()
        is_game = bool(info and info["kind"] == "game")
        state = "normal" if is_game else "disabled"
        for widget in (self.afk_check, self.afk_spin, self.afk_now_btn):
            widget.config(state=state)
        if is_game:
            self.afk_on.set(info["afk"]["on"])
            self.afk_minutes.set(str(info["afk"]["minutes"]))
        else:
            self.afk_on.set(False)

    def afk_reschedule(self, info):
        info["afk"]["next"] = time.time() + info["afk"]["minutes"] * 60

    def refresh_tab_label(self, info):
        afk = info["afk"]
        suffix = f"  (AFK {afk['minutes']}m)" if afk["on"] else ""
        try:
            self.nb.tab(info["frame"], text=f"  {info['label']}{suffix}  ")
        except tk.TclError:
            pass
        self.refresh_picker()

    def afk_toggled(self):
        _hwnd, info = self.current_info()
        if not info or info["kind"] != "game":
            return
        info["afk"]["on"] = bool(self.afk_on.get())
        self.afk_reschedule(info)
        self.refresh_tab_label(info)
        self.app.remember_afk(info)

    def afk_minutes_changed(self):
        _hwnd, info = self.current_info()
        if not info or info["kind"] != "game":
            return
        try:
            mins = max(1, min(15, int(self.afk_minutes.get())))
        except ValueError:
            return
        if mins == info["afk"]["minutes"]:
            return                      # unchanged (e.g. just clicked away): keep the countdown
        info["afk"]["minutes"] = mins
        self.afk_reschedule(info)
        self.refresh_tab_label(info)
        self.app.remember_afk(info)

    def afk_minutes_commit(self):
        self.afk_minutes_changed()
        self.load_afk_controls()   # normalise whatever was typed

    def afk_jump_current(self):
        hwnd, info = self.current_info()
        if info and info["kind"] == "game":
            self.afk_begin([(hwnd, info)], force=True)

    def afk_jump_all(self):
        self.afk_begin([(h, i) for h, i in self.embedded.items() if i["kind"] == "game"],
                       force=True)

    def afk_tick(self):
        if not self.alive:
            return
        try:
            now = time.time()
            if self.afk_running:
                targets = self.afk_ctx["targets"] if self.afk_ctx else self.afk_pending
                if now - self.afk_started > AWAY_MAX_WAIT + 300 + 20 * len(targets):
                    log_error("Anti-AFK cycle took too long; resetting it.")
                    self.afk_abort()
            if not self.afk_running and not self.app.recorder_playing():   # never fight a playback
                due = [(h, i) for h, i in self.embedded.items()
                       if i["kind"] == "game" and i["afk"]["on"] and now >= i["afk"]["next"]]
                if due:
                    self.afk_begin(due)
            if not self.afk_running:
                _hwnd, info = self.current_info()
                if not info:
                    self.afk_status.set("Anti-AFK: no window selected")
                elif info["kind"] != "game":
                    self.afk_status.set("Anti-AFK: game windows only")
                elif not info["afk"]["on"]:
                    self.afk_status.set("Anti-AFK: off for this account")
                else:
                    remaining = max(0, int(info["afk"]["next"] - now))
                    note = info["afk"].get("last")
                    self.afk_status.set(f"Next jump in {remaining // 60}:{remaining % 60:02d}"
                                        + (f"  \u00b7 last: {note}" if note else ""))
        except Exception:
            log_error(traceback.format_exc())
        self.after(1000, self.afk_tick)

    def afk_begin(self, targets, force=False):
        if self.afk_running:
            return
        targets = [(h, i) for h, i in targets if user32.IsWindow(h)]
        if not targets:
            self.afk_status.set("No Roblox game to jump")
            return
        self.afk_pending = targets
        self.afk_running = True
        self.afk_started = self.afk_wait_start = time.time()
        self.afk_wait_idle(force)

    @afk_safe
    def afk_wait_idle(self, force):
        """Don't grab the keyboard while you're actively using the PC (waits up to 3 min)."""
        if not self.alive:
            return
        if (not force and self.afk_mode.get() == "away" and self.app.real_idle() < AWAY_IDLE
                and time.time() - self.afk_wait_start < AWAY_MAX_WAIT):
            self.afk_status.set("Waiting until you're away from the PC...")
            self.after(2000, lambda: self.afk_wait_idle(force))
            return
        self.afk_start_cycle()

    @afk_safe
    def afk_start_cycle(self):
        targets = [(h, i) for h, i in self.afk_pending
                   if user32.IsWindow(h) and h in self.embedded]
        if not targets:
            self.afk_pending = []
            self.afk_status.set("No Roblox game to jump")
            self.afk_running = False
            return
        self.afk_pending = []
        iconic = self.app.state() == "iconic"
        if iconic:
            self.app.deiconify()
        self.afk_ctx = {"targets": targets, "i": 0, "iconic": iconic,
                        "prev_fg": user32.GetForegroundWindow(),
                        "prev_tab": str(self.nb.select()) if self.embedded else None}
        self.afk_status.set("Jumping...")
        self.after(300, self.afk_step)

    @afk_safe
    def afk_step(self):
        ctx = self.afk_ctx
        if not self.alive or ctx is None:
            return
        if ctx["i"] >= len(ctx["targets"]):
            self.afk_finish()
            return
        hwnd, info = ctx["targets"][ctx["i"]]
        ctx["i"] += 1
        if not user32.IsWindow(hwnd) or hwnd not in self.embedded:
            self.after(10, self.afk_step)
            return
        try:
            self.nb.select(info["frame"])
            self.update_idletasks()
            self.sync_docks()
        except tk.TclError:
            pass
        embedded_mode = info.get("mode") == "embed"
        expected = self.root_hwnd() if embedded_mode else hwnd
        force_foreground(expected)
        if embedded_mode:
            user32.SetFocus(hwnd)
        self.after(450, lambda: self.afk_jump(expected, hwnd, info))

    @afk_safe
    def afk_jump(self, expected, hwnd, info, attempt=0):
        # Safety: only press Space if the game really is the active window.
        if user32.GetForegroundWindow() == expected:
            send_key(0x20, True)                                  # VK_SPACE down
            self.after(90, lambda: send_key(0x20, False))         # ...and up
            info["afk"]["last"] = "jumped " + time.strftime("%H:%M")
        elif attempt < 2 and user32.IsWindow(hwnd):               # Windows didn't switch: retry
            force_foreground(expected)
            self.after(400, lambda: self.afk_jump(expected, hwnd, info, attempt + 1))
            return
        else:
            info["afk"]["last"] = "skipped (couldn't focus game) " + time.strftime("%H:%M")
            log_error(f"Anti-AFK skipped {info['label']}: couldn't bring the game window to the front.")
        self.after(700, self.afk_step)

    @afk_safe
    def afk_finish(self):
        ctx = self.afk_ctx
        self.afk_ctx = None
        for hwnd, info in ctx["targets"]:
            if self.embedded.get(hwnd) is info and info["afk"]["on"]:
                self.afk_reschedule(info)   # each account restarts its own countdown
        try:
            if ctx["prev_tab"] and ctx["prev_tab"] in [str(t) for t in self.nb.tabs()]:
                self.nb.select(ctx["prev_tab"])
        except tk.TclError:
            pass
        self.sync_docks()
        prev = ctx["prev_fg"]
        if prev and user32.IsWindow(prev) and prev not in [h for h, _ in ctx["targets"]]:
            force_foreground(prev)
        if ctx["iconic"]:
            self.app.iconify()
        self.afk_running = False

    def on_afk_mode(self, _event=None):
        label = self.afk_mode_box.get()
        for key, text in AFK_MODES:
            if text == label:
                self.afk_mode.set(key)
                self.app.settings["afk_mode"] = key
                save_settings(self.app.settings)

    def afk_abort(self):
        """Something went wrong mid-cycle: reset so the next timer can run normally."""
        ctx, self.afk_ctx = self.afk_ctx, None
        targets = ctx["targets"] if ctx else self.afk_pending
        self.afk_pending = []
        for hwnd, info in targets:
            if self.embedded.get(hwnd) is info and info["afk"]["on"]:
                self.afk_reschedule(info)
        self.afk_running = False
        self.afk_status.set("Anti-AFK hit a problem (see error.log)")

    # ----- used by the Recorder's schedule -----
    def afk_due_any(self):
        now = time.time()
        return any(i["kind"] == "game" and i["afk"]["on"] and now >= i["afk"]["next"]
                   for i in self.embedded.values())

    def bring_account_game(self, name):
        """Show this account's game and make it the active window. Its hwnd, or None."""
        game = next((h for h, i in self.windows_for(name) if i["kind"] == "game"), None)
        if game is None:
            return None
        info = self.embedded[game]
        self.app.select_account(name)
        self.nb.select(info["frame"])
        self.update_idletasks()
        self.sync_docks()
        force_foreground(game if info.get("mode") == "dock" else self.root_hwnd())
        if info.get("mode") != "dock":
            user32.SetFocus(game)
        return game

    def set_account_afk(self, name):
        """Switch Anti-AFK on for this account's game(s) (keeps a timer that's already running)."""
        for _h, info in self.windows_for(name):
            if info["kind"] == "game" and not info["afk"]["on"]:
                info["afk"]["on"] = True
                self.afk_reschedule(info)
                self.refresh_tab_label(info)
                self.app.remember_afk(info)
        self.load_afk_controls()

    # ----- switching what's shown (driven by the account list) -----
    def windows_for(self, account):
        return [(h, i) for h, i in self.embedded.items()
                if i["account"] == account and user32.IsWindow(h)]

    def show_account(self, name):
        """Show this account's game (or its browser if it has no game yet)."""
        if not self.alive:
            return
        cur = self.current_hwnd()
        if cur and self.embedded[cur]["account"] == name:
            return   # already showing one of this account's windows (e.g. its browser)
        cands = self.windows_for(name)
        pick = next((i for _h, i in cands if i["kind"] == "game"), None)
        if pick is None and cands:
            pick = cands[0][1]
        self.nb.select(pick["frame"] if pick else self.empty)

    def show_for_selected_account(self):
        if not self.alive:
            return
        name = self.app.current_account()
        if name:
            self.show_account(name)

    def window_title(self, info):
        afk = info["afk"]
        return info["label"] + (f"  (AFK {afk['minutes']}m)" if afk["on"] else "")

    def refresh_picker(self):
        items = list(self.embedded.items())
        self.picker_hwnds = [h for h, _ in items]
        self.picker["values"] = [self.window_title(i) for _, i in items]
        cur = self.current_hwnd()
        if cur in self.picker_hwnds:
            self.picker.current(self.picker_hwnds.index(cur))
        else:
            self.picker.set("")
        info = self.embedded.get(cur)
        both = False
        if info and info["account"]:
            both = len({i["kind"] for _, i in items if i["account"] == info["account"]}) > 1
        self.kind_btn.config(state="normal" if both else "disabled")

    def on_picker(self, _event=None):
        idx = self.picker.current()
        if 0 <= idx < len(self.picker_hwnds):
            info = self.embedded.get(self.picker_hwnds[idx])
            if info:
                self.nb.select(info["frame"])
                if info["account"]:
                    self.app.select_account(info["account"])

    def toggle_kind(self):
        cur = self.current_hwnd()
        if not cur:
            return
        info = self.embedded[cur]
        for _h, other in self.windows_for(info["account"]):
            if other["kind"] != info["kind"]:
                self.nb.select(other["frame"])
                return

    def close_current(self):
        hwnd = self.current_hwnd()
        if hwnd:
            self.close_tab(hwnd)

    def close_tab(self, hwnd):
        """Close the embedded window itself (the game or browser) and remove its tab."""
        info = self.embedded.get(hwnd)
        if not info or not user32.IsWindow(hwnd):
            self.prune_dead()
            return
        if info["kind"] == "game" and not messagebox.askyesno(
                "Close game", f"Close '{info['label']}'?\nThis exits that Roblox game.", parent=self):
            return
        if info["kind"] == "game" and info["account"]:
            self.app.note_manual_close(info["account"])   # you closed it on purpose
        pid = get_pid(hwnd)
        user32.PostMessageW(hwnd, WM_CLOSE, 0, 0)
        self.after(400, lambda: self.check_closed(hwnd, pid, 0))

    def close_account_games(self, name):
        """Close an account's leftover game window(s) before rejoining (auto-reconnect)."""
        for hwnd, info in list(self.embedded.items()):
            if info["account"] == name and info["kind"] == "game" and user32.IsWindow(hwnd):
                pid = get_pid(hwnd)
                user32.PostMessageW(hwnd, WM_CLOSE, 0, 0)
                self.after(5000, lambda h=hwnd, p=pid: self.force_close(h, p))

    def force_close(self, hwnd, pid):
        if self.alive and user32.IsWindow(hwnd):
            subprocess.Popen(["taskkill", "/PID", str(pid), "/T", "/F"],
                             creationflags=0x08000000)  # CREATE_NO_WINDOW

    def check_closed(self, hwnd, pid, attempt):
        if not self.alive:
            return
        if not user32.IsWindow(hwnd) or hwnd not in self.embedded:
            self.prune_dead()
            return
        if attempt < 8:
            self.after(400, lambda: self.check_closed(hwnd, pid, attempt + 1))
            return
        if messagebox.askyesno("Not closing",
                               "That window didn't close. Force close it?", parent=self):
            subprocess.Popen(["taskkill", "/PID", str(pid), "/T", "/F"],
                             creationflags=0x08000000)  # CREATE_NO_WINDOW
            self.after(800, self.prune_dead)

    def detach(self, hwnd):
        info = self.embedded.pop(hwnd, None)
        if not info:
            return
        self.release_input(info)
        if user32.IsWindow(hwnd) and user32.IsHungAppWindow(hwnd):
            self.released.add(hwnd)               # frozen: just let go, waiting on it would hang us
        elif user32.IsWindow(hwnd):
            if info.get("mode") == "dock":
                _set_long(hwnd, GWLP_HWNDPARENT, 0)
            else:
                user32.SetParent(hwnd, None)
            if info["style"] is not None:
                _set_long(hwnd, GWL_STYLE, info["style"])
            user32.SetWindowPos(hwnd, None, 0, 0, 0, 0, SWP_FLAGS_FRAMECHANGE)
            if info["rect"]:
                l, t, r, b = info["rect"]
                user32.MoveWindow(hwnd, l, t, max(r - l, 400), max(b - t, 300), True)
            user32.ShowWindow(hwnd, SW_SHOW)
            self.released.add(hwnd)
        self.nb.forget(info["frame"])
        info["frame"].destroy()
        self.show_for_selected_account()
        self.update_layout()

    def detach_current(self):
        current = str(self.nb.select())
        for hwnd, info in list(self.embedded.items()):
            if str(info["frame"]) == current:
                self.detach(hwnd)
                return

    def detach_all(self):
        for hwnd in list(self.embedded):
            self.detach(hwnd)

    def game_pids(self):
        """Processes of the games in Game View, including popped-out ones."""
        hwnds = [h for h, i in self.embedded.items() if i["kind"] == "game"] + list(self.popped)
        return {get_pid(h) for h in hwnds if user32.IsWindow(h)} - {0}

    def close(self):
        self.alive = False
        self.detach_all()   # give windows back so the browser/Roblox aren't closed with this panel
        self.app.gameview = None
        self.app.set_topbar_visible(True)       # never leave the window without its top bar
        self.destroy()
        self.app.restore_window_size()


# ---------------------------------------------------------------------------
# Macro recorder (TinyTask-style)
# ---------------------------------------------------------------------------
class KBDLLHOOKSTRUCT(ctypes.Structure):
    _fields_ = [("vkCode", wintypes.DWORD), ("scanCode", wintypes.DWORD), ("flags", wintypes.DWORD),
                ("time", wintypes.DWORD), ("dwExtraInfo", ctypes.c_size_t)]


class MSLLHOOKSTRUCT(ctypes.Structure):
    _fields_ = [("pt", wintypes.POINT), ("mouseData", wintypes.DWORD), ("flags", wintypes.DWORD),
                ("time", wintypes.DWORD), ("dwExtraInfo", ctypes.c_size_t)]


# mouse messages -> (button, is_down)
_MOUSE_BUTTONS = {0x0201: ("l", True), 0x0202: ("l", False), 0x0204: ("r", True),
                  0x0205: ("r", False), 0x0207: ("m", True), 0x0208: ("m", False)}
_BUTTON_FLAGS = {("l", True): 0x0002, ("l", False): 0x0004, ("r", True): 0x0008,
                 ("r", False): 0x0010, ("m", True): 0x0020, ("m", False): 0x0040}


# movement keys and the key that undoes them: (opposite vk, its scan code, is_extended)
_OPPOSITE_KEY = {0x57: (0x53, 0x1F, False), 0x53: (0x57, 0x11, False),    # W <-> S
                 0x41: (0x44, 0x20, False), 0x44: (0x41, 0x1E, False),    # A <-> D
                 0x26: (0x28, 0x50, True), 0x28: (0x26, 0x48, True),      # Up <-> Down
                 0x25: (0x27, 0x4D, True), 0x27: (0x25, 0x4B, True)}      # Left <-> Right


def reverse_events(events):
    """The recording played backwards, so a character walks back along the route it took:
    time runs in reverse, movement keys are swapped for their opposite (W<->S, A<->D, arrows),
    key/button presses become releases and the other way round, and mouse paths are retraced."""
    if not events:
        return []
    total = events[-1][0]
    out = []
    for ev in events:
        t = total - ev[0]
        kind = ev[1]
        if kind == "m":
            out.append((t, "m", ev[2], ev[3]))
        elif kind == "b":
            out.append((t, "b", ev[2], not ev[3], ev[4], ev[5]))
        elif kind == "w":
            out.append((t, "w", -ev[2], ev[3], ev[4]))
        elif kind == "k":
            vk, scan, ext = ev[2], ev[3], ev[4]
            if vk in _OPPOSITE_KEY:
                vk, scan, ext = _OPPOSITE_KEY[vk]
            out.append((t, "k", vk, scan, ext, not ev[5]))
    out.reverse()                       # latest original event happens first
    out.sort(key=lambda e: e[0])        # (stable: keeps the reversed order for equal times)
    return out


class Recorder:
    """Records mouse + keyboard through low-level hooks and plays them back with SendInput.
    Event tuples (time in ms from start):
      (t, "m", x, y)  (t, "b", button, down, x, y)  (t, "w", delta, x, y)  (t, "k", vk, scan, ext, down)
    """
    VK_RECORD = 0x76   # F7
    VK_PLAY = 0x77     # F8

    def __init__(self):
        self.events = []
        self.recording = False
        self.playing = False
        self.t0 = 0.0
        self.hotkeys = queue.Queue()
        self.stop_flag = threading.Event()
        self.loop_index = 0
        self.loop_total = 1
        self.hook_thread = None
        self.thread_id = None
        self.hooks_ok = False
        self.ready = threading.Event()
        self.error = None
        self.last_real = time.time()    # last keyboard/mouse input from you (not from playback)

    # ----- hooks (own thread with a message loop) -----
    def start_hooks(self):
        if self.hook_thread is not None and self.hook_thread.is_alive():
            if self.thread_id:
                return self.hooks_ok
            self.hook_thread.join(1)            # still shutting down from stop_hooks()
        self.ready.clear()
        self.hook_thread = threading.Thread(target=self._hook_main, daemon=True)
        self.hook_thread.start()
        self.ready.wait(3)
        return self.hooks_ok

    def stop_hooks(self):
        self.hooks_ok = False
        if self.thread_id:
            user32.PostThreadMessageW(self.thread_id, 0x0012, 0, 0)    # WM_QUIT
            self.thread_id = None

    def _hook_main(self):
        self.thread_id = kernel32.GetCurrentThreadId()
        self._kb_proc = HOOKPROC(self._on_key)          # keep references alive
        self._ms_proc = HOOKPROC(self._on_mouse)
        module = kernel32.GetModuleHandleW(None)
        kb = user32.SetWindowsHookExW(13, self._kb_proc, module, 0)    # WH_KEYBOARD_LL
        ms = user32.SetWindowsHookExW(14, self._ms_proc, module, 0)    # WH_MOUSE_LL
        self.hooks_ok = bool(kb and ms)
        self.ready.set()
        if self.hooks_ok:
            msg = wintypes.MSG()
            while user32.GetMessageW(ctypes.byref(msg), None, 0, 0) > 0:
                pass
        for hook in (kb, ms):
            if hook:
                user32.UnhookWindowsHookEx(hook)

    def _now(self):
        return int((time.perf_counter() - self.t0) * 1000)

    def _on_key(self, code, wparam, lparam):
        try:
            if code >= 0:
                info = ctypes.cast(lparam, ctypes.POINTER(KBDLLHOOKSTRUCT)).contents
                if not (info.flags & 0x10):                            # ignore injected input
                    self.last_real = time.time()
                    down = wparam in (0x0100, 0x0104)
                    if info.vkCode in (self.VK_RECORD, self.VK_PLAY):  # our hotkeys: swallow them
                        if down:
                            self.hotkeys.put("record" if info.vkCode == self.VK_RECORD else "play")
                        return 1
                    if self.recording:
                        self.events.append((self._now(), "k", info.vkCode, info.scanCode,
                                            bool(info.flags & 0x01), down))
        except Exception:
            log_error(traceback.format_exc())
        return user32.CallNextHookEx(None, code, wparam, lparam)

    def _on_mouse(self, code, wparam, lparam):
        try:
            if code >= 0:
                info = ctypes.cast(lparam, ctypes.POINTER(MSLLHOOKSTRUCT)).contents
                if not (info.flags & 0x01):                            # ignore injected input
                    self.last_real = time.time()
                if self.recording and not (info.flags & 0x01):
                    x, y, t = info.pt.x, info.pt.y, self._now()
                    if wparam == 0x0200:
                        last = self.events[-1] if self.events else None
                        if not (last and last[1] == "m" and last[2:] == (x, y)):
                            self.events.append((t, "m", x, y))
                    elif wparam in _MOUSE_BUTTONS:
                        button, down = _MOUSE_BUTTONS[wparam]
                        self.events.append((t, "b", button, down, x, y))
                    elif wparam == 0x020A:                             # wheel
                        delta = ctypes.c_short((info.mouseData >> 16) & 0xFFFF).value
                        self.events.append((t, "w", delta, x, y))
        except Exception:
            log_error(traceback.format_exc())
        return user32.CallNextHookEx(None, code, wparam, lparam)

    # ----- recording -----
    def start_record(self):
        if self.playing:
            return False
        pt = wintypes.POINT()
        user32.GetCursorPos(ctypes.byref(pt))
        self.events = [(0, "m", pt.x, pt.y)]
        self.t0 = time.perf_counter()
        self.recording = True
        return True

    def stop_record(self, ignore_rect=None):
        """Stop. ignore_rect=(l,t,r,b): drop the trailing mouse events inside that rectangle
        (the click on the Stop button)."""
        self.recording = False
        if ignore_rect:
            l, t, r, b = ignore_rect
            while self.events:
                ev = self.events[-1]
                if ev[1] == "m":
                    x, y = ev[2], ev[3]
                elif ev[1] == "b":
                    x, y = ev[4], ev[5]
                elif ev[1] == "w":
                    x, y = ev[3], ev[4]
                else:
                    break
                if l <= x < r and t <= y < b:
                    self.events.pop()
                else:
                    break
        # anything still held when recording ended gets released, so loops don't pile up
        held_keys, held_buttons = {}, set()
        for ev in self.events:
            if ev[1] == "k":
                if ev[5]:
                    held_keys[ev[2]] = ev
                else:
                    held_keys.pop(ev[2], None)
            elif ev[1] == "b":
                if ev[3]:
                    held_buttons.add(ev[2])
                else:
                    held_buttons.discard(ev[2])
        end = (self.events[-1][0] if self.events else 0) + 1
        last_pos = next(((e[-2], e[-1]) for e in reversed(self.events) if e[1] in ("m", "b", "w")), (0, 0))
        for vk, ev in held_keys.items():
            self.events.append((end, "k", vk, ev[3], ev[4], False))
        for button in held_buttons:
            self.events.append((end, "b", button, False, last_pos[0], last_pos[1]))
        return len(self.events)

    def duration(self):
        return (self.events[-1][0] / 1000.0) if self.events else 0.0

    # ----- playback -----
    ZOOM_IN_NOTCHES = 40        # enough to reach first person from Roblox's furthest zoom

    def _zoom_reset(self, out, events, geometry):
        """Same camera zoom every run: with the mouse where the recording starts (over the game),
        scroll all the way in, then `out` notches back out. False if playback was stopped."""
        first = next((e for e in events if e[1] in ("m", "b", "w")), None)
        if first:
            x, y = first[-2], first[-1]            # every mouse event ends with its x, y
            self._move(x, y, geometry)
        for delta, count, pause in ((120, self.ZOOM_IN_NOTCHES, 0.02), (-120, out, 0.06)):
            for _ in range(count):
                self._mouse(0x0800, 0, 0, delta)                       # MOUSEEVENTF_WHEEL
                if not self._sleep_until(time.perf_counter() + pause):
                    return False
            if not self._sleep_until(time.perf_counter() + 0.3):
                return False
        return True

    def play(self, loops=1, speed=1.0, delay=0.5, reset=False, reset_wait=6.0, back=False, events=None,
             zoom=None):
        """loops=0 means repeat until stopped. reset=True presses Esc, R, Enter (Roblox's
        reset-character shortcut) before every run so each run starts from the spawn point.
        back=True plays the recording in reverse after each run to walk back to the start.
        events: play these instead of the current recording (the scheduler's saved files).
        zoom: if set, reset the camera zoom before each run (scroll fully in, then this many out)."""
        events = list(events if events is not None else self.events)
        if self.playing or self.recording or not events:
            return False
        self.stop_flag.clear()
        self.playing = True
        self.loop_total = loops
        self.loop_index = 0
        threading.Thread(target=self._play_main, args=(events, loops, max(speed, 0.05), delay, reset, reset_wait, back,
                                                       zoom), daemon=True).start()
        return True

    def stop_play(self):
        self.stop_flag.set()

    def _sleep_until(self, target):
        while not self.stop_flag.is_set():
            left = target - time.perf_counter()
            if left <= 0:
                return True
            time.sleep(min(left, 0.02))
        return False

    def _reset_character(self, wait):
        """Esc -> R -> Enter, then wait for the respawn. False if playback was stopped."""
        for vk, scan in ((0x1B, 0x01), (0x52, 0x13), (0x0D, 0x1C)):
            self._key(vk, scan, False, True)
            if not self._sleep_until(time.perf_counter() + 0.06):
                self._key(vk, scan, False, False)
                return False
            self._key(vk, scan, False, False)
            if not self._sleep_until(time.perf_counter() + 0.4):
                return False
        return self._sleep_until(time.perf_counter() + wait)

    def _run_events(self, events, speed, geometry, keys, buttons):
        """Play one list of events. False if playback was stopped part-way."""
        start = time.perf_counter()
        for ev in events:
            if not self._sleep_until(start + ev[0] / 1000.0 / speed):
                return False
            self._send(ev, geometry, keys, buttons)
        return True

    def _play_main(self, events, loops, speed, delay, reset=False, reset_wait=6.0, back=False, zoom=None):
        keys, buttons = set(), set()
        return_trip = reverse_events(events) if back else None
        try:
            vx, vy = user32.GetSystemMetrics(76), user32.GetSystemMetrics(77)
            vw, vh = user32.GetSystemMetrics(78), user32.GetSystemMetrics(79)
            geometry = (vx, vy, max(vw, 1), max(vh, 1))
            if not self._sleep_until(time.perf_counter() + delay):
                return
            while not self.stop_flag.is_set() and (loops == 0 or self.loop_index < loops):
                if reset and not self._reset_character(reset_wait):
                    break
                if zoom is not None and not self._zoom_reset(zoom, events, geometry):
                    break
                if not self._run_events(events, speed, geometry, keys, buttons):
                    break
                if return_trip:                                   # walk back to where it began
                    if not self._sleep_until(time.perf_counter() + 0.3):
                        break
                    if not self._run_events(return_trip, speed, geometry, keys, buttons):
                        break
                self.loop_index += 1
                if not self._sleep_until(time.perf_counter() + 0.05):
                    break
        except Exception:
            log_error(traceback.format_exc())
        finally:
            for vk, scan, ext in list(keys):                 # never leave a key/button stuck down
                self._key(vk, scan, ext, False)
            for button in list(buttons):
                self._mouse(_BUTTON_FLAGS[(button, False)])
            self.playing = False

    @staticmethod
    def _input(inp):
        user32.SendInput(1, ctypes.byref(inp), ctypes.sizeof(INPUT))

    def _mouse(self, flags, dx=0, dy=0, data=0):
        mi = MOUSEINPUT(dx, dy, data & 0xFFFFFFFF, flags, 0, 0)
        self._input(INPUT(0, _INPUT_UNION(mi=mi)))

    def _move(self, x, y, geometry):
        vx, vy, vw, vh = geometry
        nx = round((x - vx) * 65535 / max(vw - 1, 1))
        ny = round((y - vy) * 65535 / max(vh - 1, 1))
        self._mouse(0x0001 | 0x8000 | 0x4000, nx, ny)     # MOVE | ABSOLUTE | VIRTUALDESK

    def _key(self, vk, scan, ext, down):
        flags = (0x0001 if ext else 0) | (0 if down else 0x0002)
        ki = KEYBDINPUT(vk, scan, flags, 0, 0)
        self._input(INPUT(1, _INPUT_UNION(ki=ki)))

    def _send(self, ev, geometry, keys, buttons):
        kind = ev[1]
        if kind == "m":
            self._move(ev[2], ev[3], geometry)
        elif kind == "b":
            self._move(ev[4], ev[5], geometry)
            self._mouse(_BUTTON_FLAGS[(ev[2], ev[3])])
            (buttons.add if ev[3] else buttons.discard)(ev[2])
        elif kind == "w":
            self._move(ev[3], ev[4], geometry)
            self._mouse(0x0800, 0, 0, ev[2])
        elif kind == "k":
            self._key(ev[2], ev[3], ev[4], ev[5])
            (keys.add if ev[5] else keys.discard)((ev[2], ev[3], ev[4]))

    # ----- save / load -----
    def save(self, path):
        with open(path, "w", encoding="utf-8") as f:
            json.dump({"version": 1, "events": self.events}, f)

    @staticmethod
    def read_file(path):
        with open(path, "r", encoding="utf-8") as f:
            data = json.load(f)
        events = [tuple(e) for e in data["events"]]
        for e in events:
            if e[1] not in ("m", "b", "w", "k") or not isinstance(e[0], (int, float)):
                raise ValueError("Not a valid recording file.")
        return events

    def load(self, path):
        self.events = self.read_file(path)
        return len(self.events)


def join_recordings(recordings, gap_ms=500):
    """Several recordings played back to back as one (each one's times shifted after the last)."""
    out, offset = [], 0
    for events in recordings:
        if not events:
            continue
        out.extend((e[0] + offset,) + tuple(e[1:]) for e in events)
        offset = out[-1][0] + gap_ms
    return out


class StepDialog(tk.Toplevel):
    """Add / edit one schedule step: an account and the recording(s) it plays, in order."""

    def __init__(self, parent, accounts, step=None):
        super().__init__(parent)
        self.title("Schedule step")
        self.transient(parent)
        self.resizable(False, False)
        self.result = None
        self.files = list((step or {}).get("files", []))
        self.account = tk.StringVar(value=(step or {}).get("account") or (accounts[0] if accounts else ""))
        row = tk.Frame(self)
        row.pack(padx=12, pady=(12, 4), fill="x")
        tk.Label(row, text="Account:").pack(side="left")
        ttk.Combobox(row, state="readonly", values=accounts, textvariable=self.account,
                     width=18).pack(side="left", padx=6)
        tk.Label(self, text="Recordings (played in this order):").pack(padx=12, anchor="w")
        self.box = tk.Listbox(self, height=5, width=40, activestyle="none", exportselection=False)
        self.box.pack(padx=12, fill="x")
        btns = tk.Frame(self)
        btns.pack(pady=4)
        for text, cmd in (("Add...", self.add), ("Remove", self.remove),
                          ("▲", lambda: self.move(-1)), ("▼", lambda: self.move(1))):
            tk.Button(btns, text=text, command=cmd).pack(side="left", padx=2)
        ok = tk.Frame(self)
        ok.pack(pady=(4, 12))
        tk.Button(ok, text="OK", width=10, command=self.ok).pack(side="left", padx=4)
        tk.Button(ok, text="Cancel", width=10, command=self.destroy).pack(side="left", padx=4)
        self.refresh()
        parent.app.apply_theme()
        self.grab_set()

    def refresh(self):
        self.box.delete(0, tk.END)
        for path in self.files:
            self.box.insert(tk.END, os.path.basename(path))

    def add(self):
        for path in filedialog.askopenfilenames(parent=self, filetypes=[("Recording", "*.rec"),
                                                                         ("All files", "*.*")]):
            try:
                Recorder.read_file(path)
            except (OSError, ValueError, KeyError, IndexError, TypeError) as e:
                messagebox.showerror("Recorder", f"Couldn't load {os.path.basename(path)}: {e}", parent=self)
                continue
            self.files.append(path)
        self.refresh()

    def remove(self):
        sel = self.box.curselection()
        if sel:
            del self.files[sel[0]]
            self.refresh()

    def move(self, step):
        sel = self.box.curselection()
        if sel and 0 <= sel[0] + step < len(self.files):
            i = sel[0]
            self.files[i], self.files[i + step] = self.files[i + step], self.files[i]
            self.refresh()
            self.box.selection_set(i + step)

    def ok(self):
        if not self.account.get() or not self.files:
            messagebox.showinfo("Schedule step", "Pick an account and at least one recording.", parent=self)
            return
        self.result = {"account": self.account.get(), "files": list(self.files)}
        self.destroy()


class AccountGrid(tk.Frame):
    """The account list, laid out in two columns. Offers the few Listbox calls the app uses
    (insert/delete, curselection, selection_set/clear, see)."""

    COLS = 2

    def __init__(self, parent, font, on_select, on_double, color_for=None, on_move=None, on_menu=None):
        super().__init__(parent, class_="AccountGrid", highlightthickness=1, bd=0)
        self.font = font
        self.on_select = on_select
        self.on_double = on_double
        self.color_for = color_for          # index -> text colour (the account's border colour)
        self.on_move = on_move              # (from index, to index): you dragged an account
        self.on_menu = on_menu              # (index, event): you right-clicked an account
        self.drag_from = None
        self.drop_at = None
        self.cells = []
        self.sel = None
        self.t = THEMES["light"]
        for col in range(self.COLS):
            self.columnconfigure(col, weight=1, uniform="accounts")

    def delete(self, _first=0, _last=None):
        for cell in self.cells:
            cell.destroy()
        self.cells = []
        self.sel = None

    def insert(self, _index, text):
        i = len(self.cells)
        cell = tk.Label(self, text=text, font=self.font, anchor="w", padx=8, pady=3)
        cell.grid(row=i // self.COLS, column=i % self.COLS, sticky="ew")
        cell.bind("<Button-1>", lambda _e, i=i: self.click(i))
        cell.bind("<Double-Button-1>", lambda _e: self.on_double())
        cell.bind("<B1-Motion>", self.drag)
        cell.bind("<ButtonRelease-1>", self.drop)
        cell.bind("<Button-3>", lambda e, i=i: self.right_click(i, e))
        self.cells.append(cell)
        self.paint()

    def click(self, i):
        self.drag_from, self.drop_at = i, None
        self.selection_set(i)
        self.on_select()

    def right_click(self, i, event):
        self.click(i)
        if self.on_menu:
            self.on_menu(i, event)

    def cell_at(self, x_root, y_root):
        widget = self.winfo_containing(x_root, y_root)
        return self.cells.index(widget) if widget in self.cells else None

    def drag(self, event):
        """Drag an account onto another one to move it there (the target is outlined)."""
        if self.drag_from is None or not self.on_move:
            return
        target = self.cell_at(event.x_root, event.y_root)
        if target != self.drop_at:
            self.drop_at = target
            for cell in self.cells:
                cell.configure(cursor="fleur" if target is not None else "")
            self.paint()

    def drop(self, _event):
        src, dst = self.drag_from, self.drop_at
        self.drag_from = self.drop_at = None
        for cell in self.cells:
            cell.configure(cursor="")
        self.paint()
        if src is not None and dst is not None and src != dst and self.on_move:
            self.on_move(src, dst)

    def curselection(self):
        return (self.sel,) if self.sel is not None else ()

    def selection_clear(self, _first=0, _last=None):
        self.sel = None
        self.paint()

    def selection_set(self, i):
        self.sel = i if 0 <= i < len(self.cells) else None
        self.paint()

    def see(self, _i):
        pass                                   # every account is always visible

    def set_theme(self, t):
        self.t = t
        self.paint()

    def paint(self):
        t = self.t
        try:
            self.configure(bg=t["field"], highlightbackground=t["border"])
            for i, cell in enumerate(self.cells):
                on = i == self.sel
                color = (self.color_for(i) if self.color_for else None) or t["ffg"]
                target = i == self.drop_at and i != self.drag_from          # where a drag would land
                bg = t["sel_bg"] if on else t["field"]
                edge = t["sel_bg"] if target else bg                         # outline only the target
                cell.configure(bg=bg, fg=t["sel_fg"] if on else color, highlightthickness=2,
                               highlightbackground=edge, highlightcolor=edge)
        except tk.TclError:
            pass


class RecorderPanel(tk.Frame):
    """The recorder's controls (like TinyTask), shown under the accounts list."""

    def __init__(self, app, parent):
        super().__init__(parent)
        self.app = app
        self.alive = True
        self.rec = Recorder()
        if not self.rec.start_hooks():
            messagebox.showwarning("Recorder", "Couldn't start the keyboard/mouse hooks, so recording "
                                               "and the F7/F8 hotkeys won't work.", parent=self)

        self.status = tk.StringVar(value="Idle. Press F7 to record.")
        self.forever = tk.BooleanVar(value=False)
        self.repeat = tk.StringVar(value="1")
        self.speed = tk.StringVar(value="1x")
        self.reset_var = tk.BooleanVar(value=False)
        self.back_var = tk.BooleanVar(value=False)
        self.reset_wait = tk.StringVar(value="6")

        tk.Label(self, text="Recorder", font=("Segoe UI", 10, "bold")).pack(pady=(0, 2))
        self.tabs = ttk.Notebook(self)
        self.tabs.pack(fill="x")
        rec_tab, pl_tab, sched_tab = (tk.Frame(self.tabs) for _ in range(3))
        self.tabs.add(rec_tab, text=" Record ")
        self.tabs.add(pl_tab, text=" Playlist ")
        self.tabs.add(sched_tab, text=" Schedules ")
        row = tk.Frame(rec_tab)
        row.pack(pady=(0, 4))
        self.rec_btn = tk.Button(row, text="\u25CF Record (F7)", width=14,
                                 command=lambda: self.toggle_record(True))
        self.rec_btn.grid(row=0, column=0, padx=4)
        self.play_btn = tk.Button(row, text="\u25B6 Play (F8)", width=14,
                                  command=lambda: self.toggle_play(True))
        self.play_btn.grid(row=0, column=1, padx=4)

        opts = tk.Frame(rec_tab)
        opts.pack(pady=2)
        tk.Label(opts, text="Repeat:").grid(row=0, column=0, sticky="e")
        self.repeat_box = tk.Spinbox(opts, from_=1, to=9999, width=6, textvariable=self.repeat)
        self.repeat_box.grid(row=0, column=1, padx=(4, 6))
        tk.Checkbutton(opts, text="Forever", variable=self.forever).grid(row=0, column=2, padx=(0, 10))
        tk.Label(opts, text="Speed:").grid(row=0, column=3, sticky="e")
        ttk.Combobox(opts, state="readonly", width=6, textvariable=self.speed,
                     values=["0.25x", "0.5x", "1x", "2x", "4x", "8x"]).grid(row=0, column=4, padx=4)

        tk.Checkbutton(rec_tab, text="Walk back to the start afterwards (plays it in reverse)",
                       variable=self.back_var).pack(pady=(0, 2))
        reset_row = tk.Frame(rec_tab)
        reset_row.pack(pady=(0, 4))
        tk.Checkbutton(reset_row, text="Reset character before each run (Esc, R, Enter)",
                       variable=self.reset_var).grid(row=0, column=0, columnspan=3)
        tk.Label(reset_row, text="then wait").grid(row=1, column=0, sticky="e")
        tk.Spinbox(reset_row, from_=1, to=30, width=4, textvariable=self.reset_wait).grid(row=1, column=1, padx=4)
        tk.Label(reset_row, text="seconds for the respawn").grid(row=1, column=2, sticky="w")
        zcfg = self.app.settings.get("zoom_reset", {})
        self.zoom_on = tk.BooleanVar(value=bool(zcfg.get("on", False)))
        self.zoom_out = tk.StringVar(value=str(zcfg.get("out", 10)))
        zoom_row = tk.Frame(rec_tab)
        zoom_row.pack(pady=(0, 4))
        tk.Checkbutton(zoom_row, text="Reset camera zoom before each run: all the way in, then out",
                       variable=self.zoom_on, command=self.save_zoom).grid(row=0, column=0, columnspan=3)
        zbox = tk.Spinbox(zoom_row, from_=0, to=40, width=4, textvariable=self.zoom_out, command=self.save_zoom)
        zbox.grid(row=1, column=1, padx=4)
        zbox.bind("<FocusOut>", lambda _e: self.save_zoom())
        tk.Label(zoom_row, text="notches (0 = stay in first person)").grid(row=1, column=2, sticky="w")

        files = tk.Frame(rec_tab)
        files.pack(pady=2)
        tk.Button(files, text="Save...", width=10, command=self.save).grid(row=0, column=0, padx=4)
        tk.Button(files, text="Load...", width=10, command=self.load).grid(row=0, column=1, padx=4)

        tk.Label(rec_tab, textvariable=self.status, font=("Segoe UI", 10, "bold")).pack(pady=(4, 0))
        tk.Label(rec_tab, fg="#555", font=("Segoe UI", 9), justify="center",
                 text="Everything you do while recording is captured, including typing,\n"
                      "so don't type passwords. F7/F8 work while this panel is open\n"
                      "(and F8 while a schedule is on, even with the panel hidden)."
                 ).pack(pady=(0, 2))

        self.build_playlist(pl_tab)
        self.build_schedule(sched_tab)
        self.after(100, self.poll)
        self.after(1000, self.sched_tick)

    # ----- playlist: several saved recordings played back to back -----
    def build_playlist(self, parent):
        self.playlist = [p for p in self.app.settings.get("playlist", []) if isinstance(p, str)]
        tk.Label(parent, text="Playlist", font=("Segoe UI", 10, "bold")).pack(pady=(4, 0))
        self.pl_list = tk.Listbox(parent, height=3, activestyle="none", exportselection=False)
        self.pl_list.pack(fill="x", padx=8)
        btns = tk.Frame(parent)
        btns.pack(pady=2)
        for text, cmd in (("Add...", self.pl_add), ("Remove", self.pl_remove),
                          ("▲", lambda: self.pl_move(-1)), ("▼", lambda: self.pl_move(1))):
            tk.Button(btns, text=text, command=cmd).pack(side="left", padx=2)
        self.pl_btn = tk.Button(btns, text="▶ Play playlist", command=self.pl_play)
        self.pl_btn.pack(side="left", padx=(8, 0))
        self.pl_refresh()

    def pl_refresh(self, select=None):
        self.pl_list.delete(0, tk.END)
        for path in self.playlist:
            self.pl_list.insert(tk.END, os.path.basename(path))
        if select is not None and 0 <= select < len(self.playlist):
            self.pl_list.selection_set(select)
        self.app.settings["playlist"] = list(self.playlist)
        save_settings(self.app.settings)

    def pl_add(self):
        for path in filedialog.askopenfilenames(parent=self, filetypes=[("Recording", "*.rec"),
                                                                         ("All files", "*.*")]):
            try:
                Recorder.read_file(path)
            except (OSError, ValueError, KeyError, IndexError, TypeError) as e:
                messagebox.showerror("Recorder", f"Couldn't load {os.path.basename(path)}: {e}", parent=self)
                continue
            self.playlist.append(path)
        self.pl_refresh()

    def pl_remove(self):
        sel = self.pl_list.curselection()
        if sel:
            del self.playlist[sel[0]]
            self.pl_refresh(min(sel[0], len(self.playlist) - 1))

    def pl_move(self, step):
        sel = self.pl_list.curselection()
        if sel and 0 <= sel[0] + step < len(self.playlist):
            i = sel[0]
            self.playlist[i], self.playlist[i + step] = self.playlist[i + step], self.playlist[i]
            self.pl_refresh(i + step)

    def pl_play(self):
        """Play the playlist once through (with Repeat / Forever / Speed / walk back / reset)."""
        rec = self.rec
        if rec.playing:
            self.toggle_play(True)                   # same as F8: stop
            return
        if self.sched["state"] != "off":
            self.status.set("Turn the schedule off first.")
            return
        if rec.recording:
            self.status.set("Stop recording first.")
            return
        try:
            events = join_recordings([self.sched_events(p) for p in self.playlist])
        except (OSError, ValueError, KeyError, IndexError, TypeError) as e:
            self.status.set(f"Couldn't read a playlist file: {e}")
            return
        if not events:
            self.status.set("Add recordings to the playlist first.")
            return
        try:
            loops = 0 if self.forever.get() else max(1, int(self.repeat.get()))
        except ValueError:
            loops = 1
        rec.play(loops, self.sched_speed(), delay=1.0, reset=bool(self.reset_var.get()),
                 reset_wait=self.sched_reset_wait(), back=bool(self.back_var.get()), events=events,
                 zoom=self.zoom_value())

    # ----- schedules: at set minutes past each hour, play steps (account + recordings) in order -----
    SCHED_BETWEEN = [("afk", "Anti-AFK"), ("loop", "loop another recording"), ("none", "nothing")]

    @staticmethod
    def migrate_schedules(cfg):
        """Older settings had one schedule (one recording on several accounts)."""
        if isinstance(cfg.get("schedules"), list):
            return cfg["schedules"]
        slots = cfg.get("at_slots") or [[m, True] for m in cfg.get("at", [])]
        names = list(cfg.get("accounts") or ([cfg["account"]] if cfg.get("account") else []))
        steps = [{"account": n, "files": [cfg["file"]]} for n in names] if cfg.get("file") else []
        return [{"name": "Schedule 1", "on": True, "slots": slots, "steps": steps}]

    def build_schedule(self, parent):
        cfg = self.app.settings.get("schedule", {})
        self.scheds = []
        for k, sc in enumerate(self.migrate_schedules(cfg)):
            slots = (list(sc.get("slots", [])) + [[None, False]] * 4)[:4]
            self.scheds.append({"name": sc.get("name") or f"Schedule {k + 1}", "on": bool(sc.get("on", True)),
                                "slots": [list(s) for s in slots],
                                "steps": [{"account": st.get("account", ""), "files": list(st.get("files", []))}
                                          for st in sc.get("steps", [])], "next": 0.0})
        if not self.scheds:
            self.scheds.append({"name": "Schedule 1", "on": True, "slots": [[None, False]] * 4,
                                "steps": [], "next": 0.0})
        self.sel = 0                                         # the schedule shown for editing
        self.sched_on = tk.BooleanVar(value=False)           # always starts off
        self.sched_loop_file = cfg.get("loop_file", "")
        self.sched_between = tk.StringVar(value=dict(self.SCHED_BETWEEN).get(cfg.get("between", "afk"), "Anti-AFK"))
        self.sched_mode = tk.StringVar(value=dict(AFK_MODES).get(cfg.get("mode", "away"), "When I'm away"))
        self.sched_status = tk.StringVar(value="")
        self.sched = {"state": "off", "next": 0.0, "started": 0.0, "wait_start": 0.0}
        self.sched_cache = {}                                # path -> (mtime, events)
        self.sched_at = [tk.StringVar(value="--") for _ in range(4)]
        self.sched_at_on = [tk.BooleanVar(value=False) for _ in range(4)]
        self.sel_on = tk.BooleanVar(value=True)
        self.sel_name = tk.StringVar()

        tk.Label(parent, text="Schedules", font=("Segoe UI", 10, "bold")).pack(pady=(4, 2))
        r0 = tk.Frame(parent)
        r0.pack(pady=1)
        tk.Checkbutton(r0, text="On (runs every ticked schedule)", variable=self.sched_on,
                       command=self.sched_toggled).pack(side="left")
        tk.Label(r0, text="  When:").pack(side="left")
        mode_box = ttk.Combobox(r0, state="readonly", width=14, textvariable=self.sched_mode,
                                values=[label for _k, label in AFK_MODES])
        mode_box.pack(side="left", padx=4)
        mode_box.bind("<<ComboboxSelected>>", lambda _e: self.sched_save())
        r1 = tk.Frame(parent)
        r1.pack(pady=1)
        self.sel_box = ttk.Combobox(r1, state="readonly", width=14, textvariable=self.sel_name)
        self.sel_box.pack(side="left")
        self.sel_box.bind("<<ComboboxSelected>>", lambda _e: self.select_sched(self.sel_box.current()))
        tk.Checkbutton(r1, text="use", variable=self.sel_on, command=self.sched_save).pack(side="left", padx=(4, 6))
        for text, cmd in (("+ Add", self.add_sched), ("Rename", self.rename_sched), ("Remove", self.remove_sched)):
            tk.Button(r1, text=text, command=cmd).pack(side="left", padx=1)
        r_at = tk.Frame(parent)
        r_at.pack(pady=1)
        tk.Label(r_at, text="at minute").pack(side="left")
        minute_values = ["--"] + [f"{m:02d}" for m in range(1, 61)]     # 60 = on the hour
        for var, on in zip(self.sched_at, self.sched_at_on):
            tk.Checkbutton(r_at, variable=on, command=self.sched_save).pack(side="left", padx=(6, 0))
            box = tk.Spinbox(r_at, values=minute_values, width=3, textvariable=var, wrap=True,
                             command=self.sched_save)
            box.pack(side="left")
            box.bind("<FocusOut>", lambda _e: self.sched_save())
            box.bind("<Return>", lambda _e: self.sched_save())
        tk.Label(parent, text="Steps (played in order - each is an account and its recordings):",
                 fg="#555", font=("Segoe UI", 9)).pack()
        self.steps_list = tk.Listbox(parent, height=4, activestyle="none", exportselection=False)
        self.steps_list.pack(fill="x", padx=8)
        self.steps_list.bind("<Double-Button-1>", lambda _e: self.edit_step())
        sb = tk.Frame(parent)
        sb.pack(pady=2)
        for text, cmd in (("Add step...", self.add_step), ("Edit...", self.edit_step), ("Remove", self.remove_step),
                          ("▲", lambda: self.move_step(-1)), ("▼", lambda: self.move_step(1))):
            tk.Button(sb, text=text, command=cmd).pack(side="left", padx=1)
        r3 = tk.Frame(parent)
        r3.pack(pady=1)
        tk.Label(r3, text="In between:").pack(side="left")
        between_box = ttk.Combobox(r3, state="readonly", width=20, textvariable=self.sched_between,
                                   values=[label for _k, label in self.SCHED_BETWEEN])
        between_box.pack(side="left", padx=4)
        between_box.bind("<<ComboboxSelected>>", lambda _e: self.sched_save())
        self.sched_loop_btn = tk.Button(r3, command=self.pick_loop_file)
        self.sched_loop_btn.pack(side="left")
        tk.Label(parent, textvariable=self.sched_status, fg="#555", font=("Segoe UI", 9),
                 justify="center").pack(pady=(1, 4))
        self.loading = True                      # the boxes are still empty: don't copy them over
        self.select_sched(0)

    # editing ----------------------------------------------------------------
    def select_sched(self, k):
        self.store_sel()
        self.sel = max(0, min(k, len(self.scheds) - 1))
        sc = self.scheds[self.sel]
        for (m, on), var, onvar in zip(sc["slots"], self.sched_at, self.sched_at_on):
            var.set("--" if m is None else f"{m or 60:02d}")
            onvar.set(bool(on))
        self.sel_on.set(sc["on"])
        self.loading = True
        self.sched_labels()
        self.loading = False

    def store_sel(self):
        """Copy what's shown (minutes, use) into the selected schedule."""
        if not getattr(self, "scheds", None) or getattr(self, "loading", False):
            return
        sc = self.scheds[min(self.sel, len(self.scheds) - 1)]
        slots = []
        for var, on in zip(self.sched_at, self.sched_at_on):
            text = var.get().strip()
            slots.append([int(text) % 60 if text.isdigit() and int(text) <= 60 else None, bool(on.get())])
        sc["slots"] = slots
        sc["on"] = bool(self.sel_on.get())

    def sched_labels(self):
        self.sel_box["values"] = [("" if sc["on"] else "(off) ") + sc["name"] for sc in self.scheds]
        self.sel_box.current(self.sel)
        self.steps_list.delete(0, tk.END)
        for st in self.scheds[self.sel]["steps"]:
            files = ", ".join(os.path.basename(f) for f in st["files"])
            missing = "" if st["account"] in self.app.accounts else "  (account removed)"
            self.steps_list.insert(tk.END, f"{st['account']}: {files}{missing}")
        loop = self.sched_between_key() == "loop"
        lname = os.path.basename(self.sched_loop_file) if self.sched_loop_file else "choose loop recording..."
        self.sched_loop_btn.config(text=lname[:24], state="normal" if loop else "disabled")

    def add_sched(self):
        self.store_sel()
        self.scheds.append({"name": f"Schedule {len(self.scheds) + 1}", "on": True,
                            "slots": [[None, False]] * 4, "steps": [], "next": 0.0})
        self.select_sched(len(self.scheds) - 1)
        self.sched_save()

    def rename_sched(self):
        sc = self.scheds[self.sel]
        name = simpledialog.askstring("Rename schedule", "Name:", initialvalue=sc["name"], parent=self)
        if name and name.strip():
            sc["name"] = name.strip()
            self.sched_save()

    def remove_sched(self):
        if len(self.scheds) == 1:
            self.scheds[0].update(slots=[[None, False]] * 4, steps=[], name="Schedule 1")
            self.select_sched(0)
        elif messagebox.askyesno("Remove schedule", f"Remove '{self.scheds[self.sel]['name']}'?", parent=self):
            del self.scheds[self.sel]
            self.loading = True                      # don't copy the removed one's boxes anywhere
            self.select_sched(self.sel)
        self.sched_save()

    def step_dialog(self, step=None):
        dlg = StepDialog(self, list(self.app.accounts), step)
        self.wait_window(dlg)
        return dlg.result

    def add_step(self):
        step = self.step_dialog()
        if step:
            self.scheds[self.sel]["steps"].append(step)
            self.sched_save()

    def edit_step(self):
        sel = self.steps_list.curselection()
        if sel:
            step = self.step_dialog(self.scheds[self.sel]["steps"][sel[0]])
            if step:
                self.scheds[self.sel]["steps"][sel[0]] = step
                self.sched_save()

    def remove_step(self):
        sel = self.steps_list.curselection()
        if sel:
            del self.scheds[self.sel]["steps"][sel[0]]
            self.sched_save()

    def move_step(self, d):
        sel = self.steps_list.curselection()
        steps = self.scheds[self.sel]["steps"]
        if sel and 0 <= sel[0] + d < len(steps):
            i = sel[0]
            steps[i], steps[i + d] = steps[i + d], steps[i]
            self.sched_save()
            self.steps_list.selection_set(i + d)

    def pick_loop_file(self):
        path = filedialog.askopenfilename(parent=self, filetypes=[("Recording", "*.rec"), ("All files", "*.*")])
        if not path:
            return
        try:
            Recorder.read_file(path)
        except (OSError, ValueError, KeyError, IndexError, TypeError) as e:
            messagebox.showerror("Recorder", f"Couldn't load that file: {e}", parent=self)
            return
        self.sched_loop_file = path
        self.sched_save()

    def sched_between_key(self):
        return next((k for k, label in self.SCHED_BETWEEN if label == self.sched_between.get()), "none")

    def sched_mode_key(self):
        return next((k for k, label in AFK_MODES if label == self.sched_mode.get()), "away")

    @staticmethod
    def sched_minutes(sc):
        return sorted({m for m, on in sc["slots"] if on and m is not None})

    def sched_active(self):
        """Schedules that will run: ticked 'use', a ticked minute and a step with a live account."""
        return [sc for sc in self.scheds if sc["on"] and self.sched_minutes(sc)
                and any(st["account"] in self.app.accounts and st["files"] for st in sc["steps"])]

    def sched_chosen(self):
        """Every account the active schedules play on, in the account list's order."""
        names = {st["account"] for sc in self.sched_active() for st in sc["steps"]}
        return [n for n in self.app.accounts if n in names]

    @staticmethod
    def next_at(now, minutes):
        """The first xx:MM:00 strictly after `now` for any of `minutes`."""
        base = datetime.datetime.fromtimestamp(now).replace(second=0, microsecond=0)
        best = None
        for m in minutes:
            t = base.replace(minute=m)
            if t.timestamp() <= now:
                t += datetime.timedelta(hours=1)
            best = t if best is None or t < best else best
        return best.timestamp()

    @staticmethod
    def when_text(minutes):
        return ", ".join(f"xx:{m or 60:02d}" for m in sorted(minutes, key=lambda m: m or 60))

    def sched_save(self):
        self.store_sel()
        self.app.settings["schedule"] = {
            "schedules": [{"name": sc["name"], "on": sc["on"], "slots": sc["slots"], "steps": sc["steps"]}
                          for sc in self.scheds],
            "loop_file": self.sched_loop_file, "between": self.sched_between_key(),
            "mode": self.sched_mode_key()}
        save_settings(self.app.settings)
        self.sched_labels()
        if self.sched["state"] in ("between", "yield"):     # changed while it's on: re-plan
            active = self.sched_active()
            if not active:
                self.sched_off("Nothing left to run - schedules off.")
                return
            now = time.time()
            for sc in active:
                sc["next"] = self.next_at(now, self.sched_minutes(sc))
            self.sched["next"] = min(sc["next"] for sc in active)

    def sched_events(self, path):
        """The recording in a file (re-read only when the file changes)."""
        mtime = os.path.getmtime(path)
        cached = self.sched_cache.get(path)
        if not cached or cached[0] != mtime:
            cached = (mtime, Recorder.read_file(path))
            self.sched_cache[path] = cached
        return cached[1]

    # running ----------------------------------------------------------------
    def sched_toggled(self):
        if self.sched_on.get():
            self.sched_save()
            active = self.sched_active()
            problem = ("Give a schedule a ticked minute and at least one step (Add step...)." if not active else
                       "Choose the recording to loop in between." if (self.sched_between_key() == "loop"
                                                                      and not self.sched_loop_file) else None)
            if problem:
                self.sched_on.set(False)
                self.sched_status.set(problem)
                return
            if self.rec.playing:
                self.rec.stop_play()
            now = time.time()
            for sc in active:                        # each waits for its first ticked minute
                sc["next"] = self.next_at(now, self.sched_minutes(sc))
            self.sched.update(state="between", next=min(sc["next"] for sc in active), note="")
            log_error("Schedules on: " + "; ".join(
                f"{sc['name']} at {self.when_text(self.sched_minutes(sc))} "
                f"({', '.join(st['account'] for st in sc['steps'])})" for sc in active))
            self.app.update_recorder_btn()
        else:
            self.sched_off("Schedules off.")

    def sched_off(self, why):
        if self.sched["state"] in ("main", "between") and self.rec.playing:
            self.rec.stop_play()
        self.sched["state"] = "off"
        self.sched["note"] = ""
        self.sched_on.set(False)
        self.sched_status.set(why)
        if not self.app.recorder_shown:          # hidden and nothing scheduled: let go of F7/F8
            self.rec.stop_hooks()
        self.app.update_recorder_btn()

    def sched_running(self):
        return self.sched["state"] != "off"

    def sched_tick(self):
        if not self.alive:
            return
        try:
            if self.sched_on.get():
                self.sched_step()
        except Exception:
            log_error(traceback.format_exc())
            self.sched_off("Schedule hit a problem (see error.log).")
        self.after(1000, self.sched_tick)

    def sched_step(self):
        s, now = self.sched, time.time()
        gv = self.app.gameview if self.app.game_view_open() else None
        afk_busy = bool(gv and (gv.afk_running or gv.afk_due_any()))
        if s["state"] == "main":                       # the scheduled steps are playing
            if not self.rec.playing and not self.sched_play_next(gv):
                self.sched_after_main(gv)              # every step has had its turn
            return
        if s["state"] in ("between", "yield"):
            left = s["next"] - now
            if left <= 0:
                if self.rec.playing:
                    self.rec.stop_play()                # end the in-between loop first
                    return
                s.update(state="waiting", wait_start=now,
                         due=[sc for sc in self.sched_active() if sc["next"] <= now])
            elif self.sched_between_key() == "loop":
                you_here = self.sched_mode_key() == "away" and self.app.real_idle() < AWAY_IDLE
                if s["state"] == "between" and (afk_busy or you_here) and self.rec.playing:
                    self.rec.stop_play()                # Anti-AFK's turn, or you're using the PC
                    s["state"] = "yield"
                elif not afk_busy and not you_here and not self.rec.playing and not self.rec.recording:
                    self.sched_start_loop(gv)
                    s["state"] = "between"
                s["why"] = "you're using the PC" if you_here else "Anti-AFK's turn"
            if s["state"] != "waiting":
                left = max(0, int(left))
                at = time.strftime("%I:%M %p", time.localtime(s["next"])).lstrip("0")
                names = ", ".join(sc["name"] for sc in self.sched_active() if sc["next"] <= s["next"] + 1)
                self.sched_status.set(f"Next: {names} at {at} (in {left // 60}:{left % 60:02d})"
                                      + (f"  (loop paused: {s.get('why')})" if s["state"] == "yield" else "")
                                      + (f"\n{s['note']}" if s.get("note") else ""))
                return
        # waiting to start the due schedules
        if self.rec.recording:
            self.sched_status.set("Waiting: you're recording")
            return
        if afk_busy and gv and gv.afk_running:
            self.sched_status.set("Waiting for Anti-AFK to finish...")
            return
        if (self.sched_mode_key() == "away" and self.app.real_idle() < AWAY_IDLE
                and now - s["wait_start"] < AWAY_MAX_WAIT):
            self.sched_status.set("Waiting until you're away from the PC...")
            return
        queue = []
        for sc in s.get("due") or []:
            for st in sc["steps"]:
                if st["account"] not in self.app.accounts or not st["files"]:
                    continue
                try:
                    events = join_recordings([self.sched_events(f) for f in st["files"]])
                except (OSError, ValueError, KeyError, IndexError, TypeError) as e:
                    self.sched_off(f"{sc['name']}: couldn't read a recording: {e}")
                    return
                label = ", ".join(os.path.basename(f) for f in st["files"])
                queue.append((st["account"], events, f"{sc['name']}: {label}"))
        s.update(queue=queue, played=[], skipped=[], started=now)
        if not self.sched_play_next(gv):
            for sc in s.get("due") or []:
                sc["next"] = now + 60
            s.update(state="between", next=min(sc["next"] for sc in self.sched_active()),
                     note=f"{', '.join(s['skipped']) or 'nobody'}: no game open in Game View - trying again")
            self.sched_status.set(s["note"])

    def sched_play_next(self, gv):
        """Play the next step whose account has a game open. False when no step is left."""
        s = self.sched
        while s.get("queue"):
            name, events, label = s["queue"].pop(0)
            if gv is None or not gv.bring_account_game(name):
                if name not in s["skipped"]:
                    s["skipped"].append(name)           # no game for it right now
                continue
            if self.rec.play(1, self.sched_speed(), delay=0.8, reset=bool(self.reset_var.get()),
                             reset_wait=self.sched_reset_wait(), back=bool(self.back_var.get()),
                             events=events, zoom=self.zoom_value()):
                s["state"] = "main"
                if name not in s["played"]:
                    s["played"].append(name)
                self.sched_status.set(f"Playing {label} on {name}...")
                return True
        return False

    def sched_after_main(self, gv):
        s, now = self.sched, time.time()
        for sc in s.get("due") or []:
            sc["next"] = self.next_at(now, self.sched_minutes(sc)) if self.sched_minutes(sc) else now + 3600
        active = self.sched_active()
        if not active:
            self.sched_off("Nothing left to run - schedules off.")
            return
        s.update(state="between", next=min(sc["next"] for sc in active), loop_i=0,
                 note=f"Skipped (no game open): {', '.join(s['skipped'])}" if s["skipped"] else "")
        if self.sched_between_key() == "afk" and gv is not None:
            for name in s["played"]:
                gv.set_account_afk(name)
        log_error(f"Schedule: ran {', '.join(sc['name'] for sc in s.get('due') or [])} on "
                  f"{', '.join(s['played']) or 'nobody'}"
                  + (f" (no game open: {', '.join(s['skipped'])})" if s["skipped"] else "") + ".")

    def sched_start_loop(self, gv):
        """In between: play the loop recording once on each scheduled account in turn."""
        try:
            events = self.sched_events(self.sched_loop_file)
        except (OSError, ValueError, KeyError, IndexError, TypeError) as e:
            self.sched_off(f"Couldn't read the loop recording: {e}")
            return
        names = self.sched_chosen()
        start = self.sched.get("loop_i", 0)
        for k in range(len(names)):
            i = (start + k) % len(names)
            if gv is not None and gv.bring_account_game(names[i]):
                self.sched["loop_i"] = i + 1
                self.rec.play(1, self.sched_speed(), delay=0.8, events=events, zoom=self.zoom_value())
                return

    def zoom_value(self):
        """Notches to scroll out after zooming all the way in, or None if the zoom reset is off."""
        if not self.zoom_on.get():
            return None
        try:
            return min(40, max(0, int(self.zoom_out.get())))
        except ValueError:
            return 10

    def save_zoom(self):
        self.app.settings["zoom_reset"] = {"on": bool(self.zoom_on.get()),
                                           "out": self.zoom_value() if self.zoom_on.get() else
                                           (int(self.zoom_out.get()) if self.zoom_out.get().isdigit() else 10)}
        save_settings(self.app.settings)

    def sched_speed(self):
        try:
            return float(self.speed.get().rstrip("x"))
        except ValueError:
            return 1.0

    def sched_reset_wait(self):
        try:
            return max(1.0, float(self.reset_wait.get()))
        except ValueError:
            return 6.0

    # ----- actions -----
    def toggle_record(self, from_button=False):
        rec = self.rec
        if rec.recording:
            rect = None
            if from_button:          # don't record the click on this window's own Stop button
                rect = (self.winfo_rootx(), self.winfo_rooty(),
                        self.winfo_rootx() + self.winfo_width(), self.winfo_rooty() + self.winfo_height())
            count = rec.stop_record(rect)
            self.status.set(f"Recorded {count} actions ({rec.duration():.1f} s). F8 to play.")
        elif rec.playing:
            self.status.set("Stop playback first.")
        elif self.sched["state"] != "off":
            self.status.set("Turn the schedule off first.")
        elif rec.start_record():
            self.status.set("\u25CF Recording...  press F7 to stop")

    def toggle_play(self, from_button=False):
        rec = self.rec
        if rec.playing and self.sched["state"] in ("main", "between"):
            self.sched_off("Schedule stopped (F8). Tick 'On' to start it again.")
            return
        if rec.playing:
            rec.stop_play()
            return
        if self.sched["state"] != "off":
            self.status.set("Turn the schedule off first.")
            return
        if rec.recording:
            self.status.set("Stop recording first.")
            return
        if not rec.events:
            self.status.set("Nothing recorded yet. Press F7 to record.")
            return
        try:
            loops = 0 if self.forever.get() else max(1, int(self.repeat.get()))
            speed = float(self.speed.get().rstrip("x"))
            wait = max(1.0, float(self.reset_wait.get()))
        except ValueError:
            self.status.set("Check the Repeat, Speed and wait values.")
            return
        rec.play(loops, speed, delay=1.0 if from_button else 0.3,
                 reset=bool(self.reset_var.get()), reset_wait=wait, back=bool(self.back_var.get()),
                 zoom=self.zoom_value())

    def save(self):
        if not self.rec.events:
            self.status.set("Nothing to save yet.")
            return
        path = filedialog.asksaveasfilename(parent=self, defaultextension=".rec",
                                            filetypes=[("Recording", "*.rec"), ("All files", "*.*")])
        if path:
            try:
                self.rec.save(path)
                self.status.set("Saved " + os.path.basename(path))
            except OSError as e:
                messagebox.showerror("Recorder", f"Couldn't save: {e}", parent=self)

    def load(self):
        path = filedialog.askopenfilename(parent=self, filetypes=[("Recording", "*.rec"), ("All files", "*.*")])
        if path:
            try:
                count = self.rec.load(path)
                self.status.set(f"Loaded {count} actions ({self.rec.duration():.1f} s). F8 to play.")
            except (OSError, ValueError, KeyError, IndexError, TypeError) as e:
                messagebox.showerror("Recorder", f"Couldn't load that file: {e}", parent=self)

    # ----- housekeeping -----
    def poll(self):
        if not self.alive:
            return
        rec = self.rec
        while True:
            try:
                action = rec.hotkeys.get_nowait()
            except queue.Empty:
                break
            (self.toggle_record if action == "record" else self.toggle_play)()
        if rec.recording:
            self.status.set(f"\u25CF Recording... {len(rec.events)} actions  (F7 to stop)")
        elif rec.playing:
            total = "\u221E" if rec.loop_total == 0 else rec.loop_total
            self.status.set(f"\u25B6 Playing... run {rec.loop_index + 1} of {total}  (F8 to stop)")
        elif self.status.get().startswith(("\u25B6", "\u25CF")):
            self.status.set("Finished." if rec.events else "Idle.")
        self.rec_btn.config(text="\u25A0 Stop (F7)" if rec.recording else "\u25CF Record (F7)")
        self.play_btn.config(text="\u25A0 Stop (F8)" if rec.playing else "\u25B6 Play (F8)")
        self.after(100, self.poll)

    def close(self):
        self.alive = False
        self.rec.recording = False
        self.rec.stop_play()
        self.rec.stop_hooks()
        self.app.recorder_win = None
        self.app.recorder_shown = False
        self.app.recorder_btn.config(text="⏺ Recorder")
        self.destroy()


class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("Multi Roblox Manager")
        scale = self.winfo_fpixels("1i") / 96
        self.geometry(f"{int(460 * scale)}x{int(817 * scale)}")
        self.minsize(int(440 * scale), int(767 * scale))
        self.resizable(True, True)
        self.scale = scale
        self.saved_size = None

        self.sidebar_visible = True
        self.topbar = tk.Frame(self)
        self.topbar.pack(side="top", fill="x")
        self.sidebar_btn = tk.Button(self.topbar, text="\u25C0 Hide accounts", state="disabled",
                                     command=self.toggle_sidebar)
        self.sidebar_btn.pack(side="left", padx=6, pady=4)
        self.recorder_win = None
        self.recorder_shown = False          # the panel can be hidden while its schedule keeps running
        self.recorder_btn = tk.Button(self.topbar, text="\u23FA Recorder", command=self.open_recorder)
        self.recorder_btn.pack(side="left", padx=2, pady=4)
        self.body = tk.Frame(self)
        self.body.pack(side="top", fill="both", expand=True)
        self.left = tk.Frame(self.body)          # accounts panel; Game View docks to its right
        self.left.pack(side="left", fill="y")

        os.makedirs(PROFILES_DIR, exist_ok=True)
        self.accounts = self.load_accounts()
        self.creds = self.load_creds()
        self.mutex = None
        self.browser = find_browser()
        self.gameview = None
        self.embed_browser = tk.BooleanVar(value=True)
        self.settings = load_settings()
        self.dark_mode = tk.BooleanVar(value=bool(self.settings.get("dark_mode", False)))
        self.orig_theme = ttk.Style(self).theme_use()
        self.reconnect_var = tk.BooleanVar(value=False)
        self.reconnect_status = tk.StringVar(value="")
        self.reconnect_state = {}     # account -> live auto-reconnect bookkeeping
        self.reconnect_q = queue.Queue()
        self.lost_q = queue.Queue()        # "lost connection" seen in an account's Roblox log
        self.logwatch_targets = {}         # user id -> account, for the log watcher thread
        self.reconnect_where = {}          # account -> {"place", "private"}: where its game was
        self.clean_q = queue.Queue()
        self.direct_launch = tk.BooleanVar(value=bool(self.settings.get("direct_launch_v5", True)))
        self.auto_update = tk.BooleanVar(value=bool(self.settings.get("auto_update_roblox", True)))
        self.reap_on = bool(self.settings.get("end_leftover_roblox", True))
        self.reap_var = tk.BooleanVar(value=self.reap_on)
        self.launch_info = tk.StringVar(value="")
        self.skip_pairs = set(self.settings.get("skip_update_pairs", []))
        self.update_job = None
        self.warned_versions = set()
        self.clean_running = False
        self.game_owner = None              # which account the text in the Game box belongs to
        self.game_dirty = False             # you edited that text since it was loaded/saved
        self.loading_game = False
        self.game_var = tk.StringVar()
        self.game_label = tk.StringVar(value="Game ID or private link:")
        self.storage_var = tk.StringVar(value="Storage: calculating...")
        self.afk_resume = {}          # account -> anti-AFK minutes to apply to its rejoined game
        self.afk_after_var = tk.BooleanVar(value=bool(self.settings.get("afk_after_reconnect", True)))
        self.pending = []   # (account name, launch time) awaiting a Roblox window
        self.launch_q = queue.Queue()
        self.launch_inflight = 0

        self.status = tk.StringVar()
        tk.Label(self.left, textvariable=self.status, font=("Segoe UI", 11, "bold")).pack(pady=(12, 4))
        self.mutex_btn = tk.Button(self.left, text="Enable Multi-Instance", command=self.toggle_mutex)
        self.mutex_btn.pack()

        tk.Label(self.left, text="Accounts", font=("Segoe UI", 10, "bold")).pack(pady=(14, 2))
        self.listbox = AccountGrid(self.left, ("Segoe UI", 11), on_select=self.on_account_select,
                                   on_double=lambda: self.launch(), color_for=self.account_text_color,
                                   on_move=self.move_account, on_menu=self.account_menu)
        self.listbox.pack(fill="x", padx=16)

        row = tk.Frame(self.left)
        row.pack(pady=8)
        tk.Button(row, text="Add Account", width=12, command=self.add_account).grid(row=0, column=0, padx=3)
        tk.Button(row, text="Log in", width=12, command=self.login).grid(row=0, column=1, padx=3)
        tk.Button(row, text="Remove", width=12, command=self.remove_account).grid(row=0, column=2, padx=3)

        row2 = tk.Frame(self.left)
        row2.pack(pady=2)
        tk.Button(row2, text="Set Password", width=11, command=self.set_credentials).grid(row=0, column=0, padx=2)
        tk.Button(row2, text="Copy User", width=9, command=self.copy_username).grid(row=0, column=1, padx=2)
        tk.Button(row2, text="Copy Pass", width=9, command=self.copy_password).grid(row=0, column=2, padx=2)
        tk.Button(row2, text="Set Cookie", width=10, command=self.set_cookie).grid(row=0, column=3, padx=2)

        gf = tk.Frame(self.left)
        gf.pack(pady=(6, 2))
        tk.Label(gf, textvariable=self.game_label).pack(side="left")
        self.game_id = tk.Entry(gf, width=22, textvariable=self.game_var)
        self.game_id.pack(side="left", padx=6)
        self.set_game_text(self.settings.get("last_game", ""))
        self.game_var.trace_add("write", self.on_game_text_changed)
        self.game_id.bind("<FocusOut>", lambda _e: self.save_game_id(only_if_edited=True))
        self.game_id.bind("<Return>", lambda _e: self.save_game_id())

        tk.Button(self.left, text="Launch Selected Account", width=28, height=2,
                  command=self.launch).pack(pady=(10, 4))
        tk.Label(self.left, textvariable=self.launch_info, fg="#555", font=("Segoe UI", 9),
                 wraplength=int(400 * scale), justify="center").pack()
        self.open_gv_btn = tk.Button(self.left, text="Open Game View", width=28,
                                     command=self.open_game_view)
        self.open_gv_btn.pack(pady=(0, 2))
        # the accounts that had a game open when the app was last closed (snapshot for the button)
        self.reopen_names = [n for n in self.settings.get("last_open", []) if n in self.accounts]
        self.reopen_where = dict(self.settings.get("last_open_where", {}))   # name -> game it was in
        self.reopen_queue = []
        self.place_watcher = RobloxLogWatcher()   # reads which game each open account is in
        self.user_ids = {}                        # account -> Roblox user id (from its cookie)
        self.open_where = {}                      # account -> {"place", "private"} (latest seen)
        self.where_busy = False
        self.reopen_btn = tk.Button(self.left, width=28, command=self.reopen_last)
        if self.reopen_names:
            self.reopen_btn.config(text=self.reopen_text())
            self.reopen_btn.pack(after=self.open_gv_btn, pady=(0, 2))
        tk.Checkbutton(self.left, text="Show browser/games in Game View",
                       variable=self.embed_browser).pack(pady=(0, 2))
        tk.Checkbutton(self.left, text="Start each account's player directly (no launcher, no version switching)",
                       variable=self.direct_launch, command=self.save_direct_launch).pack()
        tk.Checkbutton(self.left, text="Update Roblox automatically (once) when it's out of date",
                       variable=self.auto_update, command=self.save_auto_update).pack()
        tk.Checkbutton(self.left, text="End leftover Roblox processes after a game is closed",
                       variable=self.reap_var, command=self.save_reap).pack()
        tk.Checkbutton(self.left, text="Auto-reconnect if disconnected (this account)",
                       variable=self.reconnect_var, command=self.toggle_reconnect).pack()
        tk.Checkbutton(self.left, text="Turn on Anti-AFK after reconnecting",
                       variable=self.afk_after_var, command=self.save_afk_after).pack()
        tk.Label(self.left, textvariable=self.reconnect_status, fg="#555",
                 font=("Segoe UI", 9)).pack(pady=(0, 8))

        tk.Label(
            self.left, fg="#555", font=("Segoe UI", 9), justify="center",
            text="Saved passwords are encrypted with Windows DPAPI.\n"
                 "Copied passwords are cleared from the clipboard after 30s.\n"
                 "Keep this window open while playing.",
        ).pack()
        row = tk.Frame(self.left)
        row.pack(pady=(8, 6))
        tk.Checkbutton(row, text="Dark mode", variable=self.dark_mode,
                       command=self.toggle_dark).pack(side="left")
        tk.Label(row, textvariable=self.storage_var, fg="#555",
                 font=("Segoe UI", 9)).pack(side="left", padx=(14, 6))
        tk.Button(row, text="Free up space",
                  command=lambda: self.start_cleanup(manual=True)).pack(side="left")

        self.refresh()
        self.update_idletasks()
        self.base_w = max(int(460 * scale), self.left.winfo_reqwidth() + 12)
        self.geometry(f"{self.base_w}x{int(817 * scale)}")
        self.minsize(self.base_w, int(767 * scale))
        self.protocol("WM_DELETE_WINDOW", self.on_close)
        self.apply_theme()
        self.after(150, self.set_titlebar)
        self.after(3000, self.reconnect_tick)
        self.after(10000, self.track_open_accounts)
        self.after(2000, self.recover_orphaned_games)
        self.after(2500, lambda: self.start_cleanup(manual=False))
        threading.Thread(target=self.reap_loop, daemon=True).start()
        threading.Thread(target=self.logwatch_loop, daemon=True).start()
        self.after(1000, self.reconnect_poll)

        if not self.browser:
            messagebox.showerror("No browser found",
                                 "Install Google Chrome, Microsoft Edge, or Brave first.")
        self.after(300, self.try_enable_mutex_silently)

    # ---------- auto-reconnect ----------
    def ensure_state(self, name):
        return self.reconnect_state.setdefault(name, {
            "user_id": None, "launched_at": 0.0, "misses": 0, "checking": False,
            "next_check": 0.0, "paused": False, "armed": False, "last_place": None,
            "attempts": [], "status": "waiting for you to start a game"})

    def state_cookie(self, name):
        st = self.ensure_state(name)
        if "cookie" not in st:
            token = self.creds.get(name, {}).get("cookie")
            try:
                st["cookie"] = decrypt_text(token) if token else None
            except OSError:
                st["cookie"] = None
        return st["cookie"]

    def refresh_reconnect_ui(self):
        name = self.current_account()
        cfg = self.settings.get("reconnect", {}).get(name, {}) if name else {}
        on = bool(cfg.get("on"))
        self.reconnect_var.set(on)
        if on:
            st = self.reconnect_state.get(name)
            self.reconnect_status.set("Auto-reconnect: " + (st["status"] if st else "starting..."))
        else:
            self.reconnect_status.set("")

    def toggle_reconnect(self):
        name = self.selected()
        if not name:
            self.reconnect_var.set(False)
            return
        on = bool(self.reconnect_var.get())
        cfg = self.settings.setdefault("reconnect", {}).setdefault(name, {"on": False, "game": ""})
        if on:
            if self.state_cookie(name) is None:
                messagebox.showinfo("Cookie needed", "Auto-reconnect needs this account's cookie. "
                                                     "Click 'Set Cookie' first.")
                self.reconnect_var.set(False)
                return
            gid = self.game_id.get().strip()
            if gid:
                try:
                    parse_target(gid)
                except RobloxError as e:
                    messagebox.showwarning("Game ID", str(e))
                    self.reconnect_var.set(False)
                    return
                cfg["game"] = gid
            if not cfg.get("game"):
                messagebox.showinfo("Game ID needed", "Type the Game ID to rejoin in the Game ID "
                                                      "box, then tick this again.")
                self.reconnect_var.set(False)
                return
            st = self.ensure_state(name)
            st.update(paused=False, next_check=0.0, misses=0, attempts=[],
                      status="checking...")
        cfg["on"] = on
        save_settings(self.settings)
        self.refresh()
        self.select_account(name)
        self.refresh_reconnect_ui()

    def note_launch(self, name, gid):
        """You launched this account yourself: (re)start watching it."""
        cfg = self.settings.get("reconnect", {}).get(name)
        if not (cfg and cfg.get("on")):
            return
        if gid:
            cfg["game"] = gid
            save_settings(self.settings)
        now = time.time()
        self.ensure_state(name).update(paused=False, armed=True, launched_at=now, misses=0,
                                       attempts=[], last_place=None, next_check=now + 45,
                                       status="joining...")
        self.refresh_reconnect_ui()

    def save_reap(self):
        self.reap_on = bool(self.reap_var.get())
        self.settings["end_leftover_roblox"] = self.reap_on
        save_settings(self.settings)

    def reap_loop(self):
        """Background thread: every few seconds, end Roblox processes whose window has closed,
        and Roblox's background tray process."""
        reaper = ProcessReaper()
        tray_cache = {}            # pid -> is it a '--launch-to-tray' process? (read once per process)
        crash_since = None
        while True:
            time.sleep(3)
            if not self.reap_on:
                reaper.state.clear()
                tray_cache.clear()
                crash_since = None
                continue
            try:
                running = roblox_player_pids()
                with_window = roblox_window_pids() if running else set()
                for pid in [p for p in tray_cache if p not in running]:
                    del tray_cache[pid]
                unknown = [p for p in running if p not in with_window and p not in tray_cache]
                if unknown:
                    for pid, command in roblox_command_lines().items():
                        tray_cache[pid] = "--launch-to-tray" in command.lower()
                    for pid in unknown:
                        tray_cache.setdefault(pid, False)    # couldn't read it: leave it alone
                tray = {p for p, is_tray in tray_cache.items() if is_tray and p in running}
                kills = reaper.step(running, with_window, time.time(), tray)
                for pid in kills:
                    kill_pid(pid)
                    why = "Roblox's background tray process" if pid in tray else "its game window was closed"
                    log_error(f"Ended leftover Roblox process {pid} ({why}).")
                # the crash reporter should vanish with the last player; if it lingers, end it
                if not running and process_running("RobloxCrashHandler.exe"):
                    crash_since = crash_since or time.time()
                    if time.time() - crash_since >= 10:
                        subprocess.run(["taskkill", "/IM", "RobloxCrashHandler.exe", "/F"],
                                       capture_output=True, creationflags=0x08000000)
                        crash_since = None
                else:
                    crash_since = None
            except Exception:
                log_error(traceback.format_exc())

    def save_auto_update(self):
        self.settings["auto_update_roblox"] = bool(self.auto_update.get())
        save_settings(self.settings)

    def save_direct_launch(self):
        self.settings["direct_launch_v5"] = bool(self.direct_launch.get())
        save_settings(self.settings)

    def save_afk_after(self):
        self.settings["afk_after_reconnect"] = bool(self.afk_after_var.get())
        save_settings(self.settings)

    def remember_afk(self, info):
        """Remember an account's Anti-AFK (on/off and interval), so its game gets the same
        Anti-AFK again whenever it's launched, reopened or rejoined."""
        if info["kind"] == "game" and info["account"]:
            self.settings.setdefault("afk_minutes", {})[info["account"]] = info["afk"]["minutes"]
            self.settings.setdefault("afk_on", {})[info["account"]] = bool(info["afk"]["on"])
            save_settings(self.settings)

    def saved_afk(self, name):
        """Minutes to switch Anti-AFK on with for this account's new game, or None if it was off."""
        if name and self.settings.get("afk_on", {}).get(name):
            return self.settings.get("afk_minutes", {}).get(name, 10)
        return None

    def take_afk_resume(self, name):
        """Minutes to enable Anti-AFK with for a freshly rejoined game (once), else None."""
        resume = self.afk_resume.pop(name, None)
        if resume and time.time() - resume["t"] < 600:
            return resume["minutes"]
        return None

    def note_manual_close(self, name):
        st = self.reconnect_state.get(name)
        if st:
            st["paused"] = True
            st["status"] = "paused (you closed it) - launch to resume"
            self.refresh_reconnect_ui()

    def log_reconnect_changes(self):
        """Write each account's auto-reconnect status to error.log when it changes, so a rejoin
        that didn't happen can be traced afterwards."""
        for name, st in self.reconnect_state.items():
            if st.get("logged") != st["status"]:
                st["logged"] = st["status"]
                log_error(f"Auto-reconnect [{name}]: {st['status']}")

    def logwatch_loop(self):
        """Background thread: watch Roblox's logs for a lost connection on accounts with
        auto-reconnect on."""
        watcher = RobloxLogWatcher()
        while True:
            time.sleep(4)
            targets = self.logwatch_targets
            if not targets:
                continue
            try:
                for uid, (when, reason) in watcher.scan(set(targets)).items():
                    self.lost_q.put((targets[uid], when, reason))
                for uid, where in watcher.where(set(targets)).items():
                    self.reconnect_where[targets[uid]] = where     # for rejoining the right game
            except Exception:
                log_error(traceback.format_exc())

    def handle_lost(self, name, when, reason):
        cfg = self.settings.get("reconnect", {}).get(name, {})
        st = self.ensure_state(name)
        st["lost_seen"] = time.time()          # still disconnected (reported every few seconds)
        if (not cfg.get("on") or st["paused"] or not st["armed"]
                or when <= st["launched_at"] or st.get("lost_at") == when):
            return                             # off, or a disconnect from before the last (re)join
        st["lost_at"] = when
        st["status"] = f"lost connection ({reason}) - rejoining in {RECONNECT_LOST_WAIT}s"
        self.log_reconnect_changes()
        self.refresh_reconnect_ui()
        self.after(RECONNECT_LOST_WAIT * 1000, lambda: self.rejoin_if_still_lost(name, when))

    def rejoin_after_crash(self, name):
        """Game View closed this account's frozen game: rejoin now if auto-reconnect is on."""
        cfg = self.settings.get("reconnect", {}).get(name, {})
        st = self.ensure_state(name)
        if cfg.get("on") and not st["paused"] and st["armed"]:
            st["status"] = "game froze and was closed - rejoining"
            self.log_reconnect_changes()
            self.do_reconnect(name)
            self.log_reconnect_changes()
            self.refresh_reconnect_ui()

    def rejoin_if_still_lost(self, name, when):
        """Rejoin unless you reconnected from Roblox's own dialog, or a rejoin already started."""
        st = self.ensure_state(name)
        cfg = self.settings.get("reconnect", {}).get(name, {})
        if (cfg.get("on") and not st["paused"] and st["launched_at"] < when
                and time.time() - st.get("lost_seen", 0) < 10):
            self.do_reconnect(name)
            self.log_reconnect_changes()
            self.refresh_reconnect_ui()

    def reconnect_tick(self):
        now = time.time()
        targets = {}
        for name, cfg in self.settings.get("reconnect", {}).items():
            st = self.reconnect_state.get(name)
            if cfg.get("on") and st and st.get("user_id"):
                targets[str(st["user_id"])] = name
        self.logwatch_targets = targets
        self.log_reconnect_changes()
        for name, cfg in list(self.settings.get("reconnect", {}).items()):
            if not cfg.get("on") or name not in self.accounts:
                continue
            st = self.ensure_state(name)
            if st["checking"] or st["paused"] or now < st["next_check"]:
                continue
            cookie = self.state_cookie(name)
            if not cookie:
                continue
            st["checking"] = True
            st["next_check"] = now + RECONNECT_CHECK_EVERY
            threading.Thread(target=self.presence_worker, args=(name, cookie, st["user_id"]),
                             daemon=True).start()
        self.after(5000, self.reconnect_tick)

    def presence_worker(self, name, cookie, user_id):
        try:
            if not user_id:
                user_id = whoami(cookie)["id"]
            ptype, place = get_presence(cookie, user_id)
            self.reconnect_q.put((name, user_id, ptype, place, None))
        except AuthExpired:
            self.reconnect_q.put((name, user_id, None, None, "auth"))
        except Exception:
            self.reconnect_q.put((name, user_id, None, None, "net"))

    def reconnect_poll(self):
        while True:
            try:
                event = self.reconnect_q.get_nowait()
            except queue.Empty:
                break
            self.handle_presence(*event)
        while True:
            try:
                lost = self.lost_q.get_nowait()
            except queue.Empty:
                break
            self.handle_lost(*lost)
        self.after(1000, self.reconnect_poll)

    def handle_presence(self, name, user_id, ptype, place, err):
        st = self.ensure_state(name)
        st["checking"] = False
        if user_id:
            st["user_id"] = user_id
        if err == "auth":
            st["paused"] = True
            st["status"] = "cookie expired - use Set Cookie"
        elif err:
            st["status"] = "can't reach Roblox (will retry)"
        elif ptype == 2:                      # in a game
            st["armed"] = True
            st["misses"] = 0
            if place:
                st["last_place"] = str(place)
            st["status"] = "in game \u2713"
        elif ptype == 3:                      # in Roblox Studio: leave it alone
            st["misses"] = 0
            st["status"] = "in Studio"
        elif not st["armed"]:
            st["status"] = "waiting for you to start a game"
        elif time.time() - st["launched_at"] < RECONNECT_GRACE:
            st["status"] = "joining..."
        else:
            st["misses"] += 1
            st["status"] = f"not in a game ({st['misses']}/{RECONNECT_MISSES})"
            if st["misses"] >= RECONNECT_MISSES:
                self.do_reconnect(name)
        self.refresh_reconnect_ui()

    def reconnect_target(self, name, game, target):
        """Where to rejoin, from Roblox's own log (same rule as Reopen last session):
        - still inside the private server from its link (also after moving between that game's
          areas): back through the link, so it lands in the same private server;
        - moved on to a different game: that game;
        - nothing known: the link / game ID, or the last game Roblox's presence reported."""
        where = self.reconnect_where.get(name) or self.open_where.get(name) or {}
        place = where.get("place")
        if target and target[0] in ("private", "share"):
            return str(place) if place and not where.get("private") else game
        return str(place) if place else (self.ensure_state(name).get("last_place") or game)

    def do_reconnect(self, name):
        st = self.ensure_state(name)
        now = time.time()
        st["attempts"] = [t for t in st["attempts"] if now - t < 1800]
        if len(st["attempts"]) >= RECONNECT_MAX_TRIES:
            st["paused"] = True
            st["status"] = "too many rejoins - paused (launch to resume)"
            return
        cookie = self.state_cookie(name)
        cfg = self.settings.get("reconnect", {}).get(name, {})
        game = cfg.get("game") or ""
        try:
            target = parse_target(game)
        except RobloxError:
            target = None
        gid = self.reconnect_target(name, game, target)
        if not cookie or not gid:
            return
        st["attempts"].append(now)
        st["misses"] = 0
        st["launched_at"] = now
        st["status"] = ("reconnecting (saved link)..." if gid == game else f"reconnecting (game {gid})...")
        if self.afk_after_var.get():
            minutes = self.settings.get("afk_minutes", {}).get(name, 10)
            if self.gameview is not None and self.gameview.winfo_exists():
                for _h, info in self.gameview.windows_for(name):
                    if info["kind"] == "game":
                        minutes = info["afk"]["minutes"]      # keep the interval you had
            self.afk_resume[name] = {"minutes": minutes, "t": now}
            self.open_game_view()      # Anti-AFK runs inside Game View
        if self.gameview is not None and self.gameview.winfo_exists():
            self.gameview.close_account_games(name)       # clear the dead/disconnected window
        if not self.mutex:
            self.enable_mutex(show_errors=False)
        self.launch_inflight += 1
        threading.Thread(target=self.launch_worker, args=(name, cookie, str(gid), True, bool(self.direct_launch.get()),
                                   tuple(self.skip_pairs),
                                   self.settings.get("account_versions", {}).get(name)),
                         daemon=True).start()
        self.after(200, self.poll_launch)

    def report_callback_exception(self, exc, val, tb):
        log_error("".join(traceback.format_exception(exc, val, tb)))

    # ---------- storage ----------
    def start_cleanup(self, manual=False):
        """Clean browser caches in the background, then update the size shown."""
        if self.clean_running:
            return
        self.clean_running = True
        self.storage_var.set("Storage: cleaning...")

        def work():
            try:
                self.clean_q.put((manual, run_cleanup(), None))
            except Exception as e:
                self.clean_q.put((manual, None, str(e)))

        threading.Thread(target=work, daemon=True).start()
        self.after(300, self.poll_cleanup)

    def poll_cleanup(self):
        try:
            manual, result, err = self.clean_q.get_nowait()
        except queue.Empty:
            self.after(300, self.poll_cleanup)
            return
        self.clean_running = False
        if err or result is None:
            self.storage_var.set("Storage: unknown")
            if manual:
                messagebox.showerror("Free up space", f"Couldn't clean up: {err}")
            return
        before, after, skipped = result
        self.storage_var.set(f"Storage: {human_size(after)}")
        if manual:
            note = (f"\n\n{skipped} account(s) have their browser open, so they were skipped. "
                    "Close those browsers and try again." if skipped else "")
            if before - after < 1024 * 1024:
                note += ("\n\nMost of what's left is your saved browser logins (one profile per "
                         "account). Removing an account deletes its profile.")
            messagebox.showinfo("Free up space",
                                f"Freed {human_size(max(0, before - after))}.\n"
                                f"Multi Roblox now uses {human_size(after)}.{note}")

    # ---------- dark mode ----------
    def toggle_dark(self):
        self.settings["dark_mode"] = bool(self.dark_mode.get())
        save_settings(self.settings)
        self.apply_theme()
        self.set_titlebar()

    def apply_theme(self):
        dark = bool(self.dark_mode.get())
        t = THEMES["dark" if dark else "light"]
        style = ttk.Style(self)
        try:
            if dark:
                style.theme_use("clam")   # the only built-in theme that allows custom colours
                style.configure("TCombobox", fieldbackground=t["field"], background=t["btn"],
                                foreground=t["ffg"], arrowcolor=t["ffg"], bordercolor=t["border"],
                                lightcolor=t["btn"], darkcolor=t["btn"],
                                selectbackground=t["field"], selectforeground=t["ffg"])
                style.map("TCombobox",
                          fieldbackground=[("readonly", t["field"])],
                          foreground=[("readonly", t["ffg"])],
                          selectbackground=[("readonly", t["field"])],
                          selectforeground=[("readonly", t["ffg"])],
                          background=[("active", t["btn_active"])])
                style.configure("TNotebook", background=t["bg"], borderwidth=0)      # Recorder tabs
                style.configure("TNotebook.Tab", background=t["btn"], foreground=t["fg"],
                                bordercolor=t["border"], lightcolor=t["btn"], padding=(8, 2))
                style.map("TNotebook.Tab", background=[("selected", t["sel_bg"]), ("active", t["btn_active"])],
                          foreground=[("selected", t["sel_fg"])])
            else:
                style.theme_use(self.orig_theme)
            # tab strip stays hidden in either theme (layouts are stored per theme)
            style.layout("Tabless.TNotebook.Tab", [])
            style.configure("Tabless.TNotebook", tabmargins=0, borderwidth=0,
                            **({"background": t["bg"]} if dark else {}))
        except tk.TclError:
            pass
        # defaults for widgets created later (e.g. the password / cookie dialogs)
        for pattern, value in {
            "*Background": t["bg"], "*Foreground": t["fg"],
            "*Button.Background": t["btn"], "*Button.activeBackground": t["btn_active"],
            "*Button.activeForeground": t["fg"],
            "*Entry.Background": t["field"], "*Entry.Foreground": t["ffg"],
            "*Entry.insertBackground": t["ffg"],
            "*Listbox.Background": t["field"], "*Listbox.Foreground": t["ffg"],
        }.items():
            self.option_add(pattern, value, 80)
        self._style_tree(self, t)

    def _style_tree(self, w, t):
        cls = w.winfo_class()
        try:
            if cls in ("Tk", "Toplevel"):
                w.configure(bg=t["bg"])
            elif cls == "Frame":
                if str(w.cget("bg")) != "black":      # black frames are the game backdrop
                    w.configure(bg=t["bg"])
                if isinstance(w, GameView):
                    w.configure(highlightbackground=t["border"])
            elif cls == "Label":
                if not hasattr(w, "_muted"):
                    w._muted = str(w.cget("fg")) in ("#555", "#666")
                w.configure(bg=t["bg"], fg=t["muted"] if w._muted else t["fg"])
            elif cls == "Menu":
                w.configure(bg=t["field"], fg=t["ffg"], activebackground=t["sel_bg"],
                            activeforeground=t["sel_fg"], disabledforeground=t["disabled"])
            elif cls in ("Button", "Menubutton"):
                w.configure(bg=t["btn"], fg=t["fg"], activebackground=t["btn_active"],
                            activeforeground=t["fg"], disabledforeground=t["disabled"],
                            relief=t["relief"], borderwidth=t["bd"], highlightbackground=t["bg"])
            elif cls in ("Checkbutton", "Radiobutton"):
                w.configure(bg=t["bg"], fg=t["fg"], activebackground=t["bg"],
                            activeforeground=t["fg"], selectcolor=t["check"],
                            disabledforeground=t["disabled"], highlightbackground=t["bg"])
            elif cls in ("Entry", "Spinbox"):
                cfg = dict(bg=t["field"], fg=t["ffg"], insertbackground=t["ffg"],
                           selectbackground=t["sel_bg"], selectforeground=t["sel_fg"],
                           disabledbackground=t["bg"], disabledforeground=t["disabled"],
                           highlightbackground=t["border"], highlightcolor=t["sel_bg"])
                if cls == "Spinbox":
                    cfg.update(buttonbackground=t["btn"], readonlybackground=t["field"])
                w.configure(**cfg)
            elif cls == "Listbox":
                w.configure(bg=t["field"], fg=t["ffg"], selectbackground=t["sel_bg"],
                            selectforeground=t["sel_fg"], highlightbackground=t["border"],
                            highlightcolor=t["sel_bg"])
            elif cls == "AccountGrid":
                w.set_theme(t)            # colours its own cells (keeps the selection colour)
                return
            elif cls == "TCombobox":
                self._style_combo_popdown(w, t)
        except tk.TclError:
            pass
        for child in w.winfo_children():
            self._style_tree(child, t)

    def _style_combo_popdown(self, combo, t):
        """The dropdown list of a ttk Combobox is a plain Tk listbox; colour it too."""
        try:
            popdown = str(combo.tk.call("ttk::combobox::PopdownWindow", combo))
            combo.tk.call(f"{popdown}.f.l", "configure", "-background", t["field"],
                          "-foreground", t["ffg"], "-selectbackground", t["sel_bg"],
                          "-selectforeground", t["sel_fg"])
        except tk.TclError:
            pass

    def set_titlebar(self):
        """Dark title bar on Windows 10/11 (the window frame isn't a Tk widget)."""
        try:
            self.update_idletasks()
            root = user32.GetAncestor(self.winfo_id(), GA_ROOT)
            value = ctypes.c_int(1 if self.dark_mode.get() else 0)
            dwm = ctypes.windll.dwmapi
            dwm.DwmSetWindowAttribute.argtypes = [wintypes.HWND, wintypes.DWORD,
                                                  ctypes.c_void_p, wintypes.DWORD]
            for attribute in (20, 19):    # 20 = Windows 10 20H1+/11, 19 = older builds
                if dwm.DwmSetWindowAttribute(root, attribute, ctypes.byref(value),
                                             ctypes.sizeof(value)) == 0:
                    break
            user32.SetWindowPos(root, None, 0, 0, 0, 0, SWP_FLAGS_FRAMECHANGE)  # repaint frame
        except Exception:
            pass

    # ---------- data ----------
    def load_accounts(self):
        try:
            with open(DATA_FILE, "r", encoding="utf-8") as f:
                return json.load(f)
        except (OSError, ValueError):
            return []

    def save_accounts(self):
        with open(DATA_FILE, "w", encoding="utf-8") as f:
            json.dump(self.accounts, f, indent=2)

    def load_creds(self):
        try:
            with open(CRED_FILE, "r", encoding="utf-8") as f:
                return json.load(f)
        except (OSError, ValueError):
            return {}

    def save_creds(self):
        with open(CRED_FILE, "w", encoding="utf-8") as f:
            json.dump(self.creds, f, indent=2)

    def refresh(self):
        self.listbox.delete(0, tk.END)
        for name in self.accounts:
            c = self.creds.get(name, {})
            marks = ("   \U0001F511" if "password" in c else "") + ("  \u25B6" if "cookie" in c else "") \
                + ("  \u21BB" if self.settings.get("reconnect", {}).get(name, {}).get("on") else "")
            self.listbox.insert(tk.END, name + marks)
        self.status.set("Multi-instance: " + ("ON" if self.mutex else "OFF"))
        self.mutex_btn.config(text="Disable Multi-Instance" if self.mutex else "Enable Multi-Instance")

    def set_game_text(self, text):
        """Put text in the box without counting it as something you typed."""
        self.loading_game = True
        self.game_var.set(text)
        self.loading_game = False
        self.game_dirty = False

    def on_game_text_changed(self, *_args):
        if not self.loading_game:
            self.game_dirty = True

    def show_game_owner(self):
        name = self.game_owner
        short = name if name is None or len(name) <= 14 else name[:13] + "\u2026"
        self.game_label.set(f"Game / link for {short}:" if name else "Game ID or private link:")

    def save_game_id(self, only_if_edited=False):
        """Save the Game ID / private link to the account the box belongs to (not whichever
        account happens to be selected right now), and as the last one used."""
        name = self.game_owner or self.current_account()
        if not name or name not in self.accounts or (only_if_edited and not self.game_dirty):
            return
        text = self.game_id.get().strip()
        try:
            parse_target(text)         # don't save half-typed or invalid text
        except RobloxError:
            return
        games = self.settings.setdefault("games", {})
        if text:
            games[name] = text
            self.settings["last_game"] = text
        else:
            games.pop(name, None)      # you cleared the box on purpose
        self.game_dirty = False
        save_settings(self.settings)

    def switch_game_owner(self):
        """The selected account changed: keep what you typed for the one you left, then show the
        link saved for the new one (an account with nothing saved keeps the box as it is)."""
        name = self.current_account()
        if name == self.game_owner:
            return
        self.save_game_id(only_if_edited=True)          # saved under the account being left
        self.game_owner = name
        saved = self.settings.get("games", {}).get(name or "")
        if saved:
            self.set_game_text(saved)
        self.show_game_owner()

    def current_account(self):
        """Selected account name, or None (no popup)."""
        sel = self.listbox.curselection()
        return self.accounts[sel[0]] if sel and sel[0] < len(self.accounts) else None

    def select_account(self, name):
        if name in self.accounts:
            idx = self.accounts.index(name)
            self.listbox.selection_clear(0, tk.END)
            self.listbox.selection_set(idx)
            self.listbox.see(idx)
            self.switch_game_owner()

    def on_account_select(self, _event=None):
        """Clicking an account switches Game View to that account's window."""
        self.refresh_reconnect_ui()
        self.switch_game_owner()
        if self.gameview is not None and self.gameview.winfo_exists():
            name = self.current_account()
            if name:
                self.gameview.show_account(name)

    def selected(self):
        sel = self.listbox.curselection()
        if not sel:
            messagebox.showinfo("Select an account", "Pick an account from the list first.")
            return None
        return self.accounts[sel[0]]

    # ---------- accounts ----------
    def add_account(self):
        name = simpledialog.askstring("Add Account", "Name for this account (e.g. Main, Alt1):", parent=self)
        if not name:
            return
        name = name.strip()
        if not name:
            return
        if name in self.accounts or any(safe_name(name) == safe_name(a) for a in self.accounts):
            messagebox.showwarning("Exists", "An account with that name already exists.")
            return
        self.accounts.append(name)
        self.save_accounts()
        self.refresh()
        self.listbox.selection_set(len(self.accounts) - 1)

    def remove_account(self):
        name = self.selected()
        if not name:
            return
        if not messagebox.askyesno(
                "Remove", f"Remove '{name}' and delete its saved browser login?\n"
                          "(Your Roblox account itself is not affected.)"):
            return
        shutil.rmtree(self.profile_path(name), ignore_errors=True)
        self.accounts.remove(name)
        self.creds.pop(name, None)
        self.after(500, lambda: self.start_cleanup(manual=False))
        self.settings.get("reconnect", {}).pop(name, None)
        self.settings.get("games", {}).pop(name, None)
        if self.game_owner == name:
            self.game_owner = None
            self.show_game_owner()
        self.reconnect_state.pop(name, None)
        save_settings(self.settings)
        self.save_accounts()
        self.save_creds()
        self.refresh()

    # ---------- saved credentials ----------
    def set_credentials(self):
        name = self.selected()
        if not name:
            return
        old_user = ""
        if name in self.creds:
            old_user = self.creds[name].get("username", "")
        user = simpledialog.askstring("Username", f"Roblox username for '{name}':",
                                      initialvalue=old_user, parent=self)
        if user is None:
            return
        pw = simpledialog.askstring("Password", f"Roblox password for '{name}':",
                                    show="*", parent=self)
        if not pw:
            return
        try:
            entry = self.creds.setdefault(name, {})
            entry["username"] = user.strip()
            entry["password"] = encrypt_text(pw)
            self.save_creds()
        except OSError as e:
            messagebox.showerror("Error", f"Could not save credentials:\n{e}")
            return
        self.refresh()
        self.listbox.selection_set(self.accounts.index(name))

    def copy_to_clipboard(self, text, clear_after=None):
        self.clipboard_clear()
        self.clipboard_append(text)
        if clear_after:
            def clear():
                try:
                    if self.clipboard_get() == text:
                        self.clipboard_clear()
                except tk.TclError:
                    pass
            self.after(clear_after * 1000, clear)

    def get_creds(self, name, key="password"):
        if key not in self.creds.get(name, {}):
            messagebox.showinfo("No saved login", "Click 'Set Password' first for this account.")
            return None
        return self.creds[name]

    def copy_username(self):
        name = self.selected()
        c = name and self.get_creds(name, "username")
        if c:
            self.copy_to_clipboard(c["username"])

    def copy_password(self):
        name = self.selected()
        c = name and self.get_creds(name)
        if not c:
            return
        try:
            pw = decrypt_text(c["password"])
        except OSError:
            messagebox.showerror("Error", "Could not decrypt. Passwords can only be read by the "
                                          "same Windows user on the same PC that saved them.")
            return
        self.copy_to_clipboard(pw, clear_after=30)

    def profile_path(self, name):
        return os.path.join(PROFILES_DIR, safe_name(name))

    # ---------- browser ----------
    def open_in_profile(self, name, url):
        if not self.browser:
            messagebox.showerror("No browser", "No supported browser found.")
            return
        args = [
            self.browser,
            f"--user-data-dir={self.profile_path(name)}",
            "--no-first-run",
            "--no-default-browser-check",
            "--disk-cache-size=1",                    # keep the profile small:
            "--media-cache-size=1",                   # no big page/media caches,
            "--disable-gpu-shader-disk-cache",
            "--disable-component-update",             # no downloaded components,
            "--disable-background-networking",
            "--disable-breakpad",                     # no crash-report folders,
            "--disable-features=OptimizationGuideModelDownloading,OptimizationHints,"
            "OptimizationHintsFetching,OptimizationTargetPrediction",   # no on-device AI models
            url,
        ]
        if not self.embed_browser.get():
            subprocess.Popen(args)
            return

        self.open_game_view()
        view = self.gameview
        if view.select_browser(name):
            # Same profile is already open in the view: the URL opens as a new tab there.
            subprocess.Popen(args)
            return
        exe = os.path.basename(self.browser).lower()
        snapshot = set(find_browser_windows(exe))
        proc = subprocess.Popen(args)
        view.expect_browser(name, proc.pid, snapshot, exe)

    def login(self):
        name = self.selected()
        if name:
            self.open_in_profile(name, "https://www.roblox.com/login")

    # ---------- cookie (for direct client launch) ----------
    def get_cookie(self, name):
        token = self.creds.get(name, {}).get("cookie")
        if not token:
            return None
        try:
            return decrypt_text(token)
        except OSError:
            messagebox.showerror("Error", "Could not decrypt the saved cookie. It can only be read "
                                          "by the same Windows user on the same PC that saved it.")
            return None

    def set_cookie(self, name=None):
        name = name or self.selected()
        if not name:
            return False
        raw = simpledialog.askstring(
            "Roblox cookie",
            f"Paste the .ROBLOSECURITY cookie value for '{name}'.\n\n"
            "How to get it: log in to this account in a browser, press F12 > Application >\n"
            "Cookies > https://www.roblox.com, and copy the Value of .ROBLOSECURITY.\n\n"
            "It gives full access to the account, so never share it. It's stored\n"
            "encrypted on this PC only.",
            show="*", parent=self)
        if not raw:
            return False
        cookie = clean_cookie(raw)
        try:
            who = check_cookie(cookie)
        except RobloxError as e:
            messagebox.showerror("Cookie check failed", str(e), parent=self)
            return False
        self.creds.setdefault(name, {})["cookie"] = encrypt_text(cookie)
        old_state = self.reconnect_state.get(name)
        if old_state:
            old_state.pop("cookie", None)
            old_state.update(paused=False, user_id=None)
        self.save_creds()
        self.refresh()
        self.listbox.selection_set(self.accounts.index(name))
        messagebox.showinfo("Saved", f"Cookie saved. This account is logged in as '{who}'.", parent=self)
        return True

    # ---------- launching ----------
    def launch(self):
        name = self.selected()
        if not name:
            return
        cookie = self.get_cookie(name)
        if cookie is None:
            answer = messagebox.askyesnocancel(
                "No cookie saved",
                f"'{name}' has no saved cookie, so the game client can't be started directly.\n\n"
                "Yes = save the cookie now\nNo = open the browser instead\nCancel = do nothing")
            if answer is None:
                return
            if answer is False:
                self.open_in_profile(name, self.browser_url())
                self.pending.append((name, time.time()))
                return
            if not self.set_cookie(name):
                return
            cookie = self.get_cookie(name)
            if cookie is None:
                return

        gid = self.game_id.get().strip()
        try:
            parse_target(gid)
        except RobloxError as e:
            messagebox.showwarning("Game ID", str(e))
            return
        self.game_owner = name                 # the box belongs to the account you launch
        self.show_game_owner()
        self.save_game_id()
        if not self.mutex:
            self.enable_mutex()
            if not self.mutex:
                return
        if self.update_job:                    # you launched yourself: the update step is over
            self.update_job = None
            self.launch_info.set("")
        self.note_launch(name, gid)
        self.launch_inflight += 1
        threading.Thread(target=self.launch_worker, args=(name, cookie, gid, False, bool(self.direct_launch.get()),
                                   tuple(self.skip_pairs),
                                   self.settings.get("account_versions", {}).get(name)),
                         daemon=True).start()
        self.after(200, self.poll_launch)

    def browser_url(self):
        gid = self.game_id.get().strip()
        if "roblox.com" in gid:
            return gid if "://" in gid else "https://" + gid
        return f"https://www.roblox.com/games/{gid}" if gid.isdigit() else "https://www.roblox.com/home"

    def launch_worker(self, name, cookie, gid, silent=False, direct=True, skip=(), prefer=None):
        try:
            payload = prepare_launch(cookie, gid, direct, skip, prefer)
            if payload["mode"] == "update":
                payload["retry"] = (cookie, gid)
            self.launch_q.put(("ok", name, payload, silent))
        except RobloxError as e:
            self.launch_q.put(("err", name, str(e), silent))
        except Exception as e:   # never let the thread die silently
            self.launch_q.put(("err", name, f"Unexpected error: {e}", silent))

    def poll_launch(self):
        while True:
            try:
                kind, name, payload, silent = self.launch_q.get_nowait()
            except queue.Empty:
                break
            self.launch_inflight -= 1
            if kind == "ok" and payload["mode"] == "update":
                if silent:        # automatic rejoin: don't pop anything up
                    st = self.reconnect_state.get(name)
                    if st:
                        st["paused"] = True
                        st["status"] = "Roblox needs an update - launch the account once to update it"
                        self.refresh_reconnect_ui()
                else:
                    self.offer_roblox_update(name, payload)
                continue
            if kind == "ok":
                if self.embed_browser.get():
                    self.open_game_view()
                self.pending.append((name, time.time()))
                started = False
                if payload["mode"] == "exe":
                    try:
                        subprocess.Popen(payload["args"], cwd=os.path.dirname(payload["args"][0]))
                        started = True
                    except OSError:
                        pass                      # fall back to Roblox's launcher below
                if not started:
                    try:
                        os.startfile(payload["url"])
                    except OSError:
                        messagebox.showerror("Error", "Couldn't start Roblox. Is it installed?")
                if started or payload["mode"] == "url":
                    how = payload.get("how", "")
                    if not started and payload["mode"] == "exe":
                        how = "used Roblox's launcher (starting the player directly failed)"
                    self.launch_info.set(f"Last launch ({name}): {how}")
                    threading.Thread(target=log_player_command_lines, args=(how,), daemon=True).start()
                    version = payload.get("version")
                    if version and self.settings.get("account_versions", {}).get(name) != version:
                        self.settings.setdefault("account_versions", {})[name] = version
                        save_settings(self.settings)
                if payload.get("note") and not silent and payload["note"] not in self.warned_versions:
                    self.warned_versions.add(payload["note"])        # once per session, not every launch
                    messagebox.showinfo("Roblox version", payload["note"])
            elif silent:   # automatic rejoin failed: show it in the status line, no popups
                st = self.reconnect_state.get(name)
                if st:
                    st["status"] = f"rejoin failed: {payload}"
                    if "expired" in payload:
                        st["paused"] = True
                    self.refresh_reconnect_ui()
            else:
                messagebox.showerror("Launch failed", f"{name}: {payload}")
        if self.launch_inflight > 0:
            self.after(200, self.poll_launch)

    # ---------- updating Roblox ----------
    def remember_skip(self, pair):
        self.skip_pairs.add(pair)
        self.settings["skip_update_pairs"] = sorted(self.skip_pairs)
        save_settings(self.settings)

    def retry_launch(self, name, cookie, gid):
        self.launch_inflight += 1
        threading.Thread(target=self.launch_worker,
                         args=(name, cookie, gid, False, bool(self.direct_launch.get()),
                               tuple(self.skip_pairs),
                                   self.settings.get("account_versions", {}).get(name)), daemon=True).start()
        self.after(200, self.poll_launch)

    def offer_roblox_update(self, name, payload):
        installed, latest, pair = payload["installed"], payload["latest"], payload["pair"]
        cookie, gid = payload["retry"]
        if self.auto_update.get():
            answer = True                           # no question: just do it (once per version)
        else:
            answer = messagebox.askyesnocancel(
                "Roblox needs updating",
                f"Roblox on this PC ({installed}) is older than the current version ({latest}).\n\n"
                "Roblox can't finish updating while this app holds its multi-instance lock, which "
                "is probably why you keep seeing an update screen.\n\n"
                "Yes = update now (this app lets go of the lock, Roblox updates, then your game launches)\n"
                "No = launch the installed version anyway\n"
                "Cancel = do nothing")
        if answer is None:
            self.launch_info.set("Launch cancelled.")
            return
        if answer is False:
            self.remember_skip(pair)
            self.remember_skip(f"latest:{latest}")
            self.retry_launch(name, cookie, gid)
            return
        if roblox_running():
            if self.auto_update.get():
                self.launch_info.set("Roblox is out of date. Close every Roblox window, then launch "
                                     "again and it will update once.")
            else:
                messagebox.showwarning("Close Roblox first",
                                       "Close every Roblox window (check Task Manager for "
                                       "RobloxPlayerBeta.exe), then launch again.")
            return
        self.remember_skip(f"latest:{latest}")      # this version is only ever tried once
        self.update_job = {"name": name, "cookie": cookie, "gid": gid, "latest": latest,
                           "pair": pair, "installed": installed, "t0": time.time(), "done_at": None,
                           "channel": payload.get("channel", "")}
        self.disable_mutex()                       # let Roblox's updater run
        try:
            os.startfile(build_update_url(self.update_job["channel"]))
        except OSError:
            self.update_job = None
            self.enable_mutex(show_errors=False)
            messagebox.showerror("Error", "Couldn't start Roblox's updater. Is Roblox installed?")
            return
        self.launch_info.set("Updating Roblox... please wait")
        self.after(3000, self.poll_roblox_update)

    def poll_roblox_update(self):
        job = self.update_job
        if not job:
            return
        elapsed = int(time.time() - job["t0"])
        if roblox_version_installed(job["latest"]):
            if job["done_at"] is None:
                job["done_at"] = time.time()
            left = 6 - (time.time() - job["done_at"])
            if left <= 0:
                self.finish_roblox_update(True)
                return
            self.launch_info.set(f"Roblox updated. Closing the updater's window in {int(left) + 1}s, "
                                 "then launching...")
        elif elapsed > 240:
            self.finish_roblox_update(False)
            return
        else:
            self.launch_info.set(f"Updating Roblox... {elapsed}s (waiting for {job['latest']})")
        self.after(1000, self.poll_roblox_update)

    def finish_roblox_update(self, success):
        job, self.update_job = self.update_job, None
        self.launch_info.set("Roblox updated. Letting the installer finish...")
        self.after(500, lambda: self.settle_roblox_update(job, success, time.time()))

    def settle_roblox_update(self, job, success, t0):
        """Roblox's installer has to finish what it started: wait for it, close the window it
        opened the way you would (the X button), and only force-close as a last resort."""
        waited = time.time() - t0
        if roblox_installer_running() and waited < 90:
            self.launch_info.set(f"Letting Roblox's installer finish... {int(waited)}s")
            self.after(2000, lambda: self.settle_roblox_update(job, success, t0))
            return
        if roblox_running():
            self.launch_info.set("Closing the Roblox window the updater opened...")
            if "closing" not in job:
                job["closing"] = time.time()
                close_roblox_windows()                      # politely, like clicking the X
            elif time.time() - job["closing"] > 25:
                kill_roblox()                               # last resort
            self.after(1500, lambda: self.settle_roblox_update(job, success, t0))
            return
        self.after(1000, lambda: self.after_roblox_update(job, success))

    def after_roblox_update(self, job, success, tries=0):
        self.enable_mutex(show_errors=False)               # multi-instance back on
        if not self.mutex:
            # something still holds Roblox's lock: ask for it to be closed, and wait if needed
            if tries >= 10:
                kill_roblox()
            self.launch_info.set("Close the Roblox window the updater opened - this app carries on "
                                 "by itself as soon as it's closed.")
            if tries < 120:                                # keep trying for about 3 minutes
                self.after(1500, lambda: self.after_roblox_update(job, success, tries + 1))
                return
            messagebox.showwarning("Multi-instance", "The Roblox window is still open, so multi-instance "
                                                     "couldn't be switched back on. Close all Roblox "
                                                     "windows and restart this app.")
            return
        if success:
            self.launch_info.set("Roblox updated - launching...")
            self.retry_launch(job["name"], job["cookie"], job["gid"])
        elif messagebox.askyesno(
                "Update didn't finish",
                f"Roblox still shows the older version ({job['installed']}, current is {job['latest']}).\n\n"
                "Launch the installed version anyway? (This won't ask again for these versions.)"):
            self.remember_skip(job["pair"])
            self.retry_launch(job["name"], job["cookie"], job["gid"])
        else:
            self.launch_info.set("Update didn't finish.")

    def claim_account_name(self):
        """Label for the next Roblox window that appears (launch order, 3 min max)."""
        now = time.time()
        self.pending = [(n, t) for n, t in self.pending if now - t < 180]
        if self.pending:
            return self.pending.pop(0)[0]
        return None

    def open_game_view(self):
        """Show the Game View panel on the right side of this window."""
        if self.gameview is not None and self.gameview.winfo_exists():
            return
        if self.state() == "normal":
            self.update_idletasks()
            w, h = self.winfo_width(), self.winfo_height()
            x, y = self.winfo_x(), self.winfo_y()
            self.saved_size = (w, h)
            sw, sh = self.winfo_screenwidth(), self.winfo_screenheight()
            new_w = min(w + int(1000 * self.scale), sw - 40)
            new_h = min(max(h, int(817 * self.scale)), sh - 80)
            x = max(0, min(x, sw - new_w))
            y = max(0, min(y, sh - new_h - 40))
            self.geometry(f"{new_w}x{new_h}+{x}+{y}")
        self.gameview = GameView(self, self.body)
        self.gameview.pack(side="left", fill="both", expand=True, padx=(4, 6), pady=6)
        self.sidebar_btn.config(state="normal")
        self.apply_minsize()
        self.gameview.show_for_selected_account()
        self.apply_theme()

    def restore_window_size(self):
        """Shrink back to just the accounts panel after the Game View panel closes."""
        if not self.sidebar_visible:
            self.set_sidebar(True)
        self.sidebar_btn.config(state="disabled")
        self.apply_minsize()
        if self.saved_size and self.state() == "normal":
            w, h = self.saved_size
            self.geometry(f"{w}x{h}")
        self.saved_size = None

    def set_topbar_visible(self, visible):
        """Compact mode keeps the Hide accounts button and only tucks the Recorder away."""
        if visible:
            self.recorder_btn.pack(side="left", padx=2, pady=4)
        else:
            self.recorder_btn.pack_forget()
        self.topbar.pack(side="top", fill="x", before=self.body)

    def open_recorder(self):
        """The Recorder button shows the recorder under the accounts, or hides it again. Hiding
        only tucks it away, so a running schedule keeps going (F8 still stops it)."""
        panel = self.recorder_win
        if panel is not None and panel.winfo_exists() and self.recorder_shown:
            panel.pack_forget()
            self.recorder_shown = False
            if not panel.sched_running():
                panel.rec.stop_hooks()         # nothing scheduled: let go of F7/F8
            self.update_recorder_btn()
            return
        if panel is None or not panel.winfo_exists():
            panel = self.recorder_win = RecorderPanel(self, self.left)
        elif not panel.rec.start_hooks():
            messagebox.showwarning("Recorder", "Couldn't start the keyboard/mouse hooks, so recording "
                                               "and the F7/F8 hotkeys won't work.", parent=self)
        panel.pack(after=self.listbox, fill="x", padx=16, pady=(8, 0))
        self.recorder_shown = True
        self.update_recorder_btn()
        self.apply_theme()
        if not self.sidebar_visible:
            self.set_sidebar(True)
        self.update_idletasks()
        need = self.left.winfo_reqheight() + self.topbar.winfo_height()
        if self.state() == "normal" and self.winfo_height() < need:   # grow so nothing gets cut off
            self.geometry(f"{self.winfo_width()}x{need}")

    def update_recorder_btn(self):
        panel = self.recorder_win
        if self.recorder_shown:
            text = "⏺ Hide Recorder"
        elif panel is not None and panel.alive and panel.sched_running():
            text = "⏺ Recorder (schedule on)"
        else:
            text = "⏺ Recorder"
        self.recorder_btn.config(text=text)

    def recorder_playing(self):
        rw = self.recorder_win
        return bool(rw is not None and rw.alive and rw.rec.playing)

    def real_idle(self):
        """Seconds since you last used the keyboard/mouse. While the Recorder is open its hooks
        tell your input apart from its own playback (Windows counts both)."""
        rw = self.recorder_win
        if rw is not None and rw.alive and rw.rec.hooks_ok:
            return time.time() - rw.rec.last_real
        return idle_seconds()

    def game_view_open(self):
        return self.gameview is not None and bool(self.gameview.winfo_exists())

    def apply_minsize(self):
        if self.game_view_open() and not self.sidebar_visible:
            self.minsize(int(480 * self.scale), int(380 * self.scale))   # game only: can go small
        elif self.game_view_open():
            self.minsize(self.base_w + int(480 * self.scale), int(767 * self.scale))
        else:
            self.minsize(self.base_w, int(767 * self.scale))

    def toggle_sidebar(self):
        if self.game_view_open():
            self.set_sidebar(not self.sidebar_visible)

    def set_sidebar(self, visible):
        """Hide/show the accounts side so the game can use the whole window."""
        self.sidebar_visible = visible
        view = self.gameview if self.game_view_open() else None
        if visible:
            if view is not None:
                self.left.pack(side="left", fill="y", before=view)
            else:
                self.left.pack(side="left", fill="y")
            self.sidebar_btn.config(text="\u25C0 Hide accounts")
        else:
            self.left.pack_forget()
            self.sidebar_btn.config(text="\u25B6 Show accounts")
        self.apply_minsize()
        if visible and self.state() == "normal":      # make room for the accounts again
            self.update_idletasks()
            need = self.base_w + int(480 * self.scale)
            if self.winfo_width() < need:
                self.geometry(f"{need}x{self.winfo_height()}")
        if view is not None:
            self.after(80, view.sync_docks)

    # ---------- multi-instance mutex ----------
    def try_enable_mutex_silently(self):
        self.enable_mutex(show_errors=False)

    def enable_mutex(self, show_errors=True):
        if self.mutex:
            return
        k32 = ctypes.windll.kernel32
        handle = k32.CreateMutexW(None, True, MUTEX_NAME)
        if not handle:
            if show_errors:
                messagebox.showerror("Error", "Could not create the mutex.")
            return
        if k32.GetLastError() == ERROR_ALREADY_EXISTS:
            k32.CloseHandle(handle)
            if show_errors:
                messagebox.showwarning(
                    "Roblox is already running",
                    "Close every Roblox window (check Task Manager for "
                    "RobloxPlayerBeta.exe) and try again.")
            return
        self.mutex = handle
        self.refresh()

    def disable_mutex(self):
        if self.mutex:
            ctypes.windll.kernel32.CloseHandle(self.mutex)
            self.mutex = None
        self.refresh()

    def toggle_mutex(self):
        if self.mutex:
            self.disable_mutex()
        else:
            self.enable_mutex()

    # ---------- account order and colours (drag in the list, right-click menu) ----------
    def pin_account_colors(self):
        """Default colours come from list position; fix each account's current colour before the
        order changes, so moving one account doesn't recolour the others."""
        borders = self.settings.setdefault("borders", {})
        for name in self.accounts:
            if not borders.get(name, {}).get("color"):
                _on, color = account_border(self.settings, self.accounts, name)
                borders.setdefault(name, {})["color"] = color

    def move_account(self, src, dst):
        if not (0 <= src < len(self.accounts) and 0 <= dst < len(self.accounts)) or src == dst:
            return
        self.pin_account_colors()
        name = self.accounts.pop(src)
        self.accounts.insert(dst, name)
        self.save_accounts()
        save_settings(self.settings)
        self.refresh()
        self.select_account(name)
        self.after_colors_changed()

    def swap_accounts(self, a, b):
        """Swap two accounts' places in the list (and so their games' places in the grid)."""
        if a not in self.accounts or b not in self.accounts or a == b:
            return
        self.pin_account_colors()
        i, j = self.accounts.index(a), self.accounts.index(b)
        self.accounts[i], self.accounts[j] = b, a
        self.save_accounts()
        save_settings(self.settings)
        self.refresh()
        self.select_account(a)
        self.after_colors_changed()

    def after_colors_changed(self):
        self.listbox.paint()
        if self.game_view_open():
            self.gameview.sync_docks()

    def account_menu(self, i, event):
        """Right-click an account: its colour (name + game border) and its place in the list."""
        if not 0 <= i < len(self.accounts):
            return
        name = self.accounts[i]
        on, _color = account_border(self.settings, self.accounts, name)
        menu = tk.Menu(self, tearoff=0)
        menu.add_command(label=f"Colour for {name}...", command=lambda: self.pick_account_color(name))
        on_var = tk.BooleanVar(value=on)
        menu.add_checkbutton(label="Use colour (name + game border)", variable=on_var,
                             command=lambda: self.set_account_border(name, on=bool(on_var.get())))
        menu.add_separator()
        last = len(self.accounts) - 1
        menu.add_command(label="Move to top", state="normal" if i > 0 else "disabled",
                         command=lambda: self.move_account(i, 0))
        menu.add_command(label="Move up", state="normal" if i > 0 else "disabled",
                         command=lambda: self.move_account(i, i - 1))
        menu.add_command(label="Move down", state="normal" if i < last else "disabled",
                         command=lambda: self.move_account(i, i + 1))
        menu.add_command(label="Move to bottom", state="normal" if i < last else "disabled",
                         command=lambda: self.move_account(i, last))
        if self.game_view_open():
            gv = self.gameview
            has_game = any(info["kind"] == "game" for _h, info in gv.windows_for(name))
            menu.add_separator()
            menu.add_command(label="Pop out its game (move it anywhere)",
                             state="normal" if has_game else "disabled",
                             command=lambda: [gv.pop_out(h) for h, info in gv.windows_for(name)
                                              if info["kind"] == "game"])
            menu.add_command(label="Put its game back in Game View",
                             state="normal" if gv.popped_for(name) else "disabled",
                             command=lambda: gv.put_back(only=name))
        t = THEMES["dark" if self.dark_mode.get() else "light"]
        try:
            menu.configure(bg=t["field"], fg=t["ffg"], activebackground=t["sel_bg"],
                           activeforeground=t["sel_fg"], disabledforeground=t["disabled"])
        except tk.TclError:
            pass
        try:
            menu.tk_popup(event.x_root, event.y_root)
        finally:
            menu.grab_release()

    def set_account_border(self, name, **changes):
        self.settings.setdefault("borders", {}).setdefault(name, {}).update(changes)
        save_settings(self.settings)
        self.after_colors_changed()

    def pick_account_color(self, name):
        _on, color = account_border(self.settings, self.accounts, name)
        picked = colorchooser.askcolor(color=color, parent=self, title=f"Colour for {name}")[1]
        if picked:
            self.set_account_border(name, color=picked, on=True)

    def recover_orphaned_games(self):
        """At start-up: hidden games left behind by an earlier session -> open Game View, whose
        scan brings them back so you can see (and close) them."""
        try:
            if find_orphaned_games() and not self.game_view_open():
                self.open_game_view()
        except Exception:
            log_error(traceback.format_exc())

    def account_text_color(self, i):
        """An account's name is shown in its border colour (normal colour if its border is off)."""
        if not 0 <= i < len(self.accounts):
            return None
        on, color = account_border(self.settings, self.accounts, self.accounts[i])
        return color if on else None

    # ---------- remembering which accounts were open ----------
    def open_game_accounts(self):
        """Accounts with a game in Game View right now, in account-list order."""
        if not self.game_view_open():
            return None
        names = {i["account"] for h, i in self.gameview.embedded.items()
                 if i["kind"] == "game" and i["account"] and user32.IsWindow(h)}
        return [n for n in self.accounts if n in names]

    def save_open_accounts(self):
        names = self.open_game_accounts()
        if names is None:
            return
        where = {n: self.open_where[n] for n in names if n in self.open_where}
        if names != self.settings.get("last_open") or where != self.settings.get("last_open_where"):
            self.settings["last_open"] = names
            self.settings["last_open_where"] = where
            save_settings(self.settings)

    def track_open_accounts(self):
        """Keep the list current (so it's right even if the app is closed unexpectedly)."""
        try:
            self.save_open_accounts()
            names = self.open_game_accounts()
            if names and not self.where_busy:
                cookies = {n: self.creds.get(n, {}).get("cookie") for n in names}
                known = {n: str(self.reconnect_state.get(n, {}).get("user_id") or self.user_ids.get(n) or "")
                         for n in names}
                self.where_busy = True
                threading.Thread(target=self.where_worker, args=(cookies, known), daemon=True).start()
        except Exception:
            log_error(traceback.format_exc())
        self.after(10000, self.track_open_accounts)

    def where_worker(self, cookies, known):
        """Background: find which game each open account is in, from Roblox's own logs."""
        try:
            for name, token in cookies.items():
                if not known.get(name) and token:
                    try:
                        known[name] = str(whoami(decrypt_text(token))["id"])
                    except Exception:
                        pass                      # no network / bad cookie: try again next time
            ids = {uid: n for n, uid in known.items() if uid}
            for n, uid in known.items():
                if uid:
                    self.user_ids[n] = uid
            self.place_watcher.scan(set(ids))
            for uid, where in self.place_watcher.where(set(ids)).items():
                self.open_where[ids[uid]] = where
        except Exception:
            log_error(traceback.format_exc())
        finally:
            self.where_busy = False

    def reopen_target(self, name):
        """Where to relaunch an account: back into its private server (its saved link) if it was
        still in it, otherwise into the game it was in, otherwise its saved link."""
        saved = self.settings.get("games", {}).get(name, "")
        where = self.reopen_where.get(name) or {}
        if where.get("place") and not (where.get("private") and saved):
            return str(where["place"])
        return saved

    def launch_account(self, name, gid):
        """Launch an account into gid without touching its saved link (used by Reopen)."""
        self.select_account(name)
        self.refresh_reconnect_ui()
        cookie = self.get_cookie(name)
        if cookie is None or not gid:
            self.launch()                         # the normal path (asks about a missing cookie)
            return
        if not self.mutex:
            self.enable_mutex()
            if not self.mutex:
                return
        self.note_launch(name, gid)
        self.launch_inflight += 1
        threading.Thread(target=self.launch_worker, args=(name, cookie, gid, False, bool(self.direct_launch.get()),
                                   tuple(self.skip_pairs),
                                   self.settings.get("account_versions", {}).get(name)),
                         daemon=True).start()
        self.after(200, self.poll_launch)

    def reopen_text(self):
        names = ", ".join(self.reopen_names)
        return (f"↻ Reopen last session ({len(self.reopen_names)})\n"
                + (names if len(names) <= 34 else names[:32] + "..."))

    def reopen_last(self):
        """Launch the accounts that were open last time, one every 10 s (skipping any that
        already have a game open)."""
        already = set(self.open_game_accounts() or [])
        self.reopen_queue = [n for n in self.reopen_names if n in self.accounts and n not in already]
        self.reopen_btn.pack_forget()
        if not self.reopen_queue:
            return
        log_error(f"Reopening last session: {', '.join(self.reopen_queue)}.")
        self.open_game_view()
        self.reopen_next()

    def reopen_next(self):
        if not self.reopen_queue:
            return
        name = self.reopen_queue.pop(0)
        if name in self.accounts:
            target = self.reopen_target(name)
            log_error(f"Reopen: {name} -> {target or '(no game)'}")
            self.launch_account(name, target)
        if self.reopen_queue:
            self.after(10000, self.reopen_next)

    def on_close(self):
        try:
            self.save_open_accounts()                 # remember which accounts were open
        except Exception:
            log_error(traceback.format_exc())
        if self.recorder_win is not None and self.recorder_win.winfo_exists():
            self.recorder_win.close()
        game_pids = set()
        if self.gameview is not None and self.gameview.winfo_exists():
            game_pids = self.gameview.game_pids()       # the games in Game View close with the app
            self.gameview.close()
        for pid in game_pids:
            subprocess.Popen(["taskkill", "/PID", str(pid), "/T", "/F"], creationflags=0x08000000)
        if game_pids:
            log_error(f"App closed: closed {len(game_pids)} Roblox game(s) that were in Game View.")
        self.disable_mutex()
        if self.reap_on:
            start_exit_cleanup()
        self.destroy()


# Runs after the app has closed: when Roblox games close, Roblox starts a hidden background
# "--launch-to-tray" RobloxPlayerBeta process. While the app runs, reap_loop ends it; once the app
# is closed nothing would, so it stayed in Task Manager. This small hidden helper ends those (never
# a real game). It checks every second, quits as soon as it has closed the tray process, and also
# quits if no Roblox is running at all for 10 s in a row (or after 12 hours at most).
EXIT_CLEANUP_PS = r"""
$end = (Get-Date).AddHours(12)
$idle = 0
while ((Get-Date) -lt $end) {
    $players = @(Get-CimInstance Win32_Process -Filter "Name='RobloxPlayerBeta.exe'")
    $tray = @($players | Where-Object { $_.CommandLine -like '*--launch-to-tray*' })
    if ($tray.Count -gt 0) {
        foreach ($p in $tray) { Stop-Process -Id $p.ProcessId -Force -ErrorAction SilentlyContinue }
        for ($i = 0; $i -lt 10; $i++) {        # wait (up to 10 s) until it's really gone
            if (-not (Get-Process -Id ($tray.ProcessId) -ErrorAction SilentlyContinue)) { break }
            Start-Sleep -Seconds 1
        }
        if (-not (Get-Process RobloxPlayerBeta -ErrorAction SilentlyContinue)) {
            Get-Process RobloxCrashHandler -ErrorAction SilentlyContinue | Stop-Process -Force -ErrorAction SilentlyContinue
        }
        break                                  # tray process closed: done
    }
    if ($players.Count -eq 0) { $idle++ } else { $idle = 0 }
    if ($idle -ge 10) {                        # no Roblox at all for 10 s: nothing left to clean up
        Get-Process RobloxCrashHandler -ErrorAction SilentlyContinue | Stop-Process -Force -ErrorAction SilentlyContinue
        break
    }
    Start-Sleep -Seconds 1
}
"""


def start_exit_cleanup():
    try:
        subprocess.Popen(["powershell", "-NoProfile", "-NonInteractive", "-WindowStyle", "Hidden",
                          "-Command", EXIT_CLEANUP_PS],
                         creationflags=0x08000000 | 0x00000008 | 0x00000200,   # no window, detached
                         close_fds=True)
    except OSError:
        pass


if __name__ == "__main__":
    if sys.platform != "win32":
        print("This app only works on Windows.")
        sys.exit(1)
    try:  # make pixel sizes match between this app and embedded Roblox windows
        ctypes.windll.shcore.SetProcessDpiAwareness(1)
    except Exception:
        try:
            ctypes.windll.user32.SetProcessDPIAware()
        except Exception:
            pass
    App().mainloop()
