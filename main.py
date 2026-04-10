import customtkinter as ctk
import tkinter as tk
import requests
import time
import threading
import sys
import os
import winreg
import json
import ctypes
import webbrowser
import socket
import subprocess
import psutil
import datetime
from collections import deque
from urllib.parse import urlparse

from PIL import Image, ImageDraw
import pystray
from pystray import MenuItem as item
from plyer import notification
from languages import LANGS

APP_VERSION = "1.0"
GITHUB_REPO = "jeffbennington/JB-NetTracker"

myappid = 'JB NetTracker'
ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID(myappid)


ctk.set_appearance_mode("dark")
ctk.set_default_color_theme("blue")

APPDATA = os.environ.get('APPDATA', os.path.expanduser('~'))
CONFIG_DIR = os.path.join(APPDATA, 'JB Software', 'JB NetTracker')
CONFIG_FILE = os.path.join(CONFIG_DIR, 'config.json')
LOG_FILE    = os.path.join(CONFIG_DIR, 'logs.txt')

IP_CHECK_SERVERS = {
    "ip-api.com": {
        "url":    "http://ip-api.com/json/?fields=status,country,regionName,query,proxy,hosting",
        "ip":     lambda d: d.get("query"),
        "country":lambda d: d.get("country", ""),
        "region": lambda d: d.get("regionName", ""),
        "vpn":    lambda d: bool(d.get("proxy") or d.get("hosting")),
        "ok":     lambda d: d.get("status") == "success",
        "limit":  "45 req/min",
    },
    "ipwho.is": {
        "url":    "https://ipwho.is/",
        "ip":     lambda d: d.get("ip"),
        "country":lambda d: d.get("country", ""),
        "region": lambda d: d.get("region", ""),
        "vpn":    lambda d: bool((d.get("security") or {}).get("proxy")
                                 or (d.get("security") or {}).get("vpn")
                                 or (d.get("security") or {}).get("hosting")),
        "ok":     lambda d: bool(d.get("ip")),
        "limit":  "60 req/min",
    },
    "freeipapi.com": {
        "url":    "https://freeipapi.com/api/json",
        "ip":     lambda d: d.get("ipAddress"),
        "country":lambda d: d.get("countryName", ""),
        "region": lambda d: d.get("regionName", ""),
        "vpn":    lambda d: bool(d.get("isProxy") or d.get("isVpn")),
        "ok":     lambda d: bool(d.get("ipAddress")),
        "limit":  "60 req/min",
    },
    "ipapi.is": {
        "url":    "https://api.ipapi.is/",
        "ip":     lambda d: d.get("ip"),
        "country":lambda d: (d.get("location") or {}).get("country", ""),
        "region": lambda d: (d.get("location") or {}).get("state", ""),
        "vpn":    lambda d: bool(d.get("is_vpn") or d.get("is_proxy")
                                 or d.get("is_datacenter") or d.get("is_tor")),
        "ok":     lambda d: bool(d.get("ip")),
        "limit":  "1000 req/day",
    },
    "ip.sb": {
        "url":    "https://api.ip.sb/geoip",
        "ip":     lambda d: d.get("ip"),
        "country":lambda d: d.get("country", ""),
        "region": lambda d: d.get("region", ""),
        "vpn":    lambda d: False,
        "ok":     lambda d: bool(d.get("ip")),
        "limit":  "unlimited",
    },
}

SPEED_SERVERS = {
    "Cloudflare (Global)": "https://speed.cloudflare.com/__down?bytes=25000000",
    "Vultr (US/NJ)":       "https://nj-us-ping.vultr.com/vultr.com.100MB.bin",
    "Vultr (EU/AMS)":      "https://ams-nl-ping.vultr.com/vultr.com.100MB.bin",
    "Hetzner (EU/DE)":     "https://speed.hetzner.de/100MB.bin",
    "OVH (EU/FR)":         "https://proof.ovh.net/files/100Mb.dat",
    "Tele2 (EU/SE)":       "http://speedtest.tele2.net/100MB.zip",
    "Yandex (Mirror RU)":  "https://mirror.yandex.ru/ubuntu/ls-lR.gz",
}
UPLOAD_URL = "https://speed.cloudflare.com/__up"

HISTORY_LIMIT = 40
LOG_MAX_LINES = 3000
SYSTEM_LANG_KEY = "System Language"

_LOCALE_TO_LANG = {
    "ru": "Русский (Russian)",
    "en": "English (English)",
    "uk": "Українська (Ukrainian)",
    "zh": "简体中文 (Chinese)",
    "de": "Deutsch (German)",
    "pl": "Polski (Polish)",
    "es": "Español (Spanish)",
    "fr": "Français (French)",
    "pt": "Português (Portuguese)",
    "ja": "日本語 (Japanese)",
    "tr": "Türkçe (Turkish)",
    "sr": "Srpski (Serbian)",
    "kk": "Қазақша (Kazakh)",
    "be": "Беларуская (Belarusian)",
    "cs": "Čeština (Czech)",
    "ko": "한국어 (Korean)",
}


class NetCheckerApp(ctk.CTk):
    def __init__(self):
        super().__init__()
        os.makedirs(CONFIG_DIR, exist_ok=True)
        self.load_settings()

        self.title("JB NetTracker")
        self.geometry("480x800")
        self.configure(fg_color="#1a202c")
        self.resizable(True, True)

        # App icon
        _icon_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "icon.ico")
        if os.path.exists(_icon_path):
            try:
                self.iconbitmap(_icon_path)
            except Exception:
                pass

        self.current_ip = "..."
        self.current_loc = "..."
        self.is_online = True
        self._ip_hidden = False
        self._was_online = None   # None = skip first-run notification
        self._fail_count = 0      # consecutive check failures
        self.sys_speed_history = [0.0] * HISTORY_LIMIT
        self.sys_speed_upload_history = [0.0] * HISTORY_LIMIT
        self.last_ip_check = 0
        self.is_speed_testing = False
        self._speed_cancel = False
        self.is_window_visible = True
        self.icon = None
        self._last_net_io = psutil.net_io_counters()
        self._last_net_time = time.time()
        self._session_recv_total = 0   # accumulated bytes since app start
        self._session_sent_total = 0
        self._session_start_time = time.time()
        self.custom_ping_labels = {}
        self._log_lines = deque(maxlen=LOG_MAX_LINES)
        self._log_paused = False
        # Load logs from previous session
        if os.path.exists(LOG_FILE):
            try:
                with open(LOG_FILE, "r", encoding="utf-8") as _f:
                    for _line in _f:
                        _line = _line.rstrip("\n")
                        if _line:
                            self._log_lines.append(_line)
            except Exception:
                pass
        self._update_asset_url = None   # download URL from GitHub release
        self._update_release_url = None  # browser URL as fallback

        self.setup_ui()
        self.update_ui_texts()
        self.update()
        if self.always_on_top:
            self.wm_attributes('-topmost', True)

        if self.work_in_tray:
            threading.Thread(target=self.init_tray, daemon=True).start()
        else:
            self.update_tray_visibility()

        self.protocol("WM_DELETE_WINDOW", self.on_closing)
        self._append_log(f"Application started — JB NetTracker v{APP_VERSION}")
        self.tick()
        threading.Thread(target=self.check_network, daemon=True).start()
        if self.auto_update_check:
            threading.Thread(target=self._check_for_updates, daemon=True).start()

    # ─── Settings ────────────────────────────────────────────────────────────

    def load_settings(self, reset=False):
        default = {
            "language": SYSTEM_LANG_KEY,
            "ip_freq": 5,
            "ip_server": "ip-api.com",
            "speed_server": "Cloudflare (Global)",
            "work_in_tray": True,
            "notify_ip": False,
            "notify_region": True,
            "notify_connection_loss": False,
            "auto_update_check": True,
            "always_on_top": False,
            "auto_logging": True,
            "custom_dns": [],
            "speed_history": [],
        }
        if not reset and os.path.exists(CONFIG_FILE):
            try:
                with open(CONFIG_FILE, "r", encoding="utf-8") as f:
                    default.update(json.load(f))
            except:
                pass
        self.current_lang = default["language"]
        self.ip_update_seconds = default["ip_freq"]
        self.ip_server_name = default["ip_server"]
        self.speed_server_name = default["speed_server"]
        self.work_in_tray = default["work_in_tray"]
        self.notify_ip_change = default["notify_ip"]
        self.notify_region_change = default["notify_region"]
        self.notify_connection_loss = default["notify_connection_loss"]
        self.auto_update_check = default["auto_update_check"]
        self.always_on_top = default["always_on_top"]
        self.auto_logging = default["auto_logging"]
        self.custom_dns_entries = default["custom_dns"]
        self.speed_history = default["speed_history"]

    def save_settings(self):
        settings = {
            "language": self.current_lang,
            "ip_freq": self.ip_update_seconds,
            "ip_server": self.ip_server_name,
            "speed_server": self.speed_server_name,
            "work_in_tray": self.work_in_tray,
            "notify_ip": self.notify_ip_change,
            "notify_region": self.notify_region_change,
            "notify_connection_loss": self.notify_connection_loss,
            "auto_update_check": self.auto_update_check,
            "always_on_top": self.always_on_top,
            "auto_logging": self.auto_logging,
            "custom_dns": self.custom_dns_entries,
            "speed_history": self.speed_history,
        }
        try:
            os.makedirs(CONFIG_DIR, exist_ok=True)
            with open(CONFIG_FILE, "w", encoding="utf-8") as f:
                json.dump(settings, f, ensure_ascii=False, indent=4)
        except:
            pass

    # ─── Language helpers ─────────────────────────────────────────────────────

    @staticmethod
    def _get_system_lang():
        try:
            buf = ctypes.create_unicode_buffer(85)
            ctypes.windll.kernel32.GetUserDefaultLocaleName(buf, 85)
            prefix = buf.value[:2].lower()
        except Exception:
            prefix = ""
        return _LOCALE_TO_LANG.get(prefix, "English (English)")

    def _resolve_lang(self):
        if self.current_lang == SYSTEM_LANG_KEY:
            return LANGS.get(self._get_system_lang(), LANGS["English (English)"])
        return LANGS.get(self.current_lang, LANGS["English (English)"])

    # ─── Logging ──────────────────────────────────────────────────────────────

    def _append_log(self, text):
        if not getattr(self, "auto_logging", True):
            return
        if self._log_paused:
            return
        now = datetime.datetime.now()
        ts = now.strftime("%d.%m.%Y %H:%M:%S.") + f"{now.microsecond // 1000:03d}"
        self._log_lines.append(f"{ts} {text}")

    # ─── UI Setup ────────────────────────────────────────────────────────────

    def setup_ui(self):
        self.tab_view = ctk.CTkTabview(self, fg_color="transparent")
        self.tab_view.pack(padx=5, pady=5, fill="both", expand=True)
        self.tab_monitor = self.tab_view.add("Monitor")
        self.tab_speed_check = self.tab_view.add("Speed")
        self.tab_settings = self.tab_view.add("Settings")
        self.tab_about = self.tab_view.add("About")

        self.setup_monitor_tab()
        self.setup_speed_tab()
        self.setup_settings_tab()
        self.setup_about_tab()

    def setup_monitor_tab(self):
        ms = ctk.CTkScrollableFrame(self.tab_monitor, fg_color="transparent")
        ms.pack(fill="both", expand=True)

        # Block 1: IP / Location
        self.block1 = ctk.CTkFrame(ms, corner_radius=20, fg_color="#2d3748")
        self.block1.pack(pady=10, padx=15, fill="x")
        ctk.CTkLabel(self.block1, text="JB NETTRACKER", font=("Roboto", 20, "bold"),
                     text_color="#63b3ed").pack(pady=(15, 2))
        self.timer_bar = ctk.CTkProgressBar(self.block1, height=3)
        self.timer_bar.pack(fill="x", padx=60, pady=5)
        ip_row = ctk.CTkFrame(self.block1, fg_color="transparent")
        ip_row.pack()
        # Mirror spacer — same size as copy button, keeps IP text visually centred
        ctk.CTkLabel(ip_row, text="⧉", font=("Roboto", 16),
                     text_color="#2d3748", fg_color="transparent").pack(side="left", padx=(0, 6))
        self.label_ip = ctk.CTkLabel(ip_row, text="...", font=("Roboto", 22, "bold"),
                                     cursor="hand2")
        self.label_ip.pack(side="left")
        self.label_ip.bind("<Button-1>", self._toggle_ip_visibility)
        self._copy_lbl = ctk.CTkLabel(ip_row, text="⧉", font=("Roboto", 16),
                                      text_color="#718096", cursor="hand2")
        self._copy_lbl.pack(side="left", padx=(6, 0))
        self._copy_lbl.bind("<Button-1>", self._copy_ip)
        self._copied_hint = ctk.CTkLabel(self.block1, text="✓ Скопировано",
                                         font=("Roboto", 10), text_color="#68d391")
        self.label_country = ctk.CTkLabel(self.block1, text="...", font=("Roboto", 13))
        self.label_country.pack()
        self.label_vpn = ctk.CTkLabel(self.block1, text="", font=("Roboto", 11, "italic"))
        self.label_vpn.pack(pady=(0, 15))

        # Block 2: Ping latency
        self.block2 = ctk.CTkFrame(ms, corner_radius=20, fg_color="#2d3748")
        self.block2.pack(pady=10, padx=15, fill="x")
        self.dns_title_label = ctk.CTkLabel(self.block2, text="", font=("Roboto", 11, "bold"))
        self.dns_title_label.pack(pady=(5, 0))
        self.dns_timer_bar = ctk.CTkProgressBar(self.block2, height=3, progress_color="#63b3ed")
        self.dns_timer_bar.pack(fill="x", padx=60, pady=5)

        self.ping_labels = {}
        dns_grid = ctk.CTkFrame(self.block2, fg_color="transparent")
        dns_grid.pack(fill="x", padx=15, pady=(0, 8))
        dns_grid.grid_columnconfigure(0, weight=1, uniform="col")
        dns_grid.grid_columnconfigure(1, weight=1, uniform="col")
        self.dns_left = ctk.CTkFrame(dns_grid, fg_color="transparent")
        self.dns_left.grid(row=0, column=0, sticky="new")
        self.dns_right = ctk.CTkFrame(dns_grid, fg_color="transparent")
        self.dns_right.grid(row=0, column=1, sticky="new")
        dns_servers = [("Google", "8.8.8.8"), ("Cloudflare", "1.1.1.1"),
                       ("Yandex", "77.88.8.8"), ("Quad9", "9.9.9.9")]
        for i, (name, ip) in enumerate(dns_servers):
            parent = self.dns_left if i < 2 else self.dns_right
            row = ctk.CTkFrame(parent, fg_color="transparent")
            row.pack(fill="x", padx=8, pady=2)
            ctk.CTkLabel(row, text=name, font=("Roboto", 12)).pack(side="left")
            lbl = ctk.CTkLabel(row, text="-- ms", text_color="#63b3ed", font=("Roboto", 12, "bold"))
            lbl.pack(side="right")
            self.ping_labels[ip] = lbl

        self._rebuild_custom_dns_rows()

        # Block 3: System speed
        self.block3 = ctk.CTkFrame(ms, corner_radius=20, fg_color="#2d3748")
        self.block3.pack(pady=10, padx=15, fill="x")
        self.sys_speed_title_label = ctk.CTkLabel(self.block3, text="", font=("Roboto", 11, "bold"))
        self.sys_speed_title_label.pack(pady=(10, 8))

        speed_row = ctk.CTkFrame(self.block3, fg_color="transparent")
        speed_row.pack(fill="x", padx=20)

        dl_frame = ctk.CTkFrame(speed_row, fg_color="transparent")
        dl_frame.pack(side="left", expand=True)
        self.dl_title_label = ctk.CTkLabel(dl_frame, text="", font=("Roboto", 11),
                                           text_color="#718096")
        self.dl_title_label.pack()
        self.label_download = ctk.CTkLabel(dl_frame, text="0.0", font=("Roboto", 30, "bold"),
                                           text_color="#68d391")
        self.label_download.pack()
        ctk.CTkLabel(dl_frame, text="Mbps", font=("Roboto", 11)).pack(pady=(0, 4))

        ul_frame = ctk.CTkFrame(speed_row, fg_color="transparent")
        ul_frame.pack(side="right", expand=True)
        self.ul_title_label = ctk.CTkLabel(ul_frame, text="", font=("Roboto", 11),
                                           text_color="#718096")
        self.ul_title_label.pack()
        self.label_upload = ctk.CTkLabel(ul_frame, text="0.0", font=("Roboto", 30, "bold"),
                                         text_color="#63b3ed")
        self.label_upload.pack()
        ctk.CTkLabel(ul_frame, text="Mbps", font=("Roboto", 11)).pack(pady=(0, 4))

        self.canvas = ctk.CTkCanvas(self.block3, height=120, bg="#2d3748", highlightthickness=0)
        self.canvas.pack(fill="x", padx=20, pady=(5, 12))

        # Block 4: Session traffic
        self.block4 = ctk.CTkFrame(ms, corner_radius=20, fg_color="#2d3748")
        self.block4.pack(pady=10, padx=15, fill="x")
        self.traffic_title_label = ctk.CTkLabel(self.block4, text="", font=("Roboto", 11, "bold"))
        self.traffic_title_label.pack(pady=(10, 4))

        self.traffic_uptime_label = ctk.CTkLabel(self.block4, text="00:00",
                                                 font=("Roboto", 13, "bold"), text_color="#63b3ed")
        self.traffic_uptime_label.pack(pady=(0, 6))

        traffic_row = ctk.CTkFrame(self.block4, fg_color="transparent")
        traffic_row.pack(fill="x", padx=20, pady=(0, 12))

        recv_frame = ctk.CTkFrame(traffic_row, fg_color="transparent")
        recv_frame.pack(side="left", expand=True)
        self.traffic_recv_title = ctk.CTkLabel(recv_frame, text="", font=("Roboto", 10),
                                               text_color="#718096")
        self.traffic_recv_title.pack()
        self.traffic_recv_label = ctk.CTkLabel(recv_frame, text="0.00 MB",
                                               font=("Roboto", 17, "bold"), text_color="#68d391")
        self.traffic_recv_label.pack()

        sent_frame = ctk.CTkFrame(traffic_row, fg_color="transparent")
        sent_frame.pack(side="left", expand=True)
        self.traffic_sent_title = ctk.CTkLabel(sent_frame, text="", font=("Roboto", 10),
                                               text_color="#718096")
        self.traffic_sent_title.pack()
        self.traffic_sent_label = ctk.CTkLabel(sent_frame, text="0.00 MB",
                                               font=("Roboto", 17, "bold"), text_color="#63b3ed")
        self.traffic_sent_label.pack()

        total_frame = ctk.CTkFrame(traffic_row, fg_color="transparent")
        total_frame.pack(side="right", expand=True)
        self.traffic_total_title = ctk.CTkLabel(total_frame, text="", font=("Roboto", 10),
                                                text_color="#718096")
        self.traffic_total_title.pack()
        self.traffic_total_label = ctk.CTkLabel(total_frame, text="0.00 MB",
                                                font=("Roboto", 17, "bold"), text_color="#f6ad55")
        self.traffic_total_label.pack()

    def setup_speed_tab(self):
        cont = ctk.CTkScrollableFrame(self.tab_speed_check, fg_color="transparent")
        cont.pack(fill="both", expand=True, padx=10, pady=10)

        # Blue title ABOVE the block
        self.lbl_speed_check_title = ctk.CTkLabel(cont, text="",
                                                   font=("Roboto", 16, "bold"),
                                                   text_color="#63b3ed")
        self.lbl_speed_check_title.pack(pady=(8, 2))

        # Main block
        self.speed_block = ctk.CTkFrame(cont, corner_radius=20, fg_color="#2d3748")
        self.speed_block.pack(pady=(4, 10), padx=10, fill="x")

        # Results row: Download | Upload | Latency
        results_row = ctk.CTkFrame(self.speed_block, fg_color="transparent")
        results_row.pack(fill="x", padx=15, pady=(18, 5))

        dl_col = ctk.CTkFrame(results_row, fg_color="transparent")
        dl_col.pack(side="left", expand=True)
        self.lbl_dl_title = ctk.CTkLabel(dl_col, text="", font=("Roboto", 11),
                                         text_color="#718096")
        self.lbl_dl_title.pack()
        self.lbl_dl_result = ctk.CTkLabel(dl_col, text="--", font=("Roboto", 34, "bold"),
                                          text_color="#68d391")
        self.lbl_dl_result.pack()
        ctk.CTkLabel(dl_col, text="Mbps", font=("Roboto", 11)).pack(pady=(0, 4))

        ul_col = ctk.CTkFrame(results_row, fg_color="transparent")
        ul_col.pack(side="left", expand=True)
        self.lbl_ul_title = ctk.CTkLabel(ul_col, text="", font=("Roboto", 11),
                                         text_color="#718096")
        self.lbl_ul_title.pack()
        self.lbl_ul_result = ctk.CTkLabel(ul_col, text="--", font=("Roboto", 34, "bold"),
                                          text_color="#63b3ed")
        self.lbl_ul_result.pack()
        ctk.CTkLabel(ul_col, text="Mbps", font=("Roboto", 11)).pack(pady=(0, 4))

        lat_col = ctk.CTkFrame(results_row, fg_color="transparent")
        lat_col.pack(side="left", expand=True)
        self.lbl_lat_title = ctk.CTkLabel(lat_col, text="", font=("Roboto", 11),
                                          text_color="#718096")
        self.lbl_lat_title.pack()
        self.lbl_lat_result = ctk.CTkLabel(lat_col, text="--", font=("Roboto", 34, "bold"),
                                           text_color="#f6ad55")
        self.lbl_lat_result.pack()
        ctk.CTkLabel(lat_col, text="ms", font=("Roboto", 11)).pack(pady=(0, 4))

        # Progress bar (hidden by default, shown during test)
        self.speed_check_progress = ctk.CTkProgressBar(self.speed_block, height=3,
                                                        progress_color="#10b981")

        # Server selection
        self.lbl_speed_server = ctk.CTkLabel(self.speed_block, text="",
                                              font=("Roboto", 11, "bold"), text_color="#718096")
        self.lbl_speed_server.pack(pady=(10, 0))
        self.speed_server_menu = ctk.CTkOptionMenu(self.speed_block,
                                                   values=list(SPEED_SERVERS.keys()),
                                                   command=self.change_server)
        self.speed_server_menu.pack(pady=(4, 8))

        # Measure button
        self.measure_btn = ctk.CTkButton(self.speed_block, text="", width=180,
                                         fg_color="#38a169", hover_color="#2f855a",
                                         command=self.start_speed_check)
        self.measure_btn.pack(pady=(0, 18))

        # History title (centered)
        self.lbl_speed_history_title = ctk.CTkLabel(cont, text="",
                                                     font=("Roboto", 13, "bold"),
                                                     text_color="#63b3ed")
        self.lbl_speed_history_title.pack(pady=(10, 2))

        # History block
        self.speed_history_block = ctk.CTkFrame(cont, corner_radius=20, fg_color="#2d3748")
        self.speed_history_block.pack(pady=(0, 4), padx=10, fill="x")
        self._update_speed_history_ui()

        # Clear button (centered, below block)
        self.clear_history_btn = ctk.CTkButton(cont, text="", width=120, height=28,
                                               fg_color="#4a5568", hover_color="#718096",
                                               command=self._clear_speed_history)
        self.clear_history_btn.pack(pady=(0, 10))

    def setup_settings_tab(self):
        cont = ctk.CTkScrollableFrame(self.tab_settings, fg_color="transparent")
        cont.pack(fill="both", expand=True, padx=10, pady=10)

        def make_card(parent):
            card = ctk.CTkFrame(parent, corner_radius=15, fg_color="#2d3748")
            card.pack(fill="x", padx=5, pady=4)
            inner = ctk.CTkFrame(card, fg_color="transparent")
            inner.pack(fill="x", padx=15, pady=10)
            return inner

        # Page title
        self.lbl_settings_title = ctk.CTkLabel(cont, text="",
                                                font=("Roboto", 16, "bold"),
                                                text_color="#63b3ed")
        self.lbl_settings_title.pack(pady=(8, 2))

        def make_section_header(parent, attr_name):
            lbl = ctk.CTkLabel(parent, text="", font=("Roboto", 11, "bold"),
                               text_color="#718096", anchor="center")
            lbl.pack(fill="x", padx=8, pady=(10, 2))
            setattr(self, attr_name, lbl)

        # ── General ──────────────────────────────────────────────────────────
        make_section_header(cont, "lbl_section_general")

        lang_inner = make_card(cont)
        self.lbl_lang = ctk.CTkLabel(lang_inner, text="", font=("Roboto", 13))
        self.lbl_lang.pack(side="left")
        self.lang_menu = ctk.CTkOptionMenu(lang_inner,
                                           values=[SYSTEM_LANG_KEY] + list(LANGS.keys()),
                                           command=self.change_lang, width=175)
        self.lang_menu.pack(side="right")

        startup_inner = make_card(cont)
        self.lbl_startup = ctk.CTkLabel(startup_inner, text="", font=("Roboto", 13))
        self.lbl_startup.pack(side="left")
        self.startup_switch = ctk.CTkSwitch(startup_inner, text="", command=self.toggle_startup, width=46)
        self.startup_switch.pack(side="right")

        tray_inner = make_card(cont)
        self.lbl_tray = ctk.CTkLabel(tray_inner, text="", font=("Roboto", 13))
        self.lbl_tray.pack(side="left")
        self.tray_switch = ctk.CTkSwitch(tray_inner, text="", command=self.toggle_tray_setting, width=46)
        self.tray_switch.pack(side="right")

        auto_log_inner = make_card(cont)
        self.lbl_auto_logging = ctk.CTkLabel(auto_log_inner, text="", font=("Roboto", 13))
        self.lbl_auto_logging.pack(side="left")
        self.auto_logging_switch = ctk.CTkSwitch(auto_log_inner, text="",
                                                  command=self.toggle_auto_logging, width=46)
        self.auto_logging_switch.pack(side="right")

        aot_inner = make_card(cont)
        self.lbl_always_on_top = ctk.CTkLabel(aot_inner, text="", font=("Roboto", 13))
        self.lbl_always_on_top.pack(side="left")
        self.always_on_top_switch = ctk.CTkSwitch(aot_inner, text="",
                                                   command=self.toggle_always_on_top, width=46)
        self.always_on_top_switch.pack(side="right")

        update_check_inner = make_card(cont)
        self.lbl_auto_update = ctk.CTkLabel(update_check_inner, text="", font=("Roboto", 13))
        self.lbl_auto_update.pack(side="left")
        self.auto_update_switch = ctk.CTkSwitch(update_check_inner, text="",
                                                command=self.toggle_auto_update_check, width=46)
        self.auto_update_switch.pack(side="right")

        # ── Network Diagnostics ───────────────────────────────────────────────
        make_section_header(cont, "lbl_section_network")

        ip_srv_inner = make_card(cont)
        self.lbl_ip_server = ctk.CTkLabel(ip_srv_inner, text="", font=("Roboto", 13))
        self.lbl_ip_server.pack(side="left")
        self.ip_server_menu = ctk.CTkOptionMenu(
            ip_srv_inner,
            values=list(IP_CHECK_SERVERS.keys()),
            command=self.change_ip_server,
            width=150
        )
        self.ip_server_menu.pack(side="right")

        freq_inner = make_card(cont)
        self.lbl_ip_freq = ctk.CTkLabel(freq_inner, text="", font=("Roboto", 13))
        self.lbl_ip_freq.pack(side="left")
        self.ip_freq_menu = ctk.CTkOptionMenu(freq_inner, values=[], command=self.change_ip_freq, width=120)
        self.ip_freq_menu.pack(side="right")

        dns_inner = make_card(cont)
        self.lbl_custom_dns = ctk.CTkLabel(dns_inner, text="", font=("Roboto", 13))
        self.lbl_custom_dns.pack(side="left")
        self.custom_dns_manage_btn = ctk.CTkButton(dns_inner, text="", width=110,
                                                   fg_color="#2b4a6f", hover_color="#3a6491",
                                                   command=self._open_custom_dns_window)
        self.custom_dns_manage_btn.pack(side="right")

        # ── Notifications ─────────────────────────────────────────────────────
        make_section_header(cont, "lbl_section_notifications")

        notify_inner = make_card(cont)
        self.lbl_notify = ctk.CTkLabel(notify_inner, text="", font=("Roboto", 13))
        self.lbl_notify.pack(side="left")
        self.ip_notify_switch = ctk.CTkSwitch(notify_inner, text="", command=self.toggle_ip_notify, width=46)
        self.ip_notify_switch.pack(side="right")

        region_notify_inner = make_card(cont)
        self.lbl_notify_region = ctk.CTkLabel(region_notify_inner, text="", font=("Roboto", 13))
        self.lbl_notify_region.pack(side="left")
        self.region_notify_switch = ctk.CTkSwitch(region_notify_inner, text="",
                                                   command=self.toggle_region_notify, width=46)
        self.region_notify_switch.pack(side="right")

        conn_loss_inner = make_card(cont)
        self.lbl_notify_conn_loss = ctk.CTkLabel(conn_loss_inner, text="", font=("Roboto", 13))
        self.lbl_notify_conn_loss.pack(side="left")
        self.conn_loss_switch = ctk.CTkSwitch(conn_loss_inner, text="",
                                              command=self.toggle_conn_loss_notify, width=46)
        self.conn_loss_switch.pack(side="right")

        # ── Bottom buttons ────────────────────────────────────────────────────
        logs_card = ctk.CTkFrame(cont, corner_radius=15, fg_color="#2d3748")
        logs_card.pack(fill="x", padx=5, pady=(14, 4))
        self.logs_button = ctk.CTkButton(logs_card, text="", fg_color="#2b4a6f",
                                         hover_color="#3a6491", command=self._open_logs_window)
        self.logs_button.pack(pady=12, padx=15, fill="x")

        reset_card = ctk.CTkFrame(cont, corner_radius=15, fg_color="#2d3748")
        reset_card.pack(fill="x", padx=5, pady=(4, 4))
        self.reset_button = ctk.CTkButton(reset_card, text="", fg_color="#4a5568",
                                          hover_color="#718096", command=self.reset_to_defaults)
        self.reset_button.pack(pady=12, padx=15, fill="x")

    def setup_about_tab(self):
        self.about_cont = ctk.CTkScrollableFrame(self.tab_about, fg_color="transparent")
        self.about_cont.pack(fill="both", expand=True, padx=10, pady=10)

        # Block 1: App name + Version
        self.about_b1 = ctk.CTkFrame(self.about_cont, corner_radius=15, fg_color="#2d3748")
        self.about_b1.pack(pady=10, padx=10, fill="x")
        ctk.CTkLabel(self.about_b1, text="JB NetTracker",
                     font=("Roboto", 24, "bold"), text_color="#63b3ed").pack(pady=(15, 2))
        self.lbl_ver_t = ctk.CTkLabel(self.about_b1, text="", font=("Roboto", 11, "bold"),
                                      text_color="#718096")
        self.lbl_ver_t.pack(pady=(6, 0))
        self.lbl_ver = ctk.CTkLabel(self.about_b1, text="", font=("Roboto", 18, "bold"),
                                    text_color="#63b3ed")
        self.lbl_ver.pack(pady=(0, 6))
        self.lbl_update_status = ctk.CTkLabel(self.about_b1, text="",
                                              font=("Roboto", 12), text_color="#718096", cursor="arrow")
        self.lbl_update_status.pack(pady=(0, 15))
        self.lbl_update_status.bind("<Button-1>", self._on_update_label_click)

        # Block 2: Description
        self.about_b2 = ctk.CTkFrame(self.about_cont, corner_radius=15, fg_color="#2d3748")
        self.about_b2.pack(pady=10, padx=10, fill="x")
        self.lbl_about_t = ctk.CTkLabel(self.about_b2, text="", font=("Roboto", 11, "bold"),
                                        text_color="#718096")
        self.lbl_about_t.pack(pady=(10, 0))
        self.lbl_desc = ctk.CTkLabel(self.about_b2, text="", font=("Roboto", 13),
                                     wraplength=340, justify="left")
        self.lbl_desc.pack(pady=15, padx=20)

        # Block 3: Links
        self.about_b3 = ctk.CTkFrame(self.about_cont, corner_radius=15, fg_color="#2d3748")
        self.about_b3.pack(pady=10, padx=10, fill="x")
        self.lbl_links_t = ctk.CTkLabel(self.about_b3, text="", font=("Roboto", 11, "bold"),
                                        text_color="#718096")
        self.lbl_links_t.pack(pady=(10, 6))

        ctk.CTkButton(
            self.about_b3, text="WEBSITE",
            font=("Roboto", 13, "bold"), fg_color="#6b46c1", hover_color="#553c9a",
            corner_radius=8, height=36,
            command=lambda: webbrowser.open("https://jbsoftware.ru")
        ).pack(fill="x", padx=15, pady=(0, 6))

        ctk.CTkButton(
            self.about_b3, text="GitHub",
            font=("Roboto", 13, "bold"), fg_color="#1a202c", hover_color="#2d3748",
            border_width=1, border_color="#4a5568",
            corner_radius=8, height=36,
            command=lambda: webbrowser.open("https://github.com/jeffbennington/JB-NetTracker")
        ).pack(fill="x", padx=15, pady=(0, 6))

        ctk.CTkButton(
            self.about_b3, text="Telegram",
            font=("Roboto", 13, "bold"), fg_color="#2b6cb0", hover_color="#2c5282",
            corner_radius=8, height=36,
            command=lambda: webbrowser.open("https://t.me/jbprogramms")
        ).pack(fill="x", padx=15, pady=(0, 14))

        # Block 4: Author
        about_b4 = ctk.CTkFrame(self.about_cont, corner_radius=15, fg_color="#2d3748")
        about_b4.pack(pady=10, padx=10, fill="x")
        ctk.CTkLabel(
            about_b4, text="Jeff Bennington",
            font=("Roboto", 15, "bold"), text_color="#e2e8f0"
        ).pack(pady=(14, 2))
        ctk.CTkLabel(
            about_b4, text="From Russia with Love",
            font=("Roboto", 12, "italic"), text_color="#718096"
        ).pack(pady=(0, 14))

    # ─── UI Text Update ───────────────────────────────────────────────────────

    def update_ui_texts(self):
        l = self._resolve_lang()

        tab_map = {
            "Monitor": l["tab_monitor"],
            "Speed": l["tab_speed"],
            "Settings": l["tab_settings"],
            "About": l["tab_about"],
        }
        for key, name in tab_map.items():
            try:
                self.tab_view._segmented_button._buttons_dict[key].configure(text=name)
            except:
                pass

        # Monitor
        self.dns_title_label.configure(text=l["dns_title"])
        self.sys_speed_title_label.configure(text=l["sys_speed_title"])
        self.dl_title_label.configure(text=l["download"])
        self.ul_title_label.configure(text=l["upload"])
        self.traffic_title_label.configure(text=l["traffic_title"])
        self.traffic_recv_title.configure(text=l["traffic_recv"])
        self.traffic_sent_title.configure(text=l["traffic_sent"])
        self.traffic_total_title.configure(text=l["traffic_total"])

        # Speed check tab
        self.lbl_speed_check_title.configure(text=l["speed_check_title"])
        self.lbl_dl_title.configure(text=l["download"])
        self.lbl_ul_title.configure(text=l["upload"])
        self.lbl_lat_title.configure(text=l["latency_label"])
        self.lbl_speed_server.configure(text=l["speed_server_label"])
        self.measure_btn.configure(text=l["measure_btn"])
        self.speed_server_menu.set(self.speed_server_name)

        # Settings — page title + section headers
        self.lbl_settings_title.configure(text=l.get("settings_title", "Settings"))
        self.lbl_section_general.configure(text=l.get("settings_section_general", "General").upper())
        self.lbl_section_network.configure(text=l.get("settings_section_network", "Network Diagnostics").upper())
        self.lbl_section_notifications.configure(text=l.get("settings_section_notifications", "Notifications").upper())

        # Settings
        self.lbl_lang.configure(text=l["lang_label"])
        self.lbl_ip_freq.configure(text=l["ip_freq_label"])
        self.lbl_ip_server.configure(text=l.get("ip_server_label", "IP Check Server"))
        self.ip_server_menu.set(self.ip_server_name)
        self.lbl_startup.configure(text=l["startup_label"])
        self.lbl_tray.configure(text=l["tray_label"])
        self.lbl_notify.configure(text=l["notify_ip"])
        self.lbl_notify_region.configure(text=l.get("notify_region_label", "Notify on region change"))
        self.region_notify_switch.select() if self.notify_region_change else self.region_notify_switch.deselect()
        self.lbl_notify_conn_loss.configure(text=l.get("notify_conn_loss_label", "Notify on connection loss"))
        self.conn_loss_switch.select() if self.notify_connection_loss else self.conn_loss_switch.deselect()
        self.lbl_always_on_top.configure(text=l.get("always_on_top_label", "Always on top"))
        self.always_on_top_switch.select() if self.always_on_top else self.always_on_top_switch.deselect()
        self.lbl_auto_update.configure(text=l.get("update_check_label", "Check for updates on startup"))
        self.auto_update_switch.select() if self.auto_update_check else self.auto_update_switch.deselect()
        self._refresh_update_status_label()
        self.lbl_custom_dns.configure(text=l["custom_dns_label"])
        self.custom_dns_manage_btn.configure(text=l["dns_manage_btn"])
        self.lbl_auto_logging.configure(text=l.get("auto_logging_label", "Auto Logging"))
        self.auto_logging_switch.select() if self.auto_logging else self.auto_logging_switch.deselect()
        self.logs_button.configure(text=l.get("logs_btn", "Logs"))
        self.reset_button.configure(text=l["reset_btn"])

        # Speed history
        self.lbl_speed_history_title.configure(text=l["speed_history_title"])
        self.clear_history_btn.configure(text=l["speed_history_clear"])
        self._update_speed_history_ui()

        opts = [l["f_5s"], l["f_10s"], l["f_30s"], l["f_1m"], l["f_2m"], l["f_5m"], l["f_10m"]]
        self.ip_freq_menu.configure(values=opts)
        m_rev = {5: l["f_5s"], 10: l["f_10s"], 30: l["f_30s"], 60: l["f_1m"],
                 120: l["f_2m"], 300: l["f_5m"], 600: l["f_10m"]}
        self.ip_freq_menu.set(m_rev.get(self.ip_update_seconds, l["f_10s"]))
        self.lang_menu.set(self.current_lang)  # SYSTEM_LANG_KEY shown as-is

        # About
        self.lbl_ver_t.configure(text=l["ver_title"])
        self.lbl_ver.configure(text=APP_VERSION)
        self.lbl_about_t.configure(text=l["about_title"])
        self.lbl_desc.configure(text=l["about_desc"])
        self.lbl_links_t.configure(text=l["links_title"])

        self.tray_switch.select() if self.work_in_tray else self.tray_switch.deselect()
        self.ip_notify_switch.select() if self.notify_ip_change else self.ip_notify_switch.deselect()
        self.check_startup_status()

        if self.icon:
            try:
                self.icon.update_menu()
            except:
                pass

    # ─── Network ─────────────────────────────────────────────────────────────

    def _update_ip_label(self):
        if self._ip_hidden:
            self.label_ip.configure(text="XXX.XXX.XXX.XX")
        else:
            self.label_ip.configure(text=self.current_ip)

    def _toggle_ip_visibility(self, _event=None):
        self._ip_hidden = not self._ip_hidden
        self._update_ip_label()

    def _copy_ip(self, _event=None):
        if self.current_ip not in ("...", "OFFLINE"):
            self.clipboard_clear()
            self.clipboard_append(self.current_ip)
            self._copied_hint.pack(before=self.label_country, pady=(0, 2))
            self.after(1000, self._copied_hint.pack_forget)

    def _retry_ip_check(self):
        """Retry IP check once after startup delay — avoids false OFFLINE on slow init."""
        self.check_network()

    def check_network(self):
        l = self._resolve_lang()
        prev_online = self.is_online
        try:
            srv = IP_CHECK_SERVERS.get(self.ip_server_name,
                                       IP_CHECK_SERVERS["ip-api.com"])
            r = requests.get(srv["url"], timeout=5).json()
            if srv["ok"](r):
                self._fail_count = 0
                new_ip = srv["ip"](r)
                new_region = f"{srv['country'](r)} ({srv['region'](r)})"
                if self.current_ip != "...":
                    if self.current_ip != new_ip and self.notify_ip_change:
                        msg = l.get("notify_ip_msg", "IP address changed. New region: {region}").format(region=new_region)
                        self.send_windows_notification("JB NetTracker", msg)
                    if self.current_loc != new_region and self.notify_region_change:
                        msg = l.get("notify_region_msg", "Region changed: {region}").format(region=new_region)
                        self.send_windows_notification("JB NetTracker", msg)
                self.current_ip = new_ip
                self.current_loc = new_region
                is_vpn = srv["vpn"](r) or self._is_system_proxy_active()
                vpn_status = "Enabled" if is_vpn else "Disabled"
                self._append_log(
                    f"Network Info - ip {new_ip}; location {new_region}; VPN/Proxy status: {vpn_status}"
                )
                loc_text = f"{l['location']}: {self.current_loc}"
                vpn_text = l["vpn_on"] if is_vpn else l["vpn_off"]
                vpn_color = "#f6e05e" if is_vpn else "#718096"
                self.after(0, self._update_ip_label)
                self.after(0, lambda t=loc_text: self.label_country.configure(text=t))
                self.after(0, lambda t=vpn_text, c=vpn_color: self.label_vpn.configure(
                    text=t, text_color=c))
                self.is_online = True
        except:
            self._fail_count += 1
            # Startup: no IP yet — retry once after 3s
            if self.current_ip == "...":
                self.after(3000, self._retry_ip_check)
                return
            # 1st or 2nd failure — recheck in 2s before declaring offline
            if self._fail_count < 3:
                self.after(2000, lambda: threading.Thread(
                    target=self.check_network, daemon=True).start())
                return
            # 3rd consecutive failure — definitely offline
            self.after(0, lambda: self.label_ip.configure(text="OFFLINE"))
            self.is_online = False

        if self.notify_connection_loss and self._was_online is not None:
            if prev_online and not self.is_online:
                self.send_windows_notification(
                    "JB NetTracker", l.get("notify_conn_lost_msg", "Connection lost"))
            elif not prev_online and self.is_online:
                self.send_windows_notification(
                    "JB NetTracker", l.get("notify_conn_restored_msg", "Connection restored"))
        self._was_online = self.is_online

        _ip_name = {"8.8.8.8": "Google", "1.1.1.1": "Cloudflare",
                    "77.88.8.8": "Yandex", "9.9.9.9": "Quad9"}

        # Compute default ping results in background thread
        _default_results = []
        for ip, lbl in list(self.ping_labels.items()):
            if not self.is_online:
                text = "--"
            else:
                v = self._tcp_ping(ip, ports=(53,))
                text = f"{int(v)} ms" if v is not None else "Err"
            _default_results.append((lbl, text, _ip_name.get(ip, ip)))

        # Compute custom ping results in background thread (snapshot to avoid race)
        # Uses ICMP ping (system ping.exe) — works for any IP regardless of open TCP ports
        _custom_snapshot = list(self.custom_ping_labels.items())
        _custom_results = []
        for host, lbl in _custom_snapshot:
            name = next((e["name"] for e in self.custom_dns_entries if e["host"] == host), host)
            if not self.is_online:
                text = "--"
            else:
                v = self._icmp_ping(host)
                text = f"{int(v)} ms" if v is not None else "Err"
            _custom_results.append((lbl, text, name))

        # Schedule UI updates on main thread
        def _apply_ping_ui():
            _ping_log = []
            for lbl, text, name in _default_results:
                try:
                    lbl.configure(text=text)
                except Exception:
                    pass
                _ping_log.append(f"{name} {text.replace(' ', '')}")
            for lbl, text, name in _custom_results:
                try:
                    lbl.configure(text=text)
                except Exception:
                    pass
                _ping_log.append(f"{name} {text.replace(' ', '')}")
            if _ping_log:
                self._append_log("Ping Latency Check - " + "; ".join(_ping_log))

        self.after(0, _apply_ping_ui)

        self.update_tray_tooltip()

    @staticmethod
    def _is_system_proxy_active():
        """Check Windows registry: returns True if system proxy (HTTP/SOCKS) is enabled."""
        try:
            key = winreg.OpenKey(
                winreg.HKEY_CURRENT_USER,
                r'Software\Microsoft\Windows\CurrentVersion\Internet Settings'
            )
            val, _ = winreg.QueryValueEx(key, 'ProxyEnable')
            winreg.CloseKey(key)
            return bool(val)
        except Exception:
            return False

    @staticmethod
    def _icmp_ping(host, timeout_ms=1500):
        """ICMP ping via Windows ping.exe. Works regardless of open TCP ports."""
        import re
        try:
            out = subprocess.run(
                ["ping", "-n", "1", "-w", str(timeout_ms), host],
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                timeout=(timeout_ms / 1000) + 3,
                creationflags=0x08000000  # CREATE_NO_WINDOW
            )
            # Decode as cp866 (Russian Windows OEM) with fallback — digits are always ASCII
            try:
                stdout = out.stdout.decode('cp866')
            except Exception:
                stdout = out.stdout.decode('latin-1')
            # Match "time=28ms", "время=28мс", "zeit=28ms", "time<1ms"
            m = re.search(r'(?:time|время|zeit|tempo|tid)[<=](\d+)', stdout, re.IGNORECASE)
            if m:
                return float(m.group(1))
            # Fallback: find =NUMBER just before TTL (works for any locale)
            m = re.search(r'[<=](\d+)\D{0,5}TTL', stdout, re.IGNORECASE)
            if m:
                val = float(m.group(1))
                if 0 < val < 9999:
                    return val
        except Exception:
            pass
        return None

    @staticmethod
    def _tcp_ping(host, ports=(53, 80, 443), timeout=1.0):
        """TCP connect latency in ms. Tries ports in order, returns None on all failures."""
        for port in ports:
            try:
                s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
                s.settimeout(timeout)
                t = time.perf_counter()
                s.connect((host, port))
                ms = (time.perf_counter() - t) * 1000
                s.close()
                return ms
            except Exception:
                continue
        return None

    @staticmethod
    def _format_traffic(b):
        if b < 1024 * 1024:
            return f"{b / 1024:.1f} KB"
        elif b < 1024 ** 3:
            return f"{b / (1024 ** 2):.2f} MB"
        return f"{b / (1024 ** 3):.2f} GB"

    def update_system_speed(self):
        try:
            net_io = psutil.net_io_counters()
            now = time.time()
            elapsed = now - self._last_net_time
            if elapsed > 0:
                d_recv = net_io.bytes_recv - self._last_net_io.bytes_recv
                d_sent = net_io.bytes_sent - self._last_net_io.bytes_sent
                # Skip negative deltas (adapter reset / network change)
                if d_recv >= 0 and d_sent >= 0:
                    recv_speed = d_recv * 8 / 1_000_000 / elapsed
                    sent_speed = d_sent * 8 / 1_000_000 / elapsed
                    self._session_recv_total += d_recv
                    self._session_sent_total += d_sent
                else:
                    recv_speed = 0.0
                    sent_speed = 0.0
                self.label_download.configure(text=f"{recv_speed:.1f}")
                self.label_upload.configure(text=f"{sent_speed:.1f}")
                self.sys_speed_history.pop(0)
                self.sys_speed_history.append(recv_speed)
                self.sys_speed_upload_history.pop(0)
                self.sys_speed_upload_history.append(sent_speed)
                self.draw_speed_graph()
            self._last_net_io = net_io
            self._last_net_time = now

            self.traffic_recv_label.configure(text=self._format_traffic(self._session_recv_total))
            self.traffic_sent_label.configure(text=self._format_traffic(self._session_sent_total))
            self.traffic_total_label.configure(text=self._format_traffic(
                self._session_recv_total + self._session_sent_total))

            uptime = int(time.time() - self._session_start_time)
            h, rem = divmod(uptime, 3600)
            m, s = divmod(rem, 60)
            uptime_str = f"{h:02d}:{m:02d}:{s:02d}" if h else f"{m:02d}:{s:02d}"
            self.traffic_uptime_label.configure(text=uptime_str)
        except:
            pass

    def run_speed_check(self):
        l = self._resolve_lang()
        result = {"dl": "--", "ul": "--", "lat": "--", "server": self.speed_server_name.split(" ")[0]}

        def reset_btn():
            self.measure_btn.configure(text=l["measure_btn"], fg_color="#38a169",
                                       hover_color="#2f855a", command=self.start_speed_check,
                                       state="normal")

        # Reset results and switch button to Cancel
        self.after(0, lambda: self.lbl_dl_result.configure(text="..."))
        self.after(0, lambda: self.lbl_ul_result.configure(text="..."))
        self.after(0, lambda: self.lbl_lat_result.configure(text="..."))
        self.after(0, lambda: self.measure_btn.configure(
            text=l["cancel_btn"], fg_color="#e53e3e", hover_color="#c53030",
            command=self.cancel_speed_check, state="normal"))
        self.after(0, lambda: self.speed_check_progress.pack(fill="x", padx=60, pady=5,
                                                              before=self.lbl_speed_server))
        self.after(0, self.speed_check_progress.start)

        # 1. Latency — TCP connect to the selected server (reliable without admin rights)
        if not self._speed_cancel:
            try:
                server_url = SPEED_SERVERS.get(self.speed_server_name,
                                               SPEED_SERVERS["Cloudflare (Global)"])
                lat_host = urlparse(server_url).hostname
                lat_port = 443 if server_url.startswith("https") else 80
                lat_values = []
                for _ in range(5):
                    if self._speed_cancel:
                        break
                    try:
                        s = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
                        s.settimeout(3)
                        t = time.perf_counter()
                        s.connect((lat_host, lat_port))
                        lat_values.append((time.perf_counter() - t) * 1000)
                        s.close()
                    except Exception:
                        pass
                if lat_values and not self._speed_cancel:
                    avg_lat = round(sum(lat_values) / len(lat_values), 1)
                    result["lat"] = str(avg_lat)
                    self.after(0, lambda v=avg_lat: self.lbl_lat_result.configure(text=str(v)))
                elif not self._speed_cancel:
                    self.after(0, lambda: self.lbl_lat_result.configure(text="Err"))
            except:
                if not self._speed_cancel:
                    self.after(0, lambda: self.lbl_lat_result.configure(text="Err"))

        # 2. Download — stream from selected server, start timer after first byte
        if not self._speed_cancel:
            try:
                dl_url = SPEED_SERVERS.get(self.speed_server_name,
                                           SPEED_SERVERS["Cloudflare (Global)"])
                r = requests.get(dl_url, stream=True, timeout=30,
                                 headers={"Cache-Control": "no-cache"})
                start = None
                size = 0
                for chunk in r.iter_content(65536):
                    if self._speed_cancel:
                        r.close()
                        break
                    if chunk:
                        if start is None:
                            start = time.perf_counter()
                        size += len(chunk)
                    if size >= 20 * 1024 * 1024:
                        break
                if start and size and not self._speed_cancel:
                    elapsed = time.perf_counter() - start
                    dl_mbps = round((size * 8) / (elapsed * 1_000_000), 1)
                    result["dl"] = str(dl_mbps)
                    self.after(0, lambda v=dl_mbps: self.lbl_dl_result.configure(text=str(v)))
                elif not self._speed_cancel:
                    self.after(0, lambda: self.lbl_dl_result.configure(text="Err"))
            except:
                if not self._speed_cancel:
                    self.after(0, lambda: self.lbl_dl_result.configure(text="Err"))

        # 3. Upload — POST 10 MB; chunk pre-generated once to avoid os.urandom delay
        if not self._speed_cancel:
            try:
                chunk = os.urandom(65536)          # 64 KB random, generated once
                total_chunks = 160                  # 160 × 64 KB = 10 MB
                ul_start = [None]                   # mutable container for nonlocal-like access

                def _upload_gen():
                    for _ in range(total_chunks):
                        if self._speed_cancel:
                            return
                        if ul_start[0] is None:
                            ul_start[0] = time.perf_counter()
                        yield chunk

                requests.post(UPLOAD_URL, data=_upload_gen(), timeout=30,
                              headers={"Content-Type": "application/octet-stream"})
                if not self._speed_cancel and ul_start[0] is not None:
                    elapsed_ul = time.perf_counter() - ul_start[0]
                    ul_bytes = total_chunks * len(chunk)
                    ul_mbps = round((ul_bytes * 8) / (elapsed_ul * 1_000_000), 1)
                    result["ul"] = str(ul_mbps)
                    self.after(0, lambda v=ul_mbps: self.lbl_ul_result.configure(text=str(v)))
            except:
                if not self._speed_cancel:
                    self.after(0, lambda: self.lbl_ul_result.configure(text="Err"))

        # Save to history if at least download was measured
        if not self._speed_cancel and result["dl"] != "--":
            result["date"] = datetime.datetime.now().strftime("%d.%m %H:%M")
            self.speed_history.insert(0, result)
            if len(self.speed_history) > 10:
                self.speed_history = self.speed_history[:10]
            self.save_settings()
            self.after(0, self._update_speed_history_ui)
            self._append_log(
                f"Internet Speed Test - Speed Test Server: {self.speed_server_name}; "
                f"Result - DL {result['dl']}; UL {result['ul']}; MS - {result['lat']}"
            )

        # Cleanup
        self.is_speed_testing = False
        self._speed_cancel = False
        self.after(0, self.speed_check_progress.stop)
        self.after(0, self.speed_check_progress.pack_forget)
        self.after(0, reset_btn)

    def start_speed_check(self):
        if not self.is_speed_testing and self.is_online:
            self._speed_cancel = False
            self.is_speed_testing = True
            threading.Thread(target=self.run_speed_check, daemon=True).start()

    def cancel_speed_check(self):
        self._speed_cancel = True
        l = self._resolve_lang()
        self.measure_btn.configure(state="disabled", text=l["cancel_btn"])

    def tick(self):
        now = time.time()
        elapsed_ip = now - self.last_ip_check
        progress = 1 - min(elapsed_ip / self.ip_update_seconds, 1)
        self.timer_bar.set(progress)
        self.dns_timer_bar.set(progress)
        if elapsed_ip >= self.ip_update_seconds:
            threading.Thread(target=self.check_network, daemon=True).start()
            self.last_ip_check = now
        self.update_system_speed()
        self.after(1000, self.tick)

    def draw_speed_graph(self):
        self.canvas.delete("all")
        w = self.canvas.winfo_width() or 420
        h = 120
        PAD_L, PAD_R, PAD_T, PAD_B = 40, 8, 8, 16
        plot_w = w - PAD_L - PAD_R
        plot_h = h - PAD_T - PAD_B

        max_v = max(max(self.sys_speed_history), max(self.sys_speed_upload_history), 0.1)
        for s in (0.5, 1, 2, 5, 10, 20, 50, 100, 200, 500, 1000):
            if s >= max_v:
                max_scale = s
                break
        else:
            max_scale = max_v * 1.2

        # Horizontal grid lines + Y labels
        for gi in range(5):
            ratio = gi / 4
            y = PAD_T + plot_h - ratio * plot_h
            dash = (3, 4) if gi > 0 else ()
            color = "#3a4f62" if gi > 0 else "#4a5568"
            self.canvas.create_line(PAD_L, y, w - PAD_R, y,
                                    fill=color, width=1, dash=dash)
            val = max_scale * ratio
            lbl = f"{val:.0f}" if val >= 1 else f"{val:.1f}"
            self.canvas.create_text(PAD_L - 4, y, text=lbl, anchor="e",
                                    fill="#718096", font=("Consolas", 8))

        # Y-axis vertical line
        self.canvas.create_line(PAD_L, PAD_T, PAD_L, h - PAD_B,
                                fill="#4a5568", width=1)

        # Plot both lines
        def plot_line(history, color):
            n = len(history)
            if n < 2:
                return
            pts = []
            for i, val in enumerate(history):
                x = PAD_L + (i / (n - 1)) * plot_w
                y = PAD_T + plot_h - (min(val, max_scale) / max_scale) * plot_h
                pts.append((x, y))
            for i in range(len(pts) - 1):
                self.canvas.create_line(
                    pts[i][0], pts[i][1], pts[i+1][0], pts[i+1][1],
                    fill=color, width=2, smooth=True)

        plot_line(self.sys_speed_history, "#68d391")
        plot_line(self.sys_speed_upload_history, "#63b3ed")

        # Legend (top-right)
        self.canvas.create_text(w - PAD_R, PAD_T + 2,
                                text="↓ DL", anchor="ne",
                                fill="#68d391", font=("Roboto", 8, "bold"))
        self.canvas.create_text(w - PAD_R, PAD_T + 13,
                                text="↑ UL", anchor="ne",
                                fill="#63b3ed", font=("Roboto", 8, "bold"))

        # Bottom label
        self.canvas.create_text(PAD_L + plot_w // 2, h - 3,
                                text=f"← {HISTORY_LIMIT}s", anchor="center",
                                fill="#4a5568", font=("Consolas", 8))

    # ─── Custom Ping Targets ─────────────────────────────────────────────────

    def _rebuild_custom_dns_rows(self):
        # Remove previously added custom rows (anything beyond the 2 default rows per column)
        for frame in (self.dns_left, self.dns_right):
            for child in list(frame.winfo_children())[2:]:
                child.destroy()
        self.custom_ping_labels = {}
        if not self.custom_dns_entries:
            return
        for i, entry in enumerate(self.custom_dns_entries):
            parent = self.dns_left if i % 2 == 0 else self.dns_right
            row = ctk.CTkFrame(parent, fg_color="transparent")
            row.pack(fill="x", padx=8, pady=2)
            ctk.CTkLabel(row, text=entry["name"], font=("Roboto", 12),
                         anchor="w").pack(side="left")
            lbl = ctk.CTkLabel(row, text="-- ms", text_color="#f6ad55", font=("Roboto", 12, "bold"))
            lbl.pack(side="right")
            self.custom_ping_labels[entry["host"]] = lbl

    def _open_custom_dns_window(self):
        if hasattr(self, '_dns_window') and self._dns_window is not None:
            try:
                self._dns_window.focus_force()
                return
            except Exception:
                pass
        l = self._resolve_lang()
        win = ctk.CTkToplevel(self)
        win.title(l["dns_window_title"])
        win.geometry("390x300")
        win.resizable(False, False)
        win.configure(fg_color="#1a202c")
        self._dns_window = win

        def on_close():
            self._dns_window = None
            try:
                win.grab_release()
                win.destroy()
            except Exception:
                pass
        win.protocol("WM_DELETE_WINDOW", on_close)

        win.attributes('-topmost', True)
        win.update()
        win.grab_set()
        win.after(300, lambda: win.attributes('-topmost', False) if win.winfo_exists() else None)

        # Input block
        input_block = ctk.CTkFrame(win, corner_radius=15, fg_color="#2d3748")
        input_block.pack(fill="x", padx=15, pady=(15, 8))
        input_row = ctk.CTkFrame(input_block, fg_color="transparent")
        input_row.pack(fill="x", padx=10, pady=10)
        name_var = tk.StringVar()
        host_var = tk.StringVar()

        def _make_limiter(var, limit):
            def _cb(*_):
                v = var.get()
                if len(v) > limit:
                    var.set(v[:limit])
            return _cb

        name_var.trace_add("write", _make_limiter(name_var, 10))
        host_var.trace_add("write", _make_limiter(host_var, 50))

        name_entry = ctk.CTkEntry(input_row, placeholder_text=l["dns_name_ph"], width=100,
                                  textvariable=name_var)
        name_entry.pack(side="left", padx=(0, 5))
        host_entry = ctk.CTkEntry(input_row, placeholder_text=l["dns_host_ph"], width=160,
                                  textvariable=host_var)
        host_entry.pack(side="left", padx=(0, 5))

        def do_add():
            name = name_entry.get().strip()
            host = host_entry.get().strip()
            if not name or not host:
                return
            self.custom_dns_entries.append({"name": name, "host": host})
            name_entry.delete(0, "end")
            host_entry.delete(0, "end")
            self.save_settings()
            refresh_list()
            self._rebuild_custom_dns_rows()

        ctk.CTkButton(input_row, text=l["dns_add_btn"], width=70,
                      fg_color="#38a169", hover_color="#2f855a",
                      command=do_add).pack(side="left")

        # List block
        list_block = ctk.CTkFrame(win, corner_radius=15, fg_color="#2d3748")
        list_block.pack(fill="both", expand=True, padx=15, pady=(0, 15))
        list_inner = ctk.CTkScrollableFrame(list_block, fg_color="transparent", height=140)
        list_inner.pack(fill="both", expand=True, padx=5, pady=5)

        def do_remove(idx):
            if 0 <= idx < len(self.custom_dns_entries):
                self.custom_dns_entries.pop(idx)
            self.save_settings()
            refresh_list()
            self._rebuild_custom_dns_rows()

        def refresh_list():
            for w in list_inner.winfo_children():
                w.destroy()
            if not self.custom_dns_entries:
                ctk.CTkLabel(list_inner, text="—", font=("Roboto", 12),
                             text_color="#718096").pack(pady=15)
                return
            for i, entry in enumerate(self.custom_dns_entries):
                row = ctk.CTkFrame(list_inner, fg_color="transparent")
                row.pack(fill="x", pady=3)
                ctk.CTkLabel(row, text=f"{entry['name']}  ({entry['host']})",
                             font=("Roboto", 12)).pack(side="left")
                ctk.CTkButton(row, text="✕", width=32, height=24,
                              fg_color="#e53e3e", hover_color="#c53030",
                              command=lambda idx=i: do_remove(idx)).pack(side="right")

        refresh_list()

    def _clear_speed_history(self):
        self.speed_history = []
        self.save_settings()
        self._update_speed_history_ui()

    # ─── Speed History ────────────────────────────────────────────────────────

    def _update_speed_history_ui(self):
        l = self._resolve_lang()
        for w in self.speed_history_block.winfo_children():
            w.destroy()
        if not self.speed_history:
            ctk.CTkLabel(self.speed_history_block, text=l["speed_history_empty"],
                         font=("Roboto", 11), text_color="#718096").pack(pady=15)
            return
        header = ctk.CTkFrame(self.speed_history_block, fg_color="transparent")
        header.pack(fill="x", padx=12, pady=(10, 2))
        ctk.CTkLabel(header, text=l["speed_hist_date"], font=("Roboto", 10),
                     text_color="#718096", width=78, anchor="w").pack(side="left")
        ctk.CTkLabel(header, text=l["speed_hist_server"], font=("Roboto", 10),
                     text_color="#718096", width=75, anchor="center").pack(side="left")
        ctk.CTkLabel(header, text="DL", font=("Roboto", 10),
                     text_color="#68d391", width=55, anchor="center").pack(side="left")
        ctk.CTkLabel(header, text="UL", font=("Roboto", 10),
                     text_color="#63b3ed", width=55, anchor="center").pack(side="left")
        ctk.CTkLabel(header, text="ms", font=("Roboto", 10),
                     text_color="#f6ad55", width=48, anchor="center").pack(side="left")
        for entry in self.speed_history:
            row = ctk.CTkFrame(self.speed_history_block, fg_color="transparent")
            row.pack(fill="x", padx=12, pady=1)
            ctk.CTkLabel(row, text=entry.get("date", ""), font=("Roboto", 10),
                         width=78, anchor="w").pack(side="left")
            ctk.CTkLabel(row, text=entry.get("server", "--"), font=("Roboto", 10),
                         text_color="#718096", width=75, anchor="center").pack(side="left")
            ctk.CTkLabel(row, text=entry.get("dl", "--"), font=("Roboto", 10, "bold"),
                         text_color="#68d391", width=55, anchor="center").pack(side="left")
            ctk.CTkLabel(row, text=entry.get("ul", "--"), font=("Roboto", 10, "bold"),
                         text_color="#63b3ed", width=55, anchor="center").pack(side="left")
            ctk.CTkLabel(row, text=entry.get("lat", "--"), font=("Roboto", 10, "bold"),
                         text_color="#f6ad55", width=48, anchor="center").pack(side="left")
        ctk.CTkFrame(self.speed_history_block, fg_color="transparent", height=6).pack()

    # ─── Logs Window ─────────────────────────────────────────────────────────

    def _open_logs_window(self):
        if hasattr(self, '_logs_window') and self._logs_window is not None:
            try:
                self._logs_window.focus_force()
                return
            except Exception:
                pass

        l = self._resolve_lang()
        win = ctk.CTkToplevel(self)
        win.title(l.get("logs_window_title", "Logs"))
        win.geometry("820x540")
        win.configure(fg_color="#1a202c")
        self._logs_window = win

        try:
            _icon_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "icon.ico")
            if os.path.exists(_icon_path):
                win.after(200, lambda: win.iconbitmap(_icon_path))
        except Exception:
            pass

        def on_close():
            self._logs_window = None
            try:
                win.destroy()
            except Exception:
                pass
        win.protocol("WM_DELETE_WINDOW", on_close)

        # Content area
        content_frame = ctk.CTkFrame(win, fg_color="transparent")
        content_frame.pack(fill="both", expand=True, padx=12, pady=(12, 6))

        textbox = ctk.CTkTextbox(content_frame, font=("Consolas", 13), wrap="none",
                                 fg_color="#1e2a38", text_color="#cbd5e0")

        disabled_label = ctk.CTkLabel(
            content_frame,
            text=l.get("logging_disabled_msg",
                       'Logging is disabled.\nActivate "Auto Logging" in Settings to enable it.'),
            font=("Roboto", 16, "bold"), text_color="#718096",
            justify="center", wraplength=600
        )

        def _do_update():
            """Write current log content into textbox and scroll to bottom."""
            content = "\n".join(self._log_lines)
            textbox.configure(state="normal")
            textbox.delete("1.0", "end")
            textbox.insert("1.0", content)
            textbox.configure(state="disabled")
            textbox.see("end")
            # Reset horizontal scroll to left so long lines don't drift the view right
            try:
                textbox._textbox.xview_moveto(0)
            except Exception:
                pass

        def _refresh():
            if not win.winfo_exists():
                return
            if not self.auto_logging:
                textbox.pack_forget()
                disabled_label.pack(fill="both", expand=True)
            else:
                disabled_label.pack_forget()
                textbox.pack(fill="both", expand=True)
                if not self._log_paused:
                    _do_update()
            win.after(2000, _refresh)

        _refresh()

        # Button row
        btn_row = ctk.CTkFrame(win, fg_color="transparent")
        btn_row.pack(padx=12, pady=(0, 12), fill="x")

        def toggle_pause():
            self._log_paused = not self._log_paused
            if self._log_paused:
                pause_btn.configure(text=l.get("logs_resume_btn", "Resume"))
            else:
                pause_btn.configure(text=l.get("logs_pause_btn", "Pause"))
                if win.winfo_exists() and self.auto_logging:
                    _do_update()

        pause_btn = ctk.CTkButton(btn_row, text=l.get("logs_pause_btn", "Pause"),
                                  fg_color="#2b4a6f", hover_color="#3a6491",
                                  width=100, command=toggle_pause)
        pause_btn.pack(side="left", padx=(0, 8))

        def save_logs():
            from tkinter import filedialog
            ts = datetime.datetime.now().strftime("%Y%m%d_%H%M%S")
            path = filedialog.asksaveasfilename(
                parent=win,
                defaultextension=".txt",
                filetypes=[("Text files", "*.txt"), ("All files", "*.*")],
                initialfile=f"JBNetTracker_logs_{ts}.txt"
            )
            if path:
                try:
                    with open(path, "w", encoding="utf-8") as f:
                        f.write("\n".join(self._log_lines))
                except Exception:
                    pass

        ctk.CTkButton(btn_row, text=l.get("logs_save_btn", "Save to file"),
                      fg_color="#2b4a6f", hover_color="#3a6491",
                      width=160, command=save_logs).pack(side="left", padx=(0, 8))
        ctk.CTkButton(btn_row, text=l.get("cancel_btn", "Close"),
                      fg_color="#4a5568", hover_color="#718096",
                      width=100, command=on_close).pack(side="left")

        # Right-click context menu on textbox
        def _copy_selection():
            try:
                selected = textbox._textbox.selection_get()
                win.clipboard_clear()
                win.clipboard_append(selected)
            except tk.TclError:
                # Nothing selected — copy the line under cursor
                try:
                    idx = textbox._textbox.index("current")
                    row = idx.split(".")[0]
                    line_text = textbox._textbox.get(f"{row}.0", f"{row}.end")
                    win.clipboard_clear()
                    win.clipboard_append(line_text)
                except Exception:
                    pass

        def _show_context_menu(event):
            try:
                menu = tk.Menu(win, tearoff=0, bg="#2d3748", fg="#cbd5e0",
                               activebackground="#3a6491", activeforeground="#ffffff",
                               borderwidth=0, relief="flat")
                menu.add_command(label=l.get("ctx_copy", "Copy"), command=_copy_selection)
                menu.tk_popup(event.x_root, event.y_root)
            finally:
                menu.grab_release()

        textbox._textbox.bind("<Button-3>", _show_context_menu)

    # ─── Settings handlers ───────────────────────────────────────────────────

    def change_lang(self, choice):
        old = self.current_lang
        self.current_lang = choice
        self._append_log(f"Settings have been changed - Language: {old} -> {choice}")
        self.update_ui_texts()
        self.save_settings()

    def change_ip_server(self, choice):
        old = self.ip_server_name
        self.ip_server_name = choice
        self._append_log(f"Settings have been changed - IP Check Server: {old} -> {choice}")
        self.save_settings()

    def change_server(self, choice):
        old = self.speed_server_name
        self.speed_server_name = choice
        self._append_log(f"Settings have been changed - Speed Test Server: {old} -> {choice}")
        self.save_settings()

    def toggle_ip_notify(self):
        old = self.notify_ip_change
        self.notify_ip_change = bool(self.ip_notify_switch.get())
        self._append_log(f"Settings have been changed - Notify on IP change: {'On' if old else 'Off'} -> {'On' if self.notify_ip_change else 'Off'}")
        self.save_settings()

    def toggle_region_notify(self):
        old = self.notify_region_change
        self.notify_region_change = bool(self.region_notify_switch.get())
        self._append_log(f"Settings have been changed - Notify on region change: {'On' if old else 'Off'} -> {'On' if self.notify_region_change else 'Off'}")
        self.save_settings()

    def toggle_always_on_top(self):
        old = self.always_on_top
        self.always_on_top = bool(self.always_on_top_switch.get())
        self.wm_attributes('-topmost', self.always_on_top)
        self._append_log(f"Settings have been changed - Always on top: {'On' if old else 'Off'} -> {'On' if self.always_on_top else 'Off'}")
        self.save_settings()

    def toggle_conn_loss_notify(self):
        old = self.notify_connection_loss
        self.notify_connection_loss = bool(self.conn_loss_switch.get())
        self._append_log(f"Settings have been changed - Notify on connection loss: {'On' if old else 'Off'} -> {'On' if self.notify_connection_loss else 'Off'}")
        self.save_settings()

    def toggle_auto_logging(self):
        old = self.auto_logging
        self.auto_logging = bool(self.auto_logging_switch.get())
        if self.auto_logging and not old:
            self._append_log("Auto Logging enabled")
        self.save_settings()

    def toggle_auto_update_check(self):
        old = self.auto_update_check
        self.auto_update_check = bool(self.auto_update_switch.get())
        self._append_log(f"Settings have been changed - Check for updates on startup: {'On' if old else 'Off'} -> {'On' if self.auto_update_check else 'Off'}")
        self.save_settings()
        self._refresh_update_status_label()

    # ─── Update Check ─────────────────────────────────────────────────────────

    @staticmethod
    def _version_newer(remote: str, local: str) -> bool:
        """Return True if remote version is strictly newer than local."""
        try:
            r = tuple(int(x) for x in remote.strip().split("."))
            l = tuple(int(x) for x in local.strip().split("."))
            return r > l
        except Exception:
            return False

    def _refresh_update_status_label(self):
        """Redraw the update status label based on current state."""
        l = self._resolve_lang()
        status = getattr(self, "_update_status", None)
        if not self.auto_update_check and status != "available":
            # Show manual check button text
            self.lbl_update_status.configure(
                text=l.get("update_manual_btn", "Check for updates"),
                text_color="#63b3ed", cursor="hand2"
            )
        elif status == "checking":
            self.lbl_update_status.configure(
                text=l.get("update_checking", "Checking for updates..."),
                text_color="#718096", cursor="arrow"
            )
        elif status == "uptodate":
            self.lbl_update_status.configure(
                text=l.get("update_uptodate", "You are using the latest version"),
                text_color="#68d391", cursor="arrow"
            )
        elif status == "available":
            ver = getattr(self, "_update_latest_ver", "")
            txt = l.get("update_available", "Update {ver} available! Install?").format(ver=ver)
            self.lbl_update_status.configure(
                text=txt, text_color="#f6ad55", cursor="hand2"
            )
        elif status == "error":
            self.lbl_update_status.configure(
                text=l.get("update_error", "Failed to check for updates"),
                text_color="#fc8181", cursor="arrow"
            )
        else:
            self.lbl_update_status.configure(text="", cursor="arrow")

    def _set_update_status(self, status: str):
        self._update_status = status
        self._refresh_update_status_label()
        if status == "available":
            self._show_update_popup()

    def _show_update_popup(self):
        """Popup window notifying about available update."""
        l = self._resolve_lang()
        ver = getattr(self, "_update_latest_ver", "")
        win = ctk.CTkToplevel(self)
        win.title(l.get("update_popup_title", "Update available"))
        win.geometry("380x180")
        win.resizable(False, False)
        win.configure(fg_color="#1a202c")
        win.grab_set()
        win.lift()
        win.focus_force()
        try:
            _icon_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "icon.ico")
            if os.path.exists(_icon_path):
                win.after(100, lambda: win.iconbitmap(_icon_path))
        except Exception:
            pass

        ctk.CTkLabel(
            win,
            text=l.get("update_popup_title", "Update available"),
            font=("Roboto", 16, "bold"), text_color="#f6ad55"
        ).pack(pady=(22, 4))
        ctk.CTkLabel(
            win,
            text=l.get("update_popup_body", "Version {ver} is available. Install now?").format(ver=ver),
            font=("Roboto", 13), text_color="#e2e8f0"
        ).pack(pady=(0, 18))

        btn_row = ctk.CTkFrame(win, fg_color="transparent")
        btn_row.pack()

        def _install():
            win.destroy()
            self._do_install_update()

        ctk.CTkButton(
            btn_row,
            text=l.get("update_install_btn", "Install"),
            fg_color="#3B8ED0", hover_color="#2b6cb0",
            width=120, command=_install
        ).pack(side="left", padx=(0, 10))
        ctk.CTkButton(
            btn_row,
            text=l.get("cancel_btn", "Cancel"),
            fg_color="#2d3748", hover_color="#4a5568",
            width=100, command=win.destroy
        ).pack(side="left")

    def _on_update_label_click(self, _=None):
        status = getattr(self, "_update_status", None)
        if status == "available":
            self._do_install_update()
        elif not self.auto_update_check or status in (None, "error", "uptodate"):
            # Manual check
            self._set_update_status("checking")
            threading.Thread(target=self._check_for_updates, daemon=True).start()

    def _check_for_updates(self):
        self.after(0, lambda: self._set_update_status("checking"))
        try:
            resp = requests.get(
                f"https://api.github.com/repos/{GITHUB_REPO}/releases/latest",
                timeout=8,
                headers={"Accept": "application/vnd.github+json",
                         "X-GitHub-Api-Version": "2022-11-28"}
            )
            data = resp.json()
            if "tag_name" not in data:
                # No releases yet or API error
                self.after(0, lambda: self._set_update_status("uptodate"))
                return
            tag = data["tag_name"].lstrip("v")
            self._update_latest_ver = tag
            self._update_release_url = data.get("html_url", "")
            self._update_asset_url = None
            assets = data.get("assets", [])
            # Prefer portable .zip for auto-update
            for asset in assets:
                name = asset.get("name", "").lower()
                if "portable" in name and name.endswith(".zip"):
                    self._update_asset_url = asset.get("browser_download_url")
                    break
            # Fallback: any .zip
            if not self._update_asset_url:
                for asset in assets:
                    if asset.get("name", "").lower().endswith(".zip"):
                        self._update_asset_url = asset.get("browser_download_url")
                        break
            # Fallback: any .exe
            if not self._update_asset_url:
                for asset in assets:
                    if asset.get("name", "").lower().endswith(".exe"):
                        self._update_asset_url = asset.get("browser_download_url")
                        break
            if self._version_newer(tag, APP_VERSION):
                self.after(0, lambda: self._set_update_status("available"))
            else:
                self.after(0, lambda: self._set_update_status("uptodate"))
        except Exception:
            self.after(0, lambda: self._set_update_status("error"))

    def _do_install_update(self):
        """Download new .exe and replace current via batch script, or open browser."""
        if getattr(sys, "frozen", False) and self._update_asset_url:
            self._download_and_replace()
        else:
            # Dev mode (.py) — open browser
            url = self._update_release_url or f"https://github.com/{GITHUB_REPO}/releases/latest"
            webbrowser.open(url)

    def _download_and_replace(self):
        """Show progress window, download zip/exe, extract, launch bat to swap files."""
        import tempfile, urllib.request, zipfile

        l = self._resolve_lang()

        # ── Progress window ──────────────────────────────────────────────────
        prog_win = ctk.CTkToplevel(self)
        prog_win.title(l.get("update_progress_title", "Updating..."))
        prog_win.geometry("380x160")
        prog_win.resizable(False, False)
        prog_win.configure(fg_color="#1a202c")
        prog_win.grab_set()
        prog_win.lift()
        prog_win.focus_force()
        prog_win.protocol("WM_DELETE_WINDOW", lambda: None)   # block close
        try:
            _icon_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "icon.ico")
            if os.path.exists(_icon_path):
                prog_win.after(100, lambda: prog_win.iconbitmap(_icon_path))
        except Exception:
            pass

        lbl_stage = ctk.CTkLabel(
            prog_win,
            text=l.get("update_downloading", "Downloading update..."),
            font=("Roboto", 13), text_color="#e2e8f0"
        )
        lbl_stage.pack(pady=(28, 8))

        progress_bar = ctk.CTkProgressBar(prog_win, width=320)
        progress_bar.pack(pady=(0, 6))
        progress_bar.set(0)

        lbl_pct = ctk.CTkLabel(prog_win, text="0%", font=("Roboto", 11), text_color="#718096")
        lbl_pct.pack()

        def _set_stage(text):
            self.after(0, lambda: lbl_stage.configure(text=text))

        def _set_progress(val, pct_text=""):
            self.after(0, lambda: progress_bar.set(val))
            if pct_text:
                self.after(0, lambda: lbl_pct.configure(text=pct_text))

        # ── Download ─────────────────────────────────────────────────────────
        def _do():
            try:
                tmp_dir = tempfile.mkdtemp()
                url = self._update_asset_url
                is_zip = url.lower().endswith(".zip") or ".zip" in url.lower()

                # Download with progress callback
                dest = os.path.join(tmp_dir, "update.zip" if is_zip else "update.exe")

                def _reporthook(block, block_size, total):
                    if total > 0:
                        done = min(block * block_size, total)
                        frac = done / total
                        _set_progress(frac * 0.8, f"{int(frac * 100)}%")

                urllib.request.urlretrieve(url, dest, reporthook=_reporthook)
                _set_progress(0.8, "80%")

                if is_zip:
                    _set_stage(l.get("update_extracting", "Extracting files..."))
                    extract_dir = os.path.join(tmp_dir, "extracted")
                    with zipfile.ZipFile(dest, "r") as z:
                        z.extractall(extract_dir)
                    app_dir = os.path.dirname(os.path.abspath(sys.executable))
                    current_exe = sys.executable
                    bat = os.path.join(tmp_dir, "updater.bat")
                    with open(bat, "w", encoding="cp866") as f:
                        f.write(f'@echo off\n'
                                f'timeout /t 2 /nobreak >nul\n'
                                f'xcopy /e /i /y "{extract_dir}\\*" "{app_dir}\\"\n'
                                f'start "" "{current_exe}"\n'
                                f'rmdir /s /q "{extract_dir}"\n'
                                f'del "%~f0"\n')
                else:
                    current_exe = sys.executable
                    bat = os.path.join(tmp_dir, "updater.bat")
                    with open(bat, "w", encoding="cp866") as f:
                        f.write(f'@echo off\n'
                                f'timeout /t 2 /nobreak >nul\n'
                                f'copy /y "{dest}" "{current_exe}"\n'
                                f'start "" "{current_exe}"\n'
                                f'del "%~f0"\n')

                _set_progress(1.0, "100%")
                _set_stage(l.get("update_restarting", "Restarting..."))
                subprocess.Popen(["cmd", "/c", bat], creationflags=0x08000000)
                self.after(1200, self.on_closing)

            except Exception:
                self.after(0, prog_win.destroy)
                url = self._update_release_url or f"https://github.com/{GITHUB_REPO}/releases/latest"
                self.after(0, lambda: webbrowser.open(url))

        threading.Thread(target=_do, daemon=True).start()

    def change_ip_freq(self, choice):
        l = self._resolve_lang()
        m = {l["f_5s"]: 5, l["f_10s"]: 10, l["f_30s"]: 30, l["f_1m"]: 60,
             l["f_2m"]: 120, l["f_5m"]: 300, l["f_10m"]: 600}
        old = self.ip_update_seconds
        self.ip_update_seconds = m.get(choice, 5)
        self._append_log(f"Settings have been changed - Network Info Update Interval: {old}s -> {self.ip_update_seconds}s")
        self.last_ip_check = time.time()
        self.save_settings()

    def toggle_tray_setting(self):
        old = self.work_in_tray
        self.work_in_tray = bool(self.tray_switch.get())
        if self.work_in_tray:
            if self.icon is None:
                threading.Thread(target=self.init_tray, daemon=True).start()
            # Window stays open — tray icon just appears
        else:
            if self.icon:
                self.icon.stop()
                self.icon = None
        self._append_log(f"Settings have been changed - Work in Tray: {'On' if old else 'Off'} -> {'On' if self.work_in_tray else 'Off'}")
        self.save_settings()

    def toggle_startup(self):
        new_val = bool(self.startup_switch.get())
        app_name = "JBNetTracker"
        exe_path = f'"{os.path.realpath(sys.executable)}"'
        try:
            key = winreg.OpenKey(winreg.HKEY_CURRENT_USER,
                                 r"Software\Microsoft\Windows\CurrentVersion\Run",
                                 0, winreg.KEY_ALL_ACCESS)
            if self.startup_switch.get():
                winreg.SetValueEx(key, app_name, 0, winreg.REG_SZ, exe_path)
            else:
                winreg.DeleteValue(key, app_name)
            winreg.CloseKey(key)
        except:
            pass
        self._append_log(f"Settings have been changed - Run on Windows Startup: {'On' if new_val else 'Off'}")

    def check_startup_status(self):
        try:
            key = winreg.OpenKey(winreg.HKEY_CURRENT_USER,
                                 r"Software\Microsoft\Windows\CurrentVersion\Run",
                                 0, winreg.KEY_READ)
            winreg.QueryValueEx(key, "JBNetTracker")
            self.startup_switch.select()
            winreg.CloseKey(key)
        except:
            self.startup_switch.deselect()

    def reset_to_defaults(self):
        l = self._resolve_lang()

        dialog = ctk.CTkToplevel(self)
        dialog.title(l.get("reset_btn", "Reset"))
        dialog.geometry("400x220")
        dialog.resizable(False, False)
        dialog.configure(fg_color="#1a202c")
        dialog.transient(self)
        dialog.lift()
        dialog.focus_force()
        dialog.grab_release()

        ctk.CTkLabel(
            dialog,
            text=l.get("reset_dialog_msg",
                       "Reset settings only, or delete all app data "
                       "(including custom ping IPs and speed test history)?"),
            font=("Roboto", 12),
            wraplength=360,
            justify="center",
        ).pack(pady=(20, 16), padx=20)

        def do_settings_only():
            dialog.destroy()
            self._do_reset(keep_data=True)

        def do_all():
            dialog.destroy()
            self._do_reset(keep_data=False)

        ctk.CTkButton(
            dialog, text=l.get("reset_settings_only_btn", "Reset settings only"),
            fg_color="#4a5568", hover_color="#718096", height=32,
            command=do_settings_only,
        ).pack(fill="x", padx=24, pady=(0, 6))

        ctk.CTkButton(
            dialog, text=l.get("reset_all_btn", "Delete all data"),
            fg_color="#9b2335", hover_color="#c53030", height=32,
            command=do_all,
        ).pack(fill="x", padx=24, pady=(0, 6))

        ctk.CTkButton(
            dialog, text=l.get("cancel_btn", "Cancel"),
            fg_color="#2b4a6f", hover_color="#3a6491", height=32,
            command=dialog.destroy,
        ).pack(fill="x", padx=24)

    def _do_reset(self, keep_data=False):
        saved_dns = list(self.custom_dns_entries) if keep_data else []
        saved_history = list(self.speed_history) if keep_data else []

        if os.path.exists(CONFIG_FILE):
            try:
                os.remove(CONFIG_FILE)
            except:
                pass
        self.load_settings(reset=True)

        if keep_data:
            self.custom_dns_entries = saved_dns
            self.speed_history = saved_history

        self.startup_switch.deselect()
        self.toggle_startup()
        if self.icon:
            self.icon.stop()
            self.icon = None
        self.show_window()
        self._rebuild_custom_dns_rows()
        self.update_ui_texts()
        self.save_settings()
        if keep_data:
            self._append_log("Reset to Default (Reset settings only) completed successfully")
        else:
            self._append_log("Reset to Default (Delete all Data) completed successfully")

    # ─── Tray ────────────────────────────────────────────────────────────────

    def update_tray_visibility(self):
        if self.work_in_tray and self.icon is None:
            threading.Thread(target=self.init_tray, daemon=True).start()

    def init_tray(self):
        def on_show(icon, menu_item):
            self.after(0, self.show_window)

        def on_settings(icon, menu_item):
            self.after(0, lambda: self._open_tab("Settings"))

        def on_speed_check(icon, menu_item):
            self.after(0, lambda: self._open_tab("Speed"))

        def on_exit(icon, menu_item):
            self.after(0, self.quit_app)

        _icon_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "icon.ico")
        if os.path.exists(_icon_path):
            img = Image.open(_icon_path).convert("RGBA").resize((64, 64))
        else:
            img = Image.new('RGB', (64, 64), color='#1a202c')
            d = ImageDraw.Draw(img)
            d.ellipse((5, 5, 59, 59), fill='#3B8ED0')

        self.icon = pystray.Icon(
            "JBNetTracker",
            img,
            "JB NetTracker",
            pystray.Menu(
                item(lambda i: self._resolve_lang()["tray_open"], on_show, default=True),
                item(lambda i: self._resolve_lang()["tray_settings"], on_settings),
                item(lambda i: self._resolve_lang()["tray_speed_check"], on_speed_check),
                item(lambda i: self._resolve_lang()["tray_exit"], on_exit),
            )
        )
        self.icon.run()

    def _open_tab(self, tab_key):
        self.show_window()
        try:
            self.tab_view.set(tab_key)
        except:
            pass

    def update_tray_tooltip(self):
        if self.icon:
            self.icon.title = f"JB NetTracker\nIP: {self.current_ip}\n{self.current_loc}"

    # ─── Window ──────────────────────────────────────────────────────────────

    def send_windows_notification(self, title, message):
        def _notify():
            # Try 1: plyer (cross-platform, usually works)
            try:
                notification.notify(
                    title=title,
                    message=message,
                    app_name="JB NetTracker",
                    timeout=5
                )
                return
            except Exception:
                pass
            # Try 2: PowerShell WinForms BalloonTip (guaranteed on Windows)
            try:
                safe_t = title.replace('"', "'")
                safe_m = message.replace('"', "'")
                ps = (
                    "Add-Type -AssemblyName System.Windows.Forms;"
                    "Add-Type -AssemblyName System.Drawing;"
                    "$n=New-Object System.Windows.Forms.NotifyIcon;"
                    "$n.Icon=[System.Drawing.SystemIcons]::Information;"
                    "$n.Visible=$true;"
                    f'$n.BalloonTipTitle="{safe_t}";'
                    f'$n.BalloonTipText="{safe_m}";'
                    "$n.BalloonTipIcon='Info';"
                    "$n.ShowBalloonTip(5000);"
                    "Start-Sleep -Seconds 6;"
                    "$n.Dispose()"
                )
                subprocess.Popen(
                    ["powershell", "-WindowStyle", "Hidden", "-NonInteractive", "-Command", ps],
                    creationflags=0x08000000
                )
            except Exception:
                pass
        threading.Thread(target=_notify, daemon=True).start()

    def show_window(self):
        self.is_window_visible = True
        self.deiconify()
        self.focus_force()

    def on_closing(self):
        if self.work_in_tray:
            self.is_window_visible = False
            self.withdraw()
        else:
            self.quit_app()

    def quit_app(self):
        self._append_log("Application closed")
        try:
            with open(LOG_FILE, "w", encoding="utf-8") as f:
                f.write("\n".join(self._log_lines))
        except Exception:
            pass
        if self.icon:
            self.icon.stop()
        self.destroy()
        os._exit(0)


if __name__ == "__main__":
    app = NetCheckerApp()
    app.mainloop()
