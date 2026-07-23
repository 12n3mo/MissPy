from __future__ import annotations

import asyncio
import concurrent.futures
import csv
import io
import json
import math
import os
import re
import secrets
from dataclasses import dataclass, field
from datetime import datetime
from functools import partial
from typing import Optional

import flet as ft

# ---------------------------------------------------------------------------
# Constants & design tokens
# ---------------------------------------------------------------------------

APP_TITLE = "Cipher — Secure Password Generator"

DEFAULT_LENGTH = 37
DEFAULT_COUNT = 1
MAX_LENGTH = 512   # Assumption: sane upper bound not present in original CLI.
MAX_COUNT = 500    # Assumption: prevents accidental runaway generation.

FULL_ASCII_CHARSET = ''.join(chr(i) for i in range(33, 127))  # 94 printable chars

# Common exclusion bundles — mirrors the original CLI's --exclude epilog.
EXCLUSION_PRESETS: dict[str, str] = {
    "No quotes & backslash": "\"'\\",
    "No space": " ",
    "Ambiguous (l 1 I O 0)": "l1IO0",
    "URL-unsafe (&?#=)": "&?#=",
    "Letters & digits only": ''.join(c for c in FULL_ASCII_CHARSET if not c.isalnum()),
}

FONT_DISPLAY = "Space Grotesk"
FONT_BODY = "Inter"
FONT_MONO = "JetBrains Mono"

SPACE_GROTESK_URL = "https://fonts.gstatic.com/s/spacegrotesk/v22/V8mQoQDjQSkFtoMM3T6r8E7mF71Q-gOoraIAEj7oUUsj.ttf"
JETBRAINS_MONO_URL = "https://cdn.jsdelivr.net/gh/JetBrains/JetBrainsMono/ttf/JetBrainsMono-Regular.ttf"

HELP_MARKDOWN = """
### How password strength works

Each password is drawn uniformly at random from a character set using
Python's `secrets` module — the same cryptographically secure generator
used for tokens and session keys. Strength is measured in **bits of
entropy**: `length × log2(charset size)`.

| Bits | Rating |
|---|---|
| < 40 | Weak |
| 40 – 64 | Fair |
| 64 – 100 | Strong |
| 100+ | Excellent |

### Exclusion presets

Switch the character set to **Full ASCII, minus exclusions** and tap a
preset to quickly remove characters that cause trouble in certain systems:

- **No quotes & backslash** — avoids characters that break shell quoting.
- **No space** — keeps passwords copy-paste and double-click friendly.
- **Ambiguous characters (l 1 I O 0)** — avoids characters easy to misread
  when typed by hand.
- **URL-unsafe symbols (&?#=)** — safer to embed in query strings.
- **Letters & digits only** — removes all symbols for systems with strict
  input rules.

Each preset pill is a toggle: tap it once to apply it (its outline turns
teal), tap it again to remove exactly what it added.

### Custom character sets

Switch to **Custom character set** to type the exact characters you want
to allow — this overrides exclusions entirely, just like the original
script's `-s` flag did.
"""


class Palette:
    """Color tokens for the Cipher design system."""

    ACCENT = "#14B8A6"       # cipher teal — primary brand / generated data
    ACCENT_GOLD = "#8B5CF6"  # violet — excellent-strength highlight, kept distinct from WARNING's amber
    WARNING = "#F59E0B"      # amber — fair strength / soft warnings
    DANGER = "#F43F5E"       # rose — weak strength / errors


# ---------------------------------------------------------------------------
# Business logic (no Flet/UI imports here — pure and independently testable)
# ---------------------------------------------------------------------------

class PasswordGeneratorService:
    """Cryptographic password generation and scoring logic.

    Mirrors the original CLI script's `generate_password` plus the
    charset-resolution logic that used to live inline in `main()`.
    """

    @staticmethod
    def build_charset(mode: str, custom: str, exclude: str) -> str:
        """Resolve the effective charset from the UI's charset mode.

        Args:
            mode: One of "default", "custom", or "exclude".
            custom: User-supplied charset (used when mode == "custom").
            exclude: Characters to strip from the default set (mode == "exclude").
        """
        if mode == "custom":
            # De-duplicate while preserving first-seen order. Without this,
            # a repeated character (e.g. "aabbc") gets picked by
            # secrets.choice with higher probability than the others, so the
            # password is no longer drawn uniformly over its *distinct*
            # characters — the actual entropy is lower than
            # length * log2(len(set(charset))), which is what the UI reports.
            # Deduplicating here guarantees the two match.
            charset = ''.join(dict.fromkeys(custom))
        elif mode == "exclude":
            exclude_set = set(exclude)
            charset = ''.join(c for c in FULL_ASCII_CHARSET if c not in exclude_set)
        else:
            charset = FULL_ASCII_CHARSET

        if not charset:
            raise ValueError(
                "The resulting character set is empty. Adjust your custom "
                "characters or exclusions."
            )
        return charset

    @staticmethod
    def generate_password(length: int, charset: str) -> str:
        """Generate a single cryptographically secure password."""
        if length < 1:
            raise ValueError("Password length must be at least 1.")
        if not charset:
            raise ValueError("Charset must not be empty.")
        return ''.join(secrets.choice(charset) for _ in range(length))

    @staticmethod
    def parse_words(raw: str) -> list[str]:
        """Split user-entered text into individual words to embed. Accepts
        comma or whitespace as separators and drops empty entries.
        """
        parts = re.split(r'[,\s]+', raw.strip())
        return [p for p in parts if p]

    @staticmethod
    def generate_password_with_words(length: int, charset: str, words: list[str]) -> str:
        """Generate a password that embeds every word from `words` intact and
        fills every remaining position with a character drawn uniformly at
        random from `charset` via `secrets`.

        Placement is randomized: both which word claims which free region,
        and where within the available room it lands, are chosen via
        `secrets` — not just the fill characters — so a word's position
        also varies from password to password rather than always sitting
        at the same spot (e.g. always first).
        """
        if length < 1:
            raise ValueError("Password length must be at least 1.")
        if not charset:
            raise ValueError("Charset must not be empty.")
        total_word_len = sum(len(w) for w in words)
        if total_word_len > length:
            raise ValueError(
                f"The words you entered need {total_word_len} characters, but "
                f"the password length is only {length}."
            )

        slots: list[Optional[str]] = [None] * length

        # Randomize placement order so which word claims a given region
        # isn't deterministic run-to-run.
        word_order = list(words)
        for i in range(len(word_order) - 1, 0, -1):
            j = secrets.randbelow(i + 1)
            word_order[i], word_order[j] = word_order[j], word_order[i]

        for word in word_order:
            wlen = len(word)
            possible_starts = [
                start for start in range(length - wlen + 1)
                if all(slots[start + k] is None for k in range(wlen))
            ]
            if not possible_starts:
                raise ValueError(
                    "Not enough room to fit all the words into the requested "
                    "length without overlapping — try a longer password or "
                    "fewer/shorter words."
                )
            start = secrets.choice(possible_starts)
            for k, ch in enumerate(word):
                slots[start + k] = ch

        for i in range(length):
            if slots[i] is None:
                slots[i] = secrets.choice(charset)
        return ''.join(slots)
    @staticmethod
    def entropy_bits(length: int, charset_size: int) -> float:
        """Shannon entropy (bits) of a password drawn uniformly from charset_size options."""
        if charset_size <= 1:
            return 0.0
        return length * math.log2(charset_size)

    @staticmethod
    def entropy_tier(bits: float) -> tuple[str, str]:
        """Return (label, color-hex) describing how strong `bits` of entropy is."""
        if bits < 40:
            return "Weak", Palette.DANGER
        if bits < 64:
            return "Fair", Palette.WARNING
        if bits < 100:
            return "Strong", Palette.ACCENT
        return "Excellent", Palette.ACCENT_GOLD

    @staticmethod
    def to_txt(passwords: list[str]) -> str:
        return "\n".join(passwords)

    @staticmethod
    def to_csv(passwords: list[str]) -> str:
        buf = io.StringIO()
        writer = csv.writer(buf)
        writer.writerow(["#", "password"])
        for i, pw in enumerate(passwords, start=1):
            writer.writerow([i, pw])
        return buf.getvalue()

    @staticmethod
    def to_json(passwords: list[str]) -> str:
        return json.dumps({"passwords": passwords}, indent=2)


@dataclass
class GenerationResult:
    """Holds the outcome of the most recent generation run."""

    passwords: list[str] = field(default_factory=list)
    charset_size: int = 0
    length: int = 0
    override_entropy_bits: Optional[float] = None

    @property
    def entropy_bits(self) -> float:
        if self.override_entropy_bits is not None:
            return self.override_entropy_bits
        return PasswordGeneratorService.entropy_bits(self.length, self.charset_size)

# ---------------------------------------------------------------------------
# UI layer
# ---------------------------------------------------------------------------

class CipherApp:
    """Builds and drives the Cipher Flet UI. Delegates all logic to the service."""
    def __init__(self, page: ft.Page) -> None:
        self.page = page
        self.last_result: Optional[GenerationResult] = None
        self._status_token = 0
        self._preset_active: dict[str, bool] = dict.fromkeys(EXCLUSION_PRESETS, False)
        self.preset_buttons: dict[str, ft.OutlinedButton] = {}
        # Guards on_generate against overlapping runs. disabling generate_btn
        # isn't enough by itself: a fast double-click (or click spam) can fire
        # several click events before the disabled state round-trips back to
        # the client, so multiple on_generate coroutines can end up racing
        # each other. This flag is checked and set synchronously, before any
        # `await`, so a second click sees it immediately and bails out.
        self._generating = False
        # tkinter/Tcl must be driven from a single consistent OS thread for its
        # whole lifetime — the default executor can hop threads between calls,
        # which is what caused "Tcl_AsyncDelete: wrong thread" crashes.
        self._tk_executor = concurrent.futures.ThreadPoolExecutor(max_workers=1)

    # -- setup ---------------------------------------------------------

    def build(self) -> None:
        """Configure the page, build every control, and lay out the app."""
        page = self.page
        # Defensive: if build() ever runs a second time on the same page —
        # Flet hot-reload re-invoking main(), or a router calling this view
        # builder again — page.add() below would otherwise stack a second
        # Stack on top of the first, producing overlapping/duplicated UI and
        # controls that silently point at stale state. Clearing first makes
        # build() idempotent regardless of how many times it's called.
        page.controls.clear()
        page.overlay.clear()
        page.title = APP_TITLE
        page.theme_mode = ft.ThemeMode.DARK
        page.theme = ft.Theme(color_scheme_seed=Palette.ACCENT, font_family=FONT_BODY, use_material3=True)
        page.dark_theme = ft.Theme(color_scheme_seed=Palette.ACCENT, font_family=FONT_BODY, use_material3=True)
        page.fonts = {FONT_DISPLAY: SPACE_GROTESK_URL, FONT_MONO: JETBRAINS_MONO_URL}
        page.padding = 0
        # Scroll lives on main_column (below), not the page itself — that way the
        # outer Stack always matches the real window viewport, so the toast
        # (pinned to the Stack's top-right) stays visible no matter how far the
        # user has scrolled the form/results content.
        try:
            page.window.width = 900
            page.window.height = 700
            page.window.min_width = 420
            page.window.min_height = 640
            center_result = page.window.center()
            if asyncio.iscoroutine(center_result):
                asyncio.create_task(center_result)
        except Exception:
            pass  # Window sizing API varies across Flet versions — safe to skip.

        self._build_controls()

        header = ft.Container(
            content=ft.Row(
                [
                    ft.Row(
                        [
                            ft.Icon(ft.Icons.LOCK_OUTLINE, color=Palette.ACCENT, size=32),
                            ft.Column(
                                [
                                    ft.Text(
                                        APP_TITLE, size=22, weight=ft.FontWeight.BOLD, font_family=FONT_DISPLAY,
                                        max_lines=2, overflow=ft.TextOverflow.ELLIPSIS,
                                    ),
                                    ft.Text(
                                        "CSPRNG-backed password generation", size=12, opacity=0.7,
                                        max_lines=1, overflow=ft.TextOverflow.ELLIPSIS,
                                    ),
                                ],
                                spacing=0,
                                expand=True,
                            ),
                        ],
                        spacing=12,
                        expand=True,
                    ),
                    self.theme_toggle_btn,
                ],
                alignment=ft.MainAxisAlignment.SPACE_BETWEEN,
            ),
            padding=ft.Padding(left=24, top=20, right=24, bottom=20),
        )

        form_card = ft.Card(content=ft.Container(content=self._form_column(), padding=20), elevation=1)
        results_card = ft.Card(content=ft.Container(content=self._results_column(), padding=20), elevation=1)

        generator_tab = ft.Container(
            content=ft.ResponsiveRow(
                [
                    ft.Container(form_card, col={"xs": 12, "md": 5}),
                    ft.Container(results_card, col={"xs": 12, "md": 7}),
                ],
                spacing=20,
                run_spacing=20,
            ),
            padding=ft.Padding(left=24, top=8, right=24, bottom=8),
        )

        help_tab = ft.Container(
            content=ft.Markdown(
                HELP_MARKDOWN, selectable=True, extension_set=ft.MarkdownExtensionSet.GITHUB_WEB
            ),
            padding=24,
        )
        self.tab_content_controls = [generator_tab, help_tab]
        self.tab_content_container = ft.Container(content=generator_tab, expand=True)
        tab_buttons = ft.Row(
            [
                ft.OutlinedButton(
                    content=ft.Text("Generator"),
                    icon=ft.Icons.KEY_ROUNDED,
                    on_click=partial(self.switch_tab, 0),
                    style=ft.ButtonStyle(shape=ft.RoundedRectangleBorder(radius=8)),
                ),
                ft.OutlinedButton(
                    content=ft.Text("Presets & Help"),
                    icon=ft.Icons.HELP_OUTLINE,
                    on_click=partial(self.switch_tab, 1),
                    style=ft.ButtonStyle(shape=ft.RoundedRectangleBorder(radius=8)),
                ),
            ],
            spacing=0,
        )

        main_column = ft.Column(
            [header, ft.Divider(height=1), tab_buttons, self.tab_content_container],
            expand=True, spacing=0, scroll=ft.ScrollMode.ADAPTIVE,
        )
        page.add(ft.Stack([main_column, self.status_banner], expand=True))

    def _build_controls(self) -> None:
        """Instantiate every stateful control used across the UI."""
        self.theme_icon = ft.Icon(ft.Icons.LIGHT_MODE_OUTLINED, size=20)
        self.theme_toggle_btn = ft.Container(
            content=self.theme_icon,
            width=44,
            height=44,
            border_radius=22,
            alignment=ft.Alignment(0, 0),
            ink=True,
            on_click=self.on_toggle_theme,
            tooltip="Switch to light theme",
        )

        self.status_icon = ft.Icon(ft.Icons.CHECK_CIRCLE_ROUNDED, size=20, color=Palette.ACCENT)
        self.status_text = ft.Text(value="", size=13, weight=ft.FontWeight.W_600, expand=True)
        self.status_banner = ft.Container(
            content=ft.Row(
                [
                    self.status_icon,
                    self.status_text,
                    ft.IconButton(icon=ft.Icons.CLOSE, icon_size=16, on_click=self._hide_status),
                ],
                spacing=10,
                alignment=ft.MainAxisAlignment.START,
                vertical_alignment=ft.CrossAxisAlignment.CENTER,
            ),
            padding=ft.Padding(left=16, top=12, right=8, bottom=12),
            width=340,
            border_radius=10,
            bgcolor="#1F2937",
            shadow=ft.BoxShadow(blur_radius=18, spread_radius=1, color=ft.Colors.with_opacity(0.35, "#000000")),
            top=24,
            right=24,
            opacity=0,
            scale=0.9,
            offset=ft.Offset(0, -0.15),
            animate_opacity=ft.Animation(220, ft.AnimationCurve.EASE_OUT),
            animate_scale=ft.Animation(220, ft.AnimationCurve.EASE_OUT),
            animate_offset=ft.Animation(220, ft.AnimationCurve.EASE_OUT),
        )

        # -- Form controls ------------------------------------------------
        self.count_field = ft.TextField(
            value=str(DEFAULT_COUNT), width=70, text_align=ft.TextAlign.CENTER,
            keyboard_type=ft.KeyboardType.NUMBER, dense=True,
        )
        self.length_field = ft.TextField(
            label="Length", value=str(DEFAULT_LENGTH), width=100,
            keyboard_type=ft.KeyboardType.NUMBER, dense=True,
            on_change=self._on_length_field_change,
        )
        self.length_slider = ft.Slider(
            min=1, max=128, value=DEFAULT_LENGTH, divisions=127, label="{value}",
            on_change=self._on_length_slider_change, expand=True,
        )
        self.mode_group = ft.RadioGroup(
            value="default",
            on_change=self._on_mode_change,
            content=ft.Column(
                [
                    ft.Radio(value="default", label="Full ASCII (94 characters)"),
                    ft.Radio(value="exclude", label="Full ASCII, minus exclusions"),
                    ft.Radio(value="custom", label="Custom character set"),
                    ft.Radio(value="words", label="Include specific words"),
                ],
                spacing=4,
            ),
        )
        self.exclude_field = ft.TextField(label="Characters to exclude", value="", visible=False, dense=True)
        self.custom_field = ft.TextField(label="Custom allowed characters", value="", visible=False, dense=True)
        self.words_field = ft.TextField(
            label="Words (comma or space separated)",
            value="",
            visible=False,
            dense=True,
            hint_text="e.g. Nemo1203, Blue",
        )
        self.preset_row = ft.Row(
            [self._preset_pill(name, chars) for name, chars in EXCLUSION_PRESETS.items()],
            wrap=True, spacing=8, run_spacing=8, visible=False,
        )
        self.generate_btn = ft.FilledButton(content=ft.Text("Generate"), icon=ft.Icons.BOLT_ROUNDED, on_click=self.on_generate)
        self.reset_btn = ft.OutlinedButton(content=ft.Text("Reset"), icon=ft.Icons.RESTART_ALT, on_click=self.on_reset)
        self.progress_bar = ft.ProgressBar(value=0, visible=False, color=Palette.ACCENT)

        # -- Results controls ----------------------------------------------
        self.mask_switch = ft.Switch(label="Mask passwords", value=False, on_change=lambda e: self._render_results())
        self.export_format = ft.Dropdown(
            label="Format", width=110, dense=True, value="txt",
            options=[ft.dropdown.Option("txt"), ft.dropdown.Option("csv"), ft.dropdown.Option("json")],
        )
        self.export_btn = ft.OutlinedButton(content=ft.Text("Export"), icon=ft.Icons.DOWNLOAD_ROUNDED, on_click=self.on_export_click)
        self.copy_all_btn = ft.OutlinedButton(content=ft.Text("Copy all"), icon=ft.Icons.COPY_ALL_OUTLINED, on_click=self.on_copy_all)
        self.clear_btn = ft.TextButton(content=ft.Text("Clear"), icon=ft.Icons.CLEAR_ROUNDED, on_click=self.on_clear_results)
        self.results_body = ft.Container(content=self._empty_state())

        self.export_path_field = ft.TextField(label="Save to", dense=True, expand=True)
        self.browse_btn = ft.IconButton(
            icon=ft.Icons.FOLDER_OPEN_ROUNDED, tooltip="Browse…", on_click=self._browse_export_path,
        )
        self.export_dialog = ft.AlertDialog(
            title=ft.Text("Export passwords"),
            content=ft.Column(
                [
                    ft.Text("Choose where to save the exported file.", size=12, opacity=0.7),
                    ft.Row(
                        [self.export_path_field, self.browse_btn],
                        vertical_alignment=ft.CrossAxisAlignment.CENTER,
                    ),
                ],
                tight=True,
                spacing=8,
                width=440,
            ),
            actions=[
                ft.TextButton(content=ft.Text("Cancel"), on_click=self._close_export_dialog),
                ft.FilledButton(content=ft.Text("Save"), on_click=self._do_export),
            ],
        )

        # Built once and reused for every clipboard-fallback prompt (see
        # _show_copy_dialog) — previously a fresh AlertDialog was constructed
        # per call and never released from page.overlay, leaking one control
        # per failed copy over a long session.
        self.copy_fallback_text = ft.Text("", selectable=True, font_family=FONT_MONO, size=14)
        self.copy_fallback_dialog = ft.AlertDialog(
            title=ft.Text("Copy text"),
            content=ft.Column(
                [
                    ft.Text(
                        "Select the text below, then press Ctrl+C (Cmd+C on Mac).",
                        size=12, italic=True, opacity=0.7,
                    ),
                    ft.Container(
                        content=self.copy_fallback_text,
                        padding=10,
                        bgcolor=ft.Colors.with_opacity(0.05, ft.Colors.ON_SURFACE),
                        border_radius=8,
                    ),
                ],
                tight=True,
                spacing=12,
            ),
            actions=[
                ft.TextButton(
                    content=ft.Text("Close"),
                    on_click=lambda e: self._close_ctl(self.copy_fallback_dialog),
                )
            ],
        )

        self.entropy_dialog = ft.AlertDialog(
            title=ft.Text("About entropy"),
            content=ft.Text(
                "Entropy estimates how many guesses an attacker would need, on "
                "average, to find your password by brute force. Every extra bit "
                "doubles that number. 64+ bits is solid for most accounts; 100+ "
                "is appropriate for high-value secrets like master passwords."
            ),
            actions=[ft.TextButton(content=ft.Text("Got it"), on_click=self._close_entropy_dialog)],
        )
        self.weak_charset_banner = ft.Banner(
            bgcolor=ft.Colors.with_opacity(0.12, Palette.WARNING),
            leading=ft.Icon(ft.Icons.WARNING_AMBER_ROUNDED, color=Palette.WARNING),
            content=ft.Text(
                "Your character set is very small. Passwords generated with it "
                "will be much easier to brute-force — consider widening it."
            ),
            actions=[ft.TextButton(content=ft.Text("Dismiss"), on_click=self._close_banner)],
        )

    # -- layout helpers --------------------------------------------------

    def _form_column(self) -> ft.Control:
        length_presets = ft.Row(
            [ft.TextButton(content=ft.Text(str(v)), on_click=partial(self._set_length_preset, v)) for v in (12, 16, 24, 32, 37, 64)],
            wrap=True, spacing=4,
        )
        count_row = ft.Row(
            [
                ft.Text("Number of passwords", size=13, weight=ft.FontWeight.W_500),
                ft.Row(
                    [
                        ft.IconButton(icon=ft.Icons.REMOVE, icon_size=16, on_click=partial(self._adjust_count, -1)),
                        self.count_field,
                        ft.IconButton(icon=ft.Icons.ADD, icon_size=16, on_click=partial(self._adjust_count, 1)),
                    ],
                    spacing=0,
                ),
            ],
            alignment=ft.MainAxisAlignment.SPACE_BETWEEN,
        )
        return ft.Column(
            [
                ft.Text("Generate", size=18, weight=ft.FontWeight.BOLD, font_family=FONT_DISPLAY),
                count_row,
                ft.Divider(height=1),
                ft.Text("Password length", size=13, weight=ft.FontWeight.W_500),
                ft.Row([self.length_slider, self.length_field], vertical_alignment=ft.CrossAxisAlignment.CENTER),
                length_presets,
                ft.Divider(height=1),
                ft.Text("Character set", size=13, weight=ft.FontWeight.W_500),
                self.mode_group,
                self.preset_row,
                self.exclude_field,
                self.custom_field,
                self.words_field,
                ft.Container(height=8),
                self.progress_bar,
                ft.Row([self.generate_btn, self.reset_btn], spacing=12),
            ],
            spacing=12,
        )

    def _results_column(self) -> ft.Control:
        return ft.Column(
            [
                ft.Row(
                    [
                        ft.Text("Results", size=18, weight=ft.FontWeight.BOLD, font_family=FONT_DISPLAY),
                        ft.IconButton(
                            icon=ft.Icons.INFO_OUTLINE, icon_size=18, tooltip="What does entropy mean?",
                            on_click=self._open_entropy_dialog,
                        ),
                    ],
                ),
                self.mask_switch,
                self.results_body,
                ft.Row([self.copy_all_btn, self.export_format, self.export_btn, self.clear_btn],
                       wrap=True, spacing=8, run_spacing=8),
            ],
            spacing=12,
        )

    def _empty_state(self) -> ft.Control:
        return ft.Container(
            content=ft.Column(
                [
                    ft.Container(ft.Icon(ft.Icons.KEY_OFF_ROUNDED, size=40), opacity=0.4),
                    ft.Text("No passwords yet — set your options and press Generate.",
                            opacity=0.6, text_align=ft.TextAlign.CENTER),
                ],
                horizontal_alignment=ft.CrossAxisAlignment.CENTER,
                spacing=8,
            ),
            alignment=ft.Alignment(0, 0),
            height=200,
        )

    def _entropy_meter(self, bits: float) -> ft.Control:
        """Signature widget: an ascending 'key teeth' bar strip showing entropy."""
        label, color = PasswordGeneratorService.entropy_tier(bits)
        filled = min(8, max(1, round(bits / 16)))
        bars = [
            ft.Container(
                width=8,
                height=10 + i * 3,
                border_radius=2,
                bgcolor=color if i < filled else ft.Colors.with_opacity(0.15, ft.Colors.ON_SURFACE),
            )
            for i in range(8)
        ]
        return ft.Row(
            [ft.Row(bars, spacing=3), ft.Text(f"{bits:.1f} bits · {label}", weight=ft.FontWeight.W_600, color=color)],
            spacing=12,
            vertical_alignment=ft.CrossAxisAlignment.END,
        )

    def _preset_pill(self, name: str, chars: str) -> ft.Control:
        """Plain text pill, matching the original minimal look. On/off state
        is shown purely through its style (border + text color) — no icon,
        no extra chrome."""
        btn = ft.OutlinedButton(
            content=ft.Text(name, size=13),
            style=self._preset_pill_style(active=False),
            on_click=partial(self._apply_preset, name, chars),
            tooltip=f"{name} — click to enable",
        )
        self.preset_buttons[name] = btn
        return btn

    @staticmethod
    def _preset_pill_style(active: bool) -> ft.ButtonStyle:
        if active:
            return ft.ButtonStyle(
                shape=ft.RoundedRectangleBorder(radius=20),
                bgcolor=ft.Colors.with_opacity(0.12, Palette.ACCENT),
                color=Palette.ACCENT,
                side=ft.BorderSide(1.4, Palette.ACCENT),
            )
        return ft.ButtonStyle(
            shape=ft.RoundedRectangleBorder(radius=20),
            side=ft.BorderSide(1, ft.Colors.with_opacity(0.25, ft.Colors.ON_SURFACE)),
        )

    def _build_rows(self, passwords: list[str]) -> tuple[list[ft.Control], list[ft.Control], list[ft.Control]]:
        """Builds three column-parallel lists (index cells, password cells,
        copy-button cells). Index and copy-button columns render outside any
        scroll container so they stay pinned; password cells are stacked into
        ONE shared scrollable column in _render_results, so a single
        scrollbar reveals overflow for every row together.

        ROW_HEIGHT is fixed at 48px — matching a default IconButton's tap/
        splash target — rather than a smaller value, specifically so the
        copy button never gets vertically clipped by its own container and
        so all three parallel columns are guaranteed pixel-identical row
        heights regardless of font metrics or platform rendering.
        """
        ROW_HEIGHT = 48
        border = ft.Border(bottom=ft.BorderSide(1, ft.Colors.with_opacity(0.06, ft.Colors.ON_SURFACE)))
        index_cells: list[ft.Control] = []
        password_cells: list[ft.Control] = []
        copy_cells: list[ft.Control] = []
        for idx, pw in enumerate(passwords, start=1):
            display = ("•" * len(pw)) if self.mask_switch.value else pw
            index_cells.append(
                ft.Container(ft.Text(str(idx), size=13), height=ROW_HEIGHT, width=32,
                             alignment=ft.Alignment(0, 0), border=border)
            )
            password_cells.append(
                ft.Container(
                    ft.Text(display, font_family=FONT_MONO, selectable=True, size=13, no_wrap=True),
                    height=ROW_HEIGHT, alignment=ft.Alignment(-1, 0),
                    padding=ft.Padding(left=8, top=0, right=8, bottom=0), border=border,
                )
            )
            copy_cells.append(
                ft.Container(
                    ft.IconButton(icon=ft.Icons.COPY_ALL_OUTLINED, tooltip="Copy password", icon_size=18,
                                  on_click=partial(self._copy_one, pw)),
                    height=ROW_HEIGHT, width=48, alignment=ft.Alignment(0, 0), border=border,
                    clip_behavior=ft.ClipBehavior.HARD_EDGE,
                )
            )
        return index_cells, password_cells, copy_cells

    # -- render --------------------------------------------------------

    async def _copy_to_clipboard(self, text: str) -> None:
        """Copy text using Flet's Clipboard service, with a manual-copy fallback."""
        try:
            await ft.Clipboard().set(text)
        except Exception:
            # Clipboard access can be blocked (e.g. browser permissions) — fall
            # back to a selectable dialog so the user can copy manually.
            self._show_copy_dialog(text)

    def _open_ctl(self, control) -> None:
        """Show a dialog/banner/snackbar, working across Flet API versions.

        Newer Flet (0.80+) uses page.open(control). Older Flet has no such
        method and instead needs the control assigned to a specific page
        attribute (page.dialog / page.banner / page.snack_bar) with
        control.open = True.
        """
        if hasattr(self.page, "open"):
            self.page.open(control)
            self.page.update()
            return
        if hasattr(self.page, "show_dialog"):
            self.page.show_dialog(control)
            self.page.update()
            return
        if control not in self.page.overlay:
            self.page.overlay.append(control)
        control.open = True
        self.page.update()

    def _close_ctl(self, control) -> None:
        """Hide a dialog/banner/snackbar, working across Flet API versions."""
        if hasattr(self.page, "close"):
            self.page.close(control)
            self.page.update()
            return
        if hasattr(self.page, "pop_dialog"):
            self.page.pop_dialog()
            self.page.update()
            return
        control.open = False
        # On the legacy path _open_ctl appended `control` to page.overlay to
        # display it. Without removing it again here, every closed dialog
        # stayed in page.overlay forever — harmless for the few singleton
        # dialogs built once in _build_controls, but unbounded for any
        # dialog created fresh per call (see _show_copy_dialog below).
        if control in self.page.overlay:
            self.page.overlay.remove(control)
        self.page.update()

    def _show_banner(self, banner: ft.Banner) -> None:
        """Show a Banner, working across Flet API versions.

        _open_ctl's legacy fallback (page.overlay.append + control.open =
        True) is written for dialogs/snackbars; several Flet versions never
        rendered a Banner from page.overlay at all — it has historically
        been driven through a dedicated `page.banner` property or a
        `page.show_banner()` method instead. Reusing _open_ctl for the
        weak-charset banner meant the warning silently never appeared on
        those versions. This targets Banner's actual API surface directly.
        """
        page = self.page
        if hasattr(page, "open"):
            # Modern unified API — page.open() dispatches on control type,
            # Banner included.
            page.open(banner)
            page.update()
            return
        if hasattr(page, "show_banner"):
            page.show_banner(banner)
            page.update()
            return
        if hasattr(page, "banner"):
            page.banner = banner
            banner.open = True
            page.update()
            return
        # No known banner API on this version — last resort, generic overlay.
        self._open_ctl(banner)

    def _hide_banner(self, banner: ft.Banner) -> None:
        """Counterpart to _show_banner — clears whichever API surface was used to show it."""
        page = self.page
        if hasattr(page, "close"):
            page.close(banner)
            page.update()
            return
        if hasattr(page, "hide_banner"):
            page.hide_banner()
            page.update()
            return
        banner.open = False
        if hasattr(page, "banner") and page.banner is banner:
            page.banner = None
        if banner in page.overlay:
            page.overlay.remove(banner)
        page.update()

    def _show_copy_dialog(self, text: str) -> None:
        """Show the text in a selectable dialog as a last-resort copy method.

        Reuses the single dialog/text control built in _build_controls
        rather than constructing a new AlertDialog per call.
        """
        self.copy_fallback_text.value = text
        self._open_ctl(self.copy_fallback_dialog)

    def _open_entropy_dialog(self, e: ft.ControlEvent) -> None:
        self._open_ctl(self.entropy_dialog)

    def _close_entropy_dialog(self, e: ft.ControlEvent) -> None:
        self._close_ctl(self.entropy_dialog)

    def _close_banner(self, e: ft.ControlEvent) -> None:
        self._hide_banner(self.weak_charset_banner)

    def _render_results(self) -> None:
        result = self.last_result
        if result is None or not result.passwords:
            self.results_body.content = self._empty_state()
            self.page.update()
            return

        index_cells, password_cells, copy_cells = self._build_rows(result.passwords)
        table_body = ft.Row(
            [
                ft.Column(index_cells, spacing=0),
                ft.Container(
                    content=ft.Row([ft.Column(password_cells, spacing=0)], scroll=ft.ScrollMode.AUTO),
                    expand=True,
                ),
                ft.Column(copy_cells, spacing=0),
            ],
            vertical_alignment=ft.CrossAxisAlignment.START,
            spacing=0,
        )
        header_row = ft.Row(
            [
                ft.Container(ft.Text("#", weight=ft.FontWeight.W_600, size=12, opacity=0.7), width=32),
                ft.Container(
                    ft.Text("Password", weight=ft.FontWeight.W_600, size=12, opacity=0.7),
                    expand=True, padding=ft.Padding(left=8, top=0, right=8, bottom=0),
                ),
                ft.Container(width=48),
            ],
            spacing=0,
        )
        self.results_body.content = ft.Column(
            [
                ft.Row(
                    [self._entropy_meter(result.entropy_bits),
                     ft.Text(f"{len(result.passwords)} generated", size=12, opacity=0.6)],
                    alignment=ft.MainAxisAlignment.SPACE_BETWEEN,
                ),
                ft.Container(
                    content=ft.Column(
                        [
                            header_row,
                            ft.Divider(height=1),
                            ft.Column([table_body], scroll=ft.ScrollMode.AUTO, expand=True),
                        ],
                        spacing=4,
                        expand=True,
                    ),
                    height=320,
                    border=ft.Border(
                        top=ft.BorderSide(1, ft.Colors.with_opacity(0.1, ft.Colors.ON_SURFACE)),
                        bottom=ft.BorderSide(1, ft.Colors.with_opacity(0.1, ft.Colors.ON_SURFACE)),
                        left=ft.BorderSide(1, ft.Colors.with_opacity(0.1, ft.Colors.ON_SURFACE)),
                        right=ft.BorderSide(1, ft.Colors.with_opacity(0.1, ft.Colors.ON_SURFACE)),
                    ),
                    border_radius=8,
                    padding=8,
                ),
            ],
            spacing=16,
        )

        if result.charset_size < 10:
            self._show_banner(self.weak_charset_banner)
        self.page.update()

    # -- validation ------------------------------------------------------

    def _parse_int(self, tf: ft.TextField, label: str, lo: int, hi: int) -> int:
        tf.error_text = None
        raw = (tf.value or "").strip()
        try:
            value = int(raw)
        except ValueError:
            tf.error_text = f"{label} must be a whole number."
            self.page.update()
            raise ValueError(f"{label} must be a whole number.") from None
        if value < lo or value > hi:
            tf.error_text = f"{label} must be between {lo} and {hi}."
            self.page.update()
            raise ValueError(f"{label} must be between {lo} and {hi}.")
        return value

    def _snack(self, message: str, error: bool = False) -> None:
        self.status_icon.name = ft.Icons.ERROR_ROUNDED if error else ft.Icons.CHECK_CIRCLE_ROUNDED
        self.status_icon.color = Palette.DANGER if error else Palette.ACCENT
        self.status_text.value = message
        self.status_banner.opacity = 1
        self.status_banner.scale = 1
        self.status_banner.offset = ft.Offset(0, 0)
        self.page.update()

        self._status_token += 1
        my_token = self._status_token
        try:
            asyncio.create_task(self._auto_hide_status(my_token))
        except RuntimeError:
            pass  # No running event loop (shouldn't normally happen) — toast just stays until manually closed.

    async def _auto_hide_status(self, token: int) -> None:
        await asyncio.sleep(2.5)
        if token == self._status_token:  # Only hide if no newer message has replaced this one.
            self._collapse_toast()

    def _hide_status(self, e: ft.ControlEvent) -> None:
        self._status_token += 1  # Invalidate any pending auto-hide for the current message.
        self._collapse_toast()

    def _collapse_toast(self) -> None:
        self.status_banner.opacity = 0
        self.status_banner.scale = 0.9
        self.status_banner.offset = ft.Offset(0, -0.15)
        self.page.update()

    def _set_busy(self, busy: bool) -> None:
        self.generate_btn.disabled = busy
        self.reset_btn.disabled = busy
        self.progress_bar.visible = busy
        if not busy:
            self.progress_bar.value = 0
        self.page.update()

    # -- event handlers ----------------------------------------------------

    async def on_generate(self, e: ft.ControlEvent) -> None:
        """Validate inputs, then generate passwords in yielding batches with progress."""
        if self._generating:
            # A prior click's coroutine hasn't finished yet — ignore this one.
            # Checked and set before any `await`, so it takes effect on the
            # very next click even if generate_btn.disabled hasn't visually
            # round-tripped to the client yet.
            return
        self._generating = True
        self._set_busy(True)
        try:
            try:
                count = self._parse_int(self.count_field, "Number of passwords", 1, MAX_COUNT)
                length = self._parse_int(self.length_field, "Length", 1, MAX_LENGTH)
                charset = PasswordGeneratorService.build_charset(
                    self.mode_group.value, self.custom_field.value or "", self.exclude_field.value or ""
                )
                words: list[str] = []
                if self.mode_group.value == "words":
                    words = PasswordGeneratorService.parse_words(self.words_field.value or "")
                    if not words:
                        raise ValueError("Enter at least one word to include.")
            except ValueError as ex:
                self._snack(str(ex), error=True)
                return

            passwords: list[str] = []
            batch = max(1, count // 20)
            for i in range(count):
                if words:
                    passwords.append(
                        PasswordGeneratorService.generate_password_with_words(length, charset, words)
                    )
                else:
                    passwords.append(PasswordGeneratorService.generate_password(length, charset))
                if i % batch == 0 or i == count - 1:
                    self.progress_bar.value = (i + 1) / count
                    self.page.update()
                    await asyncio.sleep(0)  # Yield to keep the UI responsive.

            if words:
                fill_length = length - sum(len(w) for w in words)
                # Conservative (lower-bound) entropy estimate: counts only the
                # randomly-filled characters, not the fixed words or their
                # placement, so reported strength never overstates what an
                # attacker actually has to guess.
                bits = PasswordGeneratorService.entropy_bits(fill_length, len(set(charset)))
                self.last_result = GenerationResult(
                    passwords=passwords, charset_size=len(set(charset)), length=length,
                    override_entropy_bits=bits,
                )
            else:
                self.last_result = GenerationResult(passwords=passwords, charset_size=len(set(charset)), length=length)
            self._render_results()
            self._snack(f"Generated {count} password{'s' if count != 1 else ''}.")
        except Exception as ex:  # Never let a raw traceback reach the user.
            self._snack(f"Generation failed: {ex}", error=True)
        finally:
            self._generating = False
            self._set_busy(False)

    def on_reset(self, e: ft.ControlEvent) -> None:
        self.count_field.value = str(DEFAULT_COUNT)
        self.length_field.value = str(DEFAULT_LENGTH)
        self.length_slider.value = DEFAULT_LENGTH
        self.mode_group.value = "default"
        self.custom_field.value = ""
        self.exclude_field.value = ""
        self.words_field.value = ""
        self.custom_field.visible = False
        self.exclude_field.visible = False
        self.words_field.visible = False
        self.preset_row.visible = False
        for name in self._preset_active:
            self._preset_active[name] = False
            self._update_preset_button_style(name)
        for f in (self.count_field, self.length_field, self.custom_field, self.exclude_field, self.words_field):
            f.error_text = None
        self.last_result = None
        self.progress_bar.value = 0
        self._render_results()
        self._snack("Inputs reset to defaults.")

    def on_clear_results(self, e: ft.ControlEvent) -> None:
        self.last_result = None
        self._render_results()

    def on_toggle_theme(self, e: ft.ControlEvent) -> None:
        page = self.page
        if page.theme_mode == ft.ThemeMode.DARK:
            page.theme_mode = ft.ThemeMode.LIGHT
            self.theme_icon.name = ft.Icons.DARK_MODE_OUTLINED
            self.theme_toggle_btn.tooltip = "Switch to dark theme"
        else:
            page.theme_mode = ft.ThemeMode.DARK
            self.theme_icon.name = ft.Icons.LIGHT_MODE_OUTLINED
            self.theme_toggle_btn.tooltip = "Switch to light theme"
        page.update()

    def switch_tab(self, index: int, e: ft.ControlEvent) -> None:
        if 0 <= index < len(self.tab_content_controls):
            self.tab_content_container.content = self.tab_content_controls[index]
            self.page.update()

    def _on_mode_change(self, e: Optional[ft.ControlEvent]) -> None:
        mode = self.mode_group.value
        self.exclude_field.visible = mode == "exclude"
        self.preset_row.visible = mode == "exclude"
        self.custom_field.visible = mode == "custom"
        self.words_field.visible = mode == "words"
        self.page.update()

    def _apply_preset(self, name: str, chars: str, e: ft.ControlEvent) -> None:
        self.mode_group.value = "exclude"
        self._on_mode_change(None)

        existing = set(self.exclude_field.value or "")
        is_active = self._preset_active.get(name, False)

        if is_active:
            # Turning OFF: remove only this preset's characters — but keep any
            # that another still-active preset also needs, so toggling one
            # pill off never disturbs another pill that's still on.
            chars_to_remove = set(chars)
            for other_name, other_active in self._preset_active.items():
                if other_name != name and other_active:
                    chars_to_remove -= set(EXCLUSION_PRESETS[other_name])
            existing -= chars_to_remove
            self._preset_active[name] = False
        else:
            # Turning ON: add this preset's characters on top of whatever is
            # already there (manual typing or other active presets).
            existing.update(chars)
            self._preset_active[name] = True

        self.exclude_field.value = "".join(sorted(existing))
        self._update_preset_button_style(name)
        self.page.update()

    def _update_preset_button_style(self, name: str) -> None:
        """Reflect a preset's on/off state purely through its button style —
        accent border/tint/text when active, neutral outline when not."""
        btn = self.preset_buttons.get(name)
        if btn is None:
            return
        active = self._preset_active.get(name, False)
        btn.style = self._preset_pill_style(active)
        btn.tooltip = f"{name} — click to disable" if active else f"{name} — click to enable"

    def _on_length_slider_change(self, e: ft.ControlEvent) -> None:
        self.length_field.value = str(int(self.length_slider.value))
        self.length_field.error_text = None
        self.page.update()

    def _on_length_field_change(self, e: ft.ControlEvent) -> None:
        try:
            v = int(self.length_field.value)
            if 1 <= v <= 128:
                self.length_slider.value = v
        except ValueError:
            pass
        self.page.update()

    def _set_length_preset(self, value: int, e: ft.ControlEvent) -> None:
        self.length_field.value = str(value)
        self.length_slider.value = min(value, 128)
        self.length_field.error_text = None
        self.page.update()

    def _adjust_count(self, delta: int, e: ft.ControlEvent) -> None:
        try:
            v = int(self.count_field.value)
        except ValueError:
            v = DEFAULT_COUNT
        v = max(1, min(MAX_COUNT, v + delta))
        self.count_field.value = str(v)
        self.count_field.error_text = None
        self.page.update()

    async def _copy_one(self, pw: str, e: ft.ControlEvent) -> None:
        await self._copy_to_clipboard(pw)
        self._snack("Password copied to clipboard.")

    async def on_copy_all(self, e: ft.ControlEvent) -> None:
        if not self.last_result or not self.last_result.passwords:
            self._snack("Nothing to copy yet.", error=True)
            return
        all_passwords = "\n".join(self.last_result.passwords)
        await self._copy_to_clipboard(all_passwords)
        self._snack(f"{len(self.last_result.passwords)} passwords copied to clipboard.")

    def on_export_click(self, e: ft.ControlEvent) -> None:
        if not self.last_result or not self.last_result.passwords:
            self._snack("Generate passwords before exporting.", error=True)
            return
        fmt = self.export_format.value or "txt"
        downloads_dir = os.path.join(os.path.expanduser("~"), "Downloads")
        target_dir = downloads_dir if os.path.isdir(downloads_dir) else os.path.expanduser("~")
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        self.export_path_field.value = os.path.join(target_dir, f"passwords_{timestamp}.{fmt}")
        self.export_path_field.error_text = None
        self._open_ctl(self.export_dialog)

    async def _browse_export_path(self, e: ft.ControlEvent) -> None:
        fmt = self.export_format.value or "txt"
        current = (self.export_path_field.value or "").strip()
        initial_dir = os.path.dirname(current) if current else os.path.join(os.path.expanduser("~"), "Downloads")
        if not os.path.isdir(initial_dir):
            initial_dir = os.path.expanduser("~")
        initial_file = os.path.basename(current) if current else f"passwords.{fmt}"

        loop = asyncio.get_running_loop()
        try:
            result_path = await loop.run_in_executor(
                self._tk_executor, self._native_save_dialog, initial_dir, initial_file, fmt
            )
            if result_path:
                self.export_path_field.value = result_path
                self.export_path_field.error_text = None
                self.page.update()
        except Exception as ex:
            # Native dialog isn't available on this machine — the path field is
            # still right there for typing/pasting a location manually.
            self.export_path_field.error_text = f"Native picker unavailable ({ex}); type or paste a path instead."
            self.page.update()

    @staticmethod
    def _native_save_dialog(initial_dir: str, initial_file: str, fmt: str) -> str:
        """Open the OS's actual native Save-file dialog via tkinter.

        Runs off the Flet event loop (called through run_in_executor) since
        this is a blocking call until the user closes the dialog. tkinter
        ships with the standard Python installer on Windows/macOS, so this
        works without depending on Flet's own (currently broken) FilePicker.
        """
        import tkinter as tk
        from tkinter import filedialog

        root = tk.Tk()
        root.withdraw()
        root.attributes("-topmost", True)
        try:
            path = filedialog.asksaveasfilename(
                title="Save passwords",
                initialdir=initial_dir,
                initialfile=initial_file,
                defaultextension=f".{fmt}",
                filetypes=[(fmt.upper(), f"*.{fmt}"), ("All files", "*.*")],
            )
        finally:
            root.destroy()
        return path

    def _close_export_dialog(self, e: ft.ControlEvent) -> None:
        self._close_ctl(self.export_dialog)

    def _do_export(self, e: ft.ControlEvent) -> None:
        if not self.last_result or not self.last_result.passwords:
            self._close_ctl(self.export_dialog)
            return
        path = (self.export_path_field.value or "").strip()
        if not path:
            self.export_path_field.error_text = "Enter a file path."
            self.page.update()
            return

        fmt = self.export_format.value or "txt"
        serializer = {
            "txt": PasswordGeneratorService.to_txt,
            "csv": PasswordGeneratorService.to_csv,
            "json": PasswordGeneratorService.to_json,
        }[fmt]
        content = serializer(self.last_result.passwords)

        try:
            parent = os.path.dirname(path)
            if parent:
                os.makedirs(parent, exist_ok=True)
            with open(path, "w", encoding="utf-8", newline="") as f:
                f.write(content)
            self._close_ctl(self.export_dialog)
            self._snack(f"Saved to {path}")
        except Exception as ex:
            self.export_path_field.error_text = str(ex)
            self.page.update()


def main(page: ft.Page) -> None:
    """Flet entry point — wires up and builds the Cipher UI on the given page."""
    CipherApp(page).build()

if __name__ == "__main__":
    ft.run(main)