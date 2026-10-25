# -*- coding: utf-8 -*-
"""ОБРЕЗОК by RomixERR — кропер изображений.

Что появилось в этой версии:
  1. Фиксированные разрешения 1536x1536 и 640x640 добавлены в меню.
  2. Меню «Масштаб исходника»: рабочий вариант картинки 1024 / 1536 / 1920 / 3072
     по большей или по меньшей стороне (пропорции сохраняются). Все дальнейшие
     действия (зум, кроп, маска) идут уже по рабочему изображению.
  3. Меню «Кратность кропа»: 1 (свободно), 2, 4, 8, 16, 32, 64. Прямоугольник
     ходит рывками по сетке кратности, а сохраняется ровно по области кропа.
  4. Сохранение по Ctrl+S (и Ctrl+O — открыть).
  5. Режим «Сохранять только маску кропа (ЧБ)»: чёрное поле рабочего разрешения
     с белым прямоугольником выделенной области.
  6. Сохранение в отдельную папку (выбирается через меню).

Дополнительно доработан зум и отображение:
  - рисуется только видимая область изображения (плюс запас на панораму), поэтому
    зум не зависит от размера файла и «Zoom 1:1» действительно работает;
  - колесо якорится под курсором, шаг стал мельче (х1.15, с Ctrl — х1.5), перерисовка
    колеса и панорамы дебаунсится;
  - панорама средней кнопкой мыши, стрелками (Shift — крупный), а также правой
    кнопкой вне рамки; правая кнопка внутри рамки переносит выделение;
  - выделение хранится в пикселях рабочего изображения и переживает зум, панораму,
    смену масштаба, поворот и изменение размера окна.
"""

import math
import os
import re
import tkinter as tk
from tkinter import filedialog, messagebox

from PIL import Image, ImageDraw, ImageOps, ImageTk

try:
    from tkinterdnd2 import TkinterDnD, DND_FILES
    HAS_DND = True
except ImportError:  # drag-n-drop необязателен: без него программа работает
    HAS_DND = False
    TkinterDnD = None
    DND_FILES = None


# --- настройки меню ---------------------------------------------------------
FIXED_RESOLUTIONS = (1536, 1024, 768, 640, 512)   # квадратные фикс. разрешения
SCALE_TARGETS = (1024, 1536, 1920, 3072)          # масштаб рабочего изображения
SNAP_STEPS = (1, 2, 4, 8, 16, 32, 64)             # кратность сторон кропа

MIN_ZOOM = 0.05           # относительные пределы зума (от «вписать в окно»)
MAX_ZOOM = 8.0
MIN_SCALE = 0.02          # абсолютные пределы: экранных пикселей на пиксель изображения
MAX_SCALE = 8.0
ZOOM_STEP = 1.15          # один щелчок колеса
ZOOM_STEP_FAST = 1.5      # щелчок колеса с Ctrl
PAN_KEY_STEP = 20         # стрелки
PAN_KEY_STEP_FAST = 100   # стрелки с Shift

MAX_UPSCALE = 8.0            # во сколько раз разрешаем увеличить исходник
MAX_WORKING_PIXELS = 30000000   # потолок рабочего изображения, чтобы не съесть память

VIEW_PAD_PX = 300              # сколько экранной области рендерим в запас для панорамы
MAX_DISPLAY_SIDE = 8000        # потолок bitmap'а на канвасе
MAX_DISPLAY_PIXELS = 6000000

EDGE_MARGIN = 80               # сколько пикселей изображения обязан оставлять сдвиг

REDUCE_MODES = ("L", "LA", "I", "RGB", "RGBA", "RGBX", "CMYK", "YCbCr", "F", "HSV")
# Image.reduce() в Pillow 9.5 не умеет режимы "1", "P" и "I;16" — для них обычный resize
JPEG_EXT = (".jpg", ".jpeg")


class CropImageApp:
    def __init__(self, root):
        self.root = root
        self.root.title("ОБРЕЗОК by RomixERR")
        self.root.geometry("1000x760")

        # --- режимы
        self.square_crop = tk.BooleanVar(value=False)          # фиксировать квадрат
        self.fixed_resolution_crop = tk.BooleanVar(value=False)  # фиксированное разрешение
        self.fixed_res_var = tk.IntVar(value=1024)
        self.snap_var = tk.IntVar(value=1)                     # кратность кропа
        self.scale_var = tk.StringVar(value="none")            # масштаб исходника
        self.version_index_save = tk.BooleanVar(value=True)    # версии в разные файлы
        self.custom_dir_save = tk.BooleanVar(value=False)      # сохранять в отдельную папку
        self.mask_only_save = tk.BooleanVar(value=False)       # сохранять только ЧБ-маску

        self.fixed_width = 1024
        self.fixed_height = 1024
        self.save_dir = ""

        # --- изображения
        self.source_image = None      # то, что загрузили (целиком, в памяти)
        self.image = None             # рабочий вариант (после масштабирования)
        self.image_path = None
        self.scale_factor = 1.0       # k = рабочий / исходный
        self.scale_mode = "none"      # "long" / "short" / "none"
        self.scale_target = None
        self.scale_clamped = False    # масштаб пришлось ограничить
        self.fixed_fits = True        # влезает ли фикс. разрешение в рабочий размер

        # --- отображение
        self.zoom_factor = 1.0        # 1.0 = изображение целиком в окне
        self.scale_ratio = 1.0        # экраннных пикселей на пиксель рабочего изображения
        self.zoom_shift_x = 0.0
        self.zoom_shift_y = 0.0
        self.tk_image = None
        self._last_canvas = (1, 1)
        self._render_job = None
        self._pending_render = None
        self._resize_job = None

        # --- выделение (всегда в пикселях рабочего изображения)
        self.crop_box = None          # (x1, y1, x2, y2), x2>x1, y2>y1
        self.drag_origin = None       # точка старта выделения, не меняется во время драга
        self.move_anchor = None       # для перетаскивания рамки правой кнопкой
        self.move_box0 = None
        self.pan_last = None
        self._rotate_dir = None       # "cw" / "ccw": как перенести выделение при повороте

        self.rect = None
        self.size_text = None
        self.base_status = ""
        self._dialog_open = False

        self._build_ui()
        self._update_status("Перетащите картинку в окно или откройте её через меню Open Image.")

    # ====================================================================== UI
    def _build_ui(self):
        self.status = tk.Label(self.root, anchor="w", justify="left",
                               text="", font=("Arial", 9), bg="#202020", fg="#e0e0e0",
                               padx=8, pady=4)
        self.status.pack(side="bottom", fill="x")

        self.canvas = tk.Canvas(self.root, cursor="cross", bg="gray", highlightthickness=0)
        self.canvas.pack(fill="both", expand=True)

        if HAS_DND:
            try:
                self.canvas.drop_target_register(DND_FILES)
                self.canvas.dnd_bind("<<Drop>>", self.on_drop)
            except Exception:
                # окно не TkinterDnD.Tk() (или tkdnd не загрузился) — drag-n-drop недоступен,
                # остальное работает
                pass

        menu = tk.Menu(self.root)
        self.root.config(menu=menu)

        menu.add_command(label="Open Image", command=self.open_image, accelerator="Ctrl+O")

        options = tk.Menu(menu, tearoff=0)

        options.add_checkbutton(label="Фиксировать квадрат", onvalue=True, offvalue=False,
                                variable=self.square_crop, command=self._on_mode_change)

        resolution_menu = tk.Menu(options, tearoff=0)
        for size in FIXED_RESOLUTIONS:
            resolution_menu.add_radiobutton(
                label="%d x %d" % (size, size),
                value=size, variable=self.fixed_res_var,
                command=lambda s=size: self.set_fixed_resolution(s, s))
        options.add_checkbutton(label="Фиксировать разрешение", onvalue=True, offvalue=False,
                                variable=self.fixed_resolution_crop, command=self._on_mode_change)
        options.add_cascade(label="Выбрать разрешение", menu=resolution_menu)

        # кратность кропа
        snap_menu = tk.Menu(options, tearoff=0)
        for step in SNAP_STEPS:
            label = "1 — без кратности (свободно)" if step == 1 else str(step)
            snap_menu.add_radiobutton(label=label, value=step, variable=self.snap_var,
                                      command=self._on_snap_change)
        options.add_cascade(label="Кратность кропа", menu=snap_menu)

        # масштаб исходного изображения
        scale_menu = tk.Menu(options, tearoff=0)
        scale_menu.add_radiobutton(label="Оригинал (без масштабирования)",
                                   value="none", variable=self.scale_var,
                                   command=self._on_scale_change)
        scale_menu.add_separator()
        long_menu = tk.Menu(scale_menu, tearoff=0)
        for target in SCALE_TARGETS:
            long_menu.add_radiobutton(label=str(target), value="long:%d" % target,
                                      variable=self.scale_var, command=self._on_scale_change)
        scale_menu.add_cascade(label="По большей стороне", menu=long_menu)
        short_menu = tk.Menu(scale_menu, tearoff=0)
        for target in SCALE_TARGETS:
            short_menu.add_radiobutton(label=str(target), value="short:%d" % target,
                                       variable=self.scale_var, command=self._on_scale_change)
        scale_menu.add_cascade(label="По меньшей стороне", menu=short_menu)
        options.add_cascade(label="Масштаб исходника", menu=scale_menu)

        options.add_separator()
        options.add_command(label="Zoom reset (вписать в окно)", command=self.reset_zoom,
                            accelerator="0")
        options.add_command(label="Zoom 1:1 (пиксель в пиксель)", command=self.zoom_one_to_one)
        options.add_command(label="Повернуть 90° вправо (по часовой)",
                            command=lambda: self.rotate_image("cw"))
        options.add_command(label="Повернуть 90° влево (против часовой)",
                            command=lambda: self.rotate_image("ccw"))

        options.add_separator()
        options.add_checkbutton(label="Сохранять новые версии в разные файлы",
                                onvalue=True, offvalue=False, variable=self.version_index_save)
        options.add_checkbutton(label="Сохранять в отдельную папку",
                                onvalue=True, offvalue=False, variable=self.custom_dir_save,
                                command=self._update_status_only)
        options.add_command(label="Выбрать папку для сохранения…", command=self.choose_save_dir)
        options.add_checkbutton(label="Сохранять только маску кропа (ЧБ)",
                                onvalue=True, offvalue=False, variable=self.mask_only_save,
                                command=self._update_status_only)

        menu.add_cascade(label="Опции", menu=options)
        menu.add_command(label="Save", command=self.save_cropped_image, accelerator="Ctrl+S")
        menu.add_command(label="Справка", command=self.show_help)

        # события канваса
        self.canvas.bind("<ButtonPress-1>", self.on_button_press_1)
        self.canvas.bind("<B1-Motion>", self.on_mouse_drag_1)
        self.canvas.bind("<ButtonRelease-1>", self.on_button_release_1)
        self.canvas.bind("<ButtonPress-3>", self.on_button_press_3)
        self.canvas.bind("<B3-Motion>", self.on_mouse_drag_3)
        self.canvas.bind("<ButtonRelease-3>", self.on_button_release_3)
        self.canvas.bind("<ButtonPress-2>", self.on_button_press_2)
        self.canvas.bind("<B2-Motion>", self.on_mouse_drag_2)
        self.canvas.bind("<ButtonRelease-2>", self.on_button_release_2)
        self.canvas.bind("<MouseWheel>", self.on_mouse_wheel)      # Windows / macOS
        self.canvas.bind("<Button-4>", self.on_mouse_wheel)        # Linux scroll up
        self.canvas.bind("<Button-5>", self.on_mouse_wheel)        # Linux scroll down
        self.canvas.bind("<Configure>", self.on_canvas_resize)

        # горячие клавиши
        self._safe_bind("<Control-s>", lambda e: self.save_cropped_image())
        self._safe_bind("<Control-S>", lambda e: self.save_cropped_image())
        self._safe_bind("<Control-o>", lambda e: self.open_image())
        self._safe_bind("<Key-0>", lambda e: self.reset_zoom())
        self._safe_bind("<Key-KP_0>", lambda e: self.reset_zoom())
        self._safe_bind("<Key-Escape>", lambda e: self.clear_selection())
        for key in ("plus", "equal", "KP_Add"):
            self._safe_bind("<Key-%s>" % key, lambda e: self._zoom_by_keys(ZOOM_STEP))
        for key in ("minus", "underscore", "KP_Subtract"):
            self._safe_bind("<Key-%s>" % key, lambda e: self._zoom_by_keys(1.0 / ZOOM_STEP))
        for key in ("Left", "Right", "Up", "Down"):
            self._safe_bind("<Key-%s>" % key, self._on_arrow_key)

        # кнопку могли отпустить вне канваса (в диалоге, меню, статусной строке) —
        # состояние перетаскивания не должно оставаться «висящим»
        for button in (1, 2, 3):
            self._safe_bind("<ButtonRelease-%d>" % button, self._on_global_button_release)

    def _on_global_button_release(self, event):
        if getattr(event, "widget", None) is self.canvas:
            return                      # канвас уже всё обработал своими обработчиками
        if self.drag_origin is None and self.move_box0 is None and self.pan_last is None:
            return
        self._reset_drag_state()
        if self.crop_box:
            x1, y1, x2, y2 = self.crop_box
            if x2 - x1 < 1 or y2 - y1 < 1:
                self.crop_box = None
        self._redraw_selection_now()
        self._update_status_only()

    def _safe_bind(self, sequence, handler):
        """Не все keysym есть во всех сборках Tk, поэтому привязку оборачиваем в try."""
        try:
            self.root.bind_all(sequence, handler)
        except tk.TclError:
            pass

    # ================================================================= изображения
    def open_image(self):
        if self._dialog_open:
            return
        self._reset_drag_state()
        self._dialog_open = True
        try:
            path = filedialog.askopenfilename(
                title="Открыть изображение",
                filetypes=[("Image files", "*.jpg;*.jpeg;*.png;*.bmp;*.gif;*.tif;*.tiff;*.webp")]
            )
        finally:
            self._dialog_open = False
        if path:
            self.load_image(path)

    def load_image(self, file_path):
        try:
            with Image.open(file_path) as opened:
                opened.load()
                image = ImageOps.exif_transpose(opened)   # фото с EXIF-поворотом видим как в просмотрщике
                image = image.copy()                       # отвязываем данные от файла (Windows его держит)
        except Exception as exc:
            self._set_status("Не удалось открыть файл: %s" % exc)
            return
        self.source_image = image
        self.image_path = file_path
        self._reset_drag_state()
        self.crop_box = None
        self._rebuild_working_image()
        self._set_status("Загружено: %s" % os.path.basename(file_path))

    def _rebuild_working_image(self, center_norm=None):
        """Пересчитывает рабочий image из source_image по выбранному масштабу.

        center_norm — нормированная точка изображения (0..1), которую после пересчёта
        нужно оставить в центре окна; None — вписать изображение в окно целиком.
        """
        if self.source_image is None:
            return

        source_w, source_h = self.source_image.size
        old_box = self.crop_box
        old_size = self.image.size if self.image is not None else None
        rotate_dir = self._rotate_dir
        self._rotate_dir = None

        value = self.scale_var.get()
        self.scale_clamped = False
        if value == "none":
            self.image = self.source_image
            self.scale_factor = 1.0
            self.scale_mode = "none"
            self.scale_target = None
        else:
            mode, target = value.split(":")
            target = int(target)
            base = max(source_w, source_h) if mode == "long" else min(source_w, source_h)
            k = target / float(base)
            # страховка от раздувания: ограничение на апскейл и на общее число пикселей
            if k > MAX_UPSCALE:
                k = MAX_UPSCALE
                self.scale_clamped = True
            if source_w * source_h * k * k > MAX_WORKING_PIXELS:
                k = math.sqrt(MAX_WORKING_PIXELS / float(source_w * source_h))
                self.scale_clamped = True
            new_w = max(1, int(round(source_w * k)))
            new_h = max(1, int(round(source_h * k)))
            resample = Image.Resampling.LANCZOS if k < 1.0 else Image.Resampling.BICUBIC
            self.image = self._safe_resize(self.source_image, (new_w, new_h), resample)
            self.scale_factor = k
            self.scale_mode = mode
            self.scale_target = target

        # старое выделение переносим в новые координаты (с учётом поворота)
        if old_box and old_size:
            step = self._effective_step()          # сетка может быть больше картинки
            new_w, new_h = self.image.size
            ow, oh = old_size
            x1, y1, x2, y2 = old_box
            nx1, ny1, nx2, ny2 = x1, y1, x2, y2
            if rotate_dir == "cw":       # по часовой: (x, y) -> (1 - y/oh, x/ow) в нормированных координатах
                nx1, ny1, nx2, ny2 = (1.0 - y2 / float(oh)) * new_w, x1 * new_h / float(ow), \
                                     (1.0 - y1 / float(oh)) * new_w, x2 * new_h / float(ow)
            elif rotate_dir == "ccw":    # против часовой: (x, y) -> (y/oh, 1 - x/ow)
                nx1, ny1, nx2, ny2 = y1 * new_w / float(oh), (1.0 - x2 / float(ow)) * new_h, \
                                     y2 * new_w / float(oh), (1.0 - x1 / float(ow)) * new_h
            else:
                nx1 = x1 * new_w / float(ow)
                ny1 = y1 * new_h / float(oh)
                nx2 = x2 * new_w / float(ow)
                ny2 = y2 * new_h / float(oh)
            self.crop_box = self._norm_box(
                self._snap_range(nx1, step, 0, new_w), self._snap_range(ny1, step, 0, new_h),
                self._snap_range(nx2, step, 0, new_w), self._snap_range(ny2, step, 0, new_h))
            # смена масштаба не должна молча ломать фиксированное разрешение
            self.crop_box = self._reapply_fixed_size(self.crop_box)

        if center_norm is not None and self.image is not None:
            new_w, new_h = self.image.size
            cx, cy = center_norm                   # точка на СТАРОМ изображении (0..1)
            if rotate_dir == "cw":
                cx, cy = 1.0 - cy, cx
            elif rotate_dir == "ccw":
                cx, cy = cy, 1.0 - cx
            self._render(anchor_image=(cx * new_w, cy * new_h))
        else:
            self._render(center=True)

    def _view_center_norm(self):
        """Нормированные координаты (0..1) точки рабочего изображения в центре окна."""
        if self.image is None or self.scale_ratio <= 0:
            return None
        cw = max(1, self.canvas.winfo_width())
        ch = max(1, self.canvas.winfo_height())
        point_x, point_y = self._canvas_to_image(cw / 2.0, ch / 2.0)
        w, h = self.image.size
        return (min(max(point_x / float(w), 0.0), 1.0),
                min(max(point_y / float(h), 0.0), 1.0))

    def _keep_view_after_rebuild(self):
        """Точка, бывшая в центре окна, должна остаться в центре после пересбора изображения."""
        center_norm = self._view_center_norm()
        self._rebuild_working_image(center_norm=center_norm)

    def rotate_image(self, direction="cw"):
        if self.source_image is None or self._dialog_open:
            return
        angle = -90 if direction == "cw" else 90
        try:
            rotated = self.source_image.rotate(angle, expand=True, resample=Image.Resampling.BICUBIC)
        except Exception as exc:
            self._set_status("Поворот недоступен для этого файла: %s" % exc)
            return
        self.source_image = rotated
        self._rotate_dir = direction
        self._reset_drag_state()
        self._keep_view_after_rebuild()
        self._set_status("Изображение повёрнуто %s." % ("по часовой" if direction == "cw" else "против часовой"))

    # ============================================================ modes / menu cb
    def set_fixed_resolution(self, width, height):
        self.fixed_width = width
        self.fixed_height = height
        self.fixed_resolution_crop.set(True)
        self._on_mode_change()

    def _fixed_block_size(self, step=None):
        """Реальный размер фикс-блока: с учётом границ изображения и сетки кратности.

        Единственный источник правды — по нему и рисуется рамка, и сохраняется файл.
        """
        step = self._effective_step() if step is None else step
        img_w, img_h = self.image.size
        fw, fh = self.fixed_width, self.fixed_height
        if fw > img_w or fh > img_h:
            fw, fh = min(fw, img_w), min(fh, img_h)
        if self.square_crop.get():                 # квадрат важнее: обе стороны равны
            fw = fh = min(fw, fh)
        if step > 1:
            # стороны обязаны лежать на сетке, иначе границы блока не сойдутся с _snap_range
            fw = max(step, (fw // step) * step)
            fh = max(step, (fh // step) * step)
        return int(fw), int(fh)

    def _reapply_fixed_size(self, box, announce=True):
        """Выделение должно быть ровно выбранным фиксированным разрешением (с поправкой на
        границы изображения и сетку), а не тем размером, который остался после поворота,
        смены масштаба или выбора другого разрешения."""
        if not box or not self.fixed_resolution_crop.get() or self.image is None:
            return box
        step = self._effective_step()
        img_w, img_h = self.image.size
        fw, fh = self._fixed_block_size(step)
        x1 = self._snap_range(box[0], step, 0, max(0, img_w - fw))
        y1 = self._snap_range(box[1], step, 0, max(0, img_h - fh))
        new_box = self._norm_box(x1, y1, x1 + fw, y1 + fh)
        if announce and new_box != box:
            self._set_status("Выделение приведено к фиксированному разрешению %dx%d." % (fw, fh))
        return new_box

    def _on_mode_change(self):
        self._check_fixed_fits()
        if self.crop_box:
            self.crop_box = self._reapply_fixed_size(self.crop_box)
            self._redraw_selection_now()
        self._update_status_only()

    def _effective_step(self):
        """Сетка крупнее самой картинки бессмысленна — считаем шаг равным 1."""
        step = self.snap_var.get()
        if step > 1 and self.image is not None and step > min(self.image.size):
            return 1
        return step

    def _on_snap_change(self):
        step = self._effective_step()
        if step != self.snap_var.get():
            self._set_status("Кратность %d больше размера изображения — кроп свободный." % self.snap_var.get())
        elif self.crop_box:
            # существующее выделение приводим к новой сетке
            w, h = self.image.size
            x1, y1, x2, y2 = self.crop_box
            snapped = self._norm_box(
                self._snap_range(x1, step, 0, w), self._snap_range(y1, step, 0, h),
                self._snap_range(x2, step, 0, w), self._snap_range(y2, step, 0, h))
            snapped = self._reapply_fixed_size(snapped)
            if snapped != self.crop_box:
                self.crop_box = snapped
                if self.fixed_resolution_crop.get():
                    self._set_status("Выделение подогнано под сетку %d." % step)
                else:
                    self._set_status("Выделение подогнано под кратность %d." % step)
        self._redraw_selection_now()
        self._update_status_only()

    def _on_scale_change(self):
        self._keep_view_after_rebuild()
        if self.scale_clamped:
            self._set_status("Масштаб ограничен (k=%.4f), чтобы изображение не раздувалось." % self.scale_factor)
        else:
            self._update_status_only()

    def choose_save_dir(self):
        if self._dialog_open:
            return
        self._reset_drag_state()
        self._dialog_open = True
        try:
            folder = filedialog.askdirectory(title="Папка для сохранения")
        finally:
            self._dialog_open = False
        if folder:
            self.save_dir = os.path.normpath(folder)
            self.custom_dir_save.set(True)
            try:
                os.makedirs(self.save_dir, exist_ok=True)
            except OSError:
                pass
            self._set_status("Папка для сохранения: %s" % self.save_dir)

    def clear_selection(self):
        if self._dialog_open:
            return
        self._reset_drag_state()
        self.crop_box = None
        self._redraw_selection_now()
        self._update_status_only()

    def _reset_drag_state(self):
        self.drag_origin = None
        self.move_anchor = None
        self.move_box0 = None
        self.pan_last = None

    # =========================================================== геометрия/отрисовка
    def _canvas_to_image(self, x, y):
        return ((x - self.zoom_shift_x) / self.scale_ratio,
                (y - self.zoom_shift_y) / self.scale_ratio)

    def _image_to_canvas(self, x, y):
        return (x * self.scale_ratio + self.zoom_shift_x,
                y * self.scale_ratio + self.zoom_shift_y)

    @staticmethod
    def _norm_box(x1, y1, x2, y2):
        if x2 < x1:
            x1, x2 = x2, x1
        if y2 < y1:
            y1, y2 = y2, y1
        return (int(x1), int(y1), int(x2), int(y2))

    @staticmethod
    def _snap_range(value, step, lo, hi):
        """Ближайшее значение, кратное step, в границах [lo, hi]."""
        if hi < lo:
            hi = lo
        if step <= 1:
            return int(max(lo, min(int(math.floor(value + 0.5)), hi)))
        first = -(-int(lo) // step)                 # ceil(lo / step)
        last = int(hi) // step                       # floor(hi / step)
        k = int(math.floor(value / step + 0.5))
        if k < first:
            k = first
        if k > last:
            k = last
        # интервал может не содержать ни одного кратного шага (например lo=1500, hi=1500, step=64)
        return int(max(lo, min(k * step, hi)))

    def _check_fixed_fits(self):
        if self.image is None:
            self.fixed_fits = True
            return
        w, h = self.image.size
        self.fixed_fits = (self.fixed_width <= w and self.fixed_height <= h)

    def _fit_ratio(self):
        cw = max(1, self.canvas.winfo_width())
        ch = max(1, self.canvas.winfo_height())
        w, h = self.image.size
        return min(cw / float(w), ch / float(h))

    def _view_pad(self, canvas_w, canvas_h):
        """Запас экранной области вокруг видимой (чтобы панорама не показывала пустоту).

        Потолок относится к bitmap'у целиком — видимая область плюс запас: запас не обнуляем
        разом, а уменьшаем ровно настолько, чтобы (ширина + 2*pad) * (высота + 2*pad) уложился
        в потолок. Если уже одна видимая область больше потолка (огромное окно вроде 4K),
        pad = 0: саму видимую область урезать нельзя, иначе в окне нечего будет рисовать.
        """
        area = canvas_w * canvas_h
        longest = max(canvas_w, canvas_h)
        if area >= MAX_DISPLAY_PIXELS or longest >= MAX_DISPLAY_SIDE:
            return 0
        side_room = (MAX_DISPLAY_SIDE - longest) / 2.0
        # (w + 2p)(h + 2p) <= MAX_DISPLAY_PIXELS  ->  4p^2 + 2(w+h)p + (area - MAX) <= 0
        total = canvas_w + canvas_h
        area_room = (-total + math.sqrt(total * total + 4.0 * (MAX_DISPLAY_PIXELS - area))) / 4.0
        return int(max(0, min(VIEW_PAD_PX, side_room, area_room)))

    @staticmethod
    def _safe_resize(im, size, resample):
        """resize() не тянет некоторые режимы (например I;16) — переводим в L и пробуем снова."""
        try:
            return im.resize(size, resample)
        except ValueError:
            try:
                return im.convert("L").resize(size, resample)
            except ValueError:
                return im.convert("RGB").resize(size, resample)

    def _display_image(self, src, target_w, target_h):
        """Быстро приводит область рабочего image к размеру отображения."""
        w, h = src.size
        if target_w >= w and target_h >= h:
            return self._safe_resize(src, (target_w, target_h), Image.Resampling.LANCZOS)
        # уменьшение: сначала дешёвое целочисленное усреднение, затем качественный resize
        k = int(min(w / float(target_w), h / float(target_h)))
        if k > 1 and src.mode in REDUCE_MODES:
            base = src.reduce(k)
            resample = Image.Resampling.BILINEAR
        else:                       # reduce не умеет работать с частью режимов
            base = src
            resample = Image.Resampling.LANCZOS
        return self._safe_resize(base, (target_w, target_h), resample)

    def _visible_region(self, canvas_w, canvas_h):
        """Область рабочего изображения, которую надо отрисовать (видимое + запас)."""
        img_w, img_h = self.image.size
        scale = self.scale_ratio
        pad = self._view_pad(canvas_w, canvas_h)

        left = self.zoom_shift_x
        top = self.zoom_shift_y
        right = self.zoom_shift_x + img_w * scale
        bottom = self.zoom_shift_y + img_h * scale

        cx0 = max(left, -pad)
        cx1 = min(right, canvas_w + pad)
        cy0 = max(top, -pad)
        cy1 = min(bottom, canvas_h + pad)
        if cx1 <= cx0 or cy1 <= cy0:
            return None

        ix0 = max(0, int(math.floor((cx0 - left) / scale)))
        iy0 = max(0, int(math.floor((cy0 - top) / scale)))
        ix1 = min(img_w, int(math.ceil((cx1 - left) / scale)))
        iy1 = min(img_h, int(math.ceil((cy1 - top) / scale)))
        if ix1 <= ix0 or iy1 <= iy0:
            return None

        disp_w = max(1, int(round((ix1 - ix0) * scale)))
        disp_h = max(1, int(round((iy1 - iy0) * scale)))
        return (ix0, iy0, ix1, iy1), disp_w, disp_h, left + ix0 * scale, top + iy0 * scale

    def _scale_limits(self, fit):
        """Границы масштаба: абсолютные (экр. пикселей на пиксель) и относительные (от «вписать»).

        Относительные границы нужны, чтобы мелкую картинку можно было разглядеть,
        абсолютные — чтобы «1:1» был достижим всегда.
        """
        lo = min(MIN_SCALE, MIN_ZOOM * fit)
        hi = max(MAX_SCALE, MAX_ZOOM * fit, fit)
        return lo, hi

    def _cancel_pending_render(self):
        """Прямой вызов _render отменяет отложенный — иначе через 250 мс будет вторая перерисовка."""
        if self._render_job is not None:
            try:
                self.root.after_cancel(self._render_job)
            except (ValueError, tk.TclError):
                pass
            self._render_job = None
        self._pending_render = None

    def _resize_anchor(self):
        """Точку чего держим в центре окна после изменения его размера.

        Берём центр пересечения прежнего окна с изображением: если центр окна смотрел
        «в пустоту» (панорама законно ушла к краю картинки), ничего не «догадываем» —
        держим ровно тот кусок картинки, который и так был виден, и не телепортируем вид
        к границе изображения. None — картинка в окно не попадала вовсе: вид не трогаем.
        """
        old_w, old_h = self._last_canvas
        img_w, img_h = self.image.size
        left, top = self.zoom_shift_x, self.zoom_shift_y
        right, bottom = left + img_w * self.scale_ratio, top + img_h * self.scale_ratio
        x0, x1 = max(left, 0.0), min(right, float(old_w))
        y0, y1 = max(top, 0.0), min(bottom, float(old_h))
        if x1 <= x0 or y1 <= y0:
            return None
        return self._canvas_to_image((x0 + x1) / 2.0, (y0 + y1) / 2.0)

    def _render(self, anchor=None, anchor_image=None, center=False, scale=None):
        """Перерисовывает видимую область рабочего изображения.

        scale        — задать новый абсолютный масштаб;
        center       — вписать изображение в окно (загрузка, сброс зума);
        anchor_image — точка изображения, которую ставим в центр окна (ресайз, смена масштаба);
        anchor       — точка канваса, под которой обязана остаться та же точка изображения (зум);
        ничего не передано — вид не трогаем, пересобираем только bitmap (панорама).

        Масштаб живёт в self.scale_ratio: сколько экранных пикселей на пиксель изображения.
        Он не зависит от размера окна, поэтому «1:1» остаётся 1:1 после ресайза, поворота
        и смены масштаба. self.zoom_factor — производная величина (в процентах от «вписать»),
        нужна только для показа в статусе.
        """
        if self.image is None:
            return

        self._cancel_pending_render()

        cw = max(1, self.canvas.winfo_width())
        ch = max(1, self.canvas.winfo_height())
        img_w, img_h = self.image.size

        old_scale = self.scale_ratio if self.scale_ratio > 0 else self._fit_ratio()

        if anchor is None and anchor_image is None and not center and self._last_canvas != (cw, ch):
            # окно изменили, а отложенная перерисовка (панорама) этого не учла:
            # держим в центре тот кусок картинки, что был виден в прежнем окне
            anchor_image = self._resize_anchor()

        fit = self._fit_ratio()
        lo, hi = self._scale_limits(fit)
        if scale is not None:
            self.scale_ratio = scale
        elif center:
            self.scale_ratio = fit
        self.scale_ratio = min(max(self.scale_ratio, lo), hi)
        self.zoom_factor = self.scale_ratio / fit if fit > 0 else 1.0

        if anchor_image is not None and self.scale_ratio > 0:
            point_x, point_y = anchor_image
            self.zoom_shift_x = cw / 2.0 - point_x * self.scale_ratio
            self.zoom_shift_y = ch / 2.0 - point_y * self.scale_ratio
        elif anchor is not None and old_scale > 0:
            ax, ay = anchor
            # точка изображения под курсором должна остаться под курсором
            point_x = (ax - self.zoom_shift_x) / old_scale
            point_y = (ay - self.zoom_shift_y) / old_scale
            self.zoom_shift_x = ax - point_x * self.scale_ratio
            self.zoom_shift_y = ay - point_y * self.scale_ratio
        elif center:
            self.zoom_shift_x = (cw - img_w * self.scale_ratio) / 2.0
            self.zoom_shift_y = (ch - img_h * self.scale_ratio) / 2.0

        region = self._visible_region(cw, ch)
        self.tk_image = None
        self.canvas.delete("all")
        if region is not None:
            (ix0, iy0, ix1, iy1), disp_w, disp_h, place_x, place_y = region
            crop_src = self.image.crop((ix0, iy0, ix1, iy1))
            self.tk_image = ImageTk.PhotoImage(self._display_image(crop_src, disp_w, disp_h))
            self.canvas.create_image(place_x, place_y, anchor="nw", image=self.tk_image)

        self._last_canvas = (cw, ch)
        self._check_fixed_fits()      # раньше подписи: она опирается на актуальный fixed_fits
        self._draw_selection()
        self._update_status_only()

    def _schedule_render(self, kind="keep", payload=None, delay=40, scale=None):
        """Колесо/панорама могут прийти залпом — перерисовываем один раз на пачку событий."""
        self._pending_render = (kind, payload, scale)
        if self._render_job is not None:
            try:
                self.root.after_cancel(self._render_job)
            except (ValueError, tk.TclError):
                pass
        try:
            self._render_job = self.root.after(delay, self._flush_render)
        except tk.TclError:
            self._render_job = None
            self._apply_pending_render()

    def _apply_pending_render(self):
        kind, payload, scale = self._pending_render or ("keep", None, None)
        self._pending_render = None
        if self.image is None:
            return
        if kind == "anchor":
            self._render(anchor=payload, scale=scale)
        else:
            self._render(scale=scale)

    def _flush_render(self):
        self._render_job = None
        self._apply_pending_render()

    def _selection_label(self, w, h):
        step = self._effective_step()
        label = "%d x %d" % (w, h)
        if step > 1:
            label += "  (кратно %d)" % step
            # предупреждение имеет смысл только когда сетка включена, но край всё же не сошёлся
            if w % 2 or h % 2:
                label += "  ! не кратно 2"
        return label

    def _draw_selection(self):
        if self.rect is not None:
            self.canvas.delete(self.rect)
            self.rect = None
        if self.size_text is not None:
            self.canvas.delete(self.size_text)
            self.size_text = None

        if not self.crop_box or self.image is None:
            return

        x1, y1, x2, y2 = self.crop_box
        cx1, cy1 = self._image_to_canvas(x1, y1)
        cx2, cy2 = self._image_to_canvas(x2, y2)

        # контур рисуем по реальной границе области: линия шириной 1 пиксель ровно по границе
        self.rect = self.canvas.create_rectangle(cx1 - 0.5, cy1 - 0.5, cx2 - 0.5, cy2 - 0.5,
                                                 outline="red", width=1)

        w, h = x2 - x1, y2 - y1
        label = self._selection_label(w, h)
        if self.fixed_resolution_crop.get() and not self.fixed_fits:
            label += "  ! фикс. %dx%d больше изображения, кроп %dx%d" % (
                self.fixed_width, self.fixed_height, w, h)
        self.size_text = self.canvas.create_text(max(2, cx1 + 5), max(2, cy1 - 12),
                                                 anchor="nw", text=label,
                                                 fill="white", font=("Arial", 10, "bold"))

    def _redraw_selection_now(self):
        if self.image is not None:
            self._draw_selection()

    # ============================================================ мышь: выделение
    def on_button_press_1(self, event):
        if self.image is None:
            return
        step = self._effective_step()
        img_w, img_h = self.image.size
        ix, iy = self._canvas_to_image(event.x, event.y)
        self.drag_origin = (self._snap_range(ix, step, 0, img_w),
                            self._snap_range(iy, step, 0, img_h))
        x, y = self.drag_origin
        self.crop_box = (x, y, x, y)
        self._draw_selection()
        self._update_status_only()

    def on_mouse_drag_1(self, event):
        if self.image is None or self.drag_origin is None:
            return

        step = self._effective_step()
        img_w, img_h = self.image.size
        ax, ay = self.drag_origin              # точка нажатия не «уезжает» во время драга
        fx, fy = self._canvas_to_image(event.x, event.y)
        dx, dy = fx - ax, fy - ay

        if self.fixed_resolution_crop.get():
            fw, fh = self._fixed_block_size(step)      # границы картинки + сетка + «квадрат»
            sign_x = 1 if dx >= 0 else -1
            sign_y = 1 if dy >= 0 else -1
            # прямоугольник ходит как жёсткий блок: дальний край за курсором, весь блок внутри картинки
            if sign_x > 0:
                ax = self._snap_range(fx - fw, step, 0, img_w - fw)
            else:
                ax = self._snap_range(fx + fw, step, fw, img_w)
            if sign_y > 0:
                ay = self._snap_range(fy - fh, step, 0, img_h - fh)
            else:
                ay = self._snap_range(fy + fh, step, fh, img_h)
            bx = ax + sign_x * fw
            by = ay + sign_y * fh
        elif self.square_crop.get():
            side = self._snap_range(min(abs(dx), abs(dy)), step, 0, min(img_w, img_h))
            bx = self._snap_range(ax + side * (1 if dx >= 0 else -1), step, 0, img_w)
            by = self._snap_range(ay + side * (1 if dy >= 0 else -1), step, 0, img_h)
            # после клампа по краям рамка обязана остаться квадратной
            side2 = self._snap_range(min(abs(bx - ax), abs(by - ay)), step, 0, min(img_w, img_h))
            bx = self._snap_range(ax + side2 * (1 if bx >= ax else -1), step, 0, img_w)
            by = self._snap_range(ay + side2 * (1 if by >= ay else -1), step, 0, img_h)
        else:
            bx = self._snap_range(fx, step, 0, img_w)
            by = self._snap_range(fy, step, 0, img_h)

        self.crop_box = self._norm_box(ax, ay, bx, by)
        self._draw_selection()
        self._update_status_only()

    def on_button_release_1(self, event):
        self.drag_origin = None
        if self.crop_box:
            x1, y1, x2, y2 = self.crop_box
            if x2 - x1 < 1 or y2 - y1 < 1:
                self.crop_box = None
            else:
                self.crop_box = self._reapply_fixed_size(self.crop_box, announce=False)
        self._draw_selection()
        self._update_status_only()

    # ====================================================== мышь: перенос рамки
    def on_button_press_3(self, event):
        if self.image is None:
            return
        if not self._inside_selection(event.x, event.y):
            # правая кнопка вне рамки — панорама
            self.pan_last = (event.x, event.y)
            return
        self.move_anchor = self._canvas_to_image(event.x, event.y)
        self.move_box0 = self.crop_box

    def _inside_selection(self, canvas_x, canvas_y, margin=3):
        if not self.crop_box:
            return False
        cx1, cy1 = self._image_to_canvas(self.crop_box[0], self.crop_box[1])
        cx2, cy2 = self._image_to_canvas(self.crop_box[2], self.crop_box[3])
        return (cx1 - margin <= canvas_x <= cx2 + margin and
                cy1 - margin <= canvas_y <= cy2 + margin)

    def on_mouse_drag_3(self, event):
        if self.image is None:
            return
        if self.move_box0 is None:
            if self.pan_last is not None:
                self._pan(event.x - self.pan_last[0], event.y - self.pan_last[1])
                self.pan_last = (event.x, event.y)
            return

        step = self._effective_step()
        img_w, img_h = self.image.size
        x1, y1, x2, y2 = self.move_box0
        w, h = x2 - x1, y2 - y1
        cx, cy = self._canvas_to_image(event.x, event.y)
        nx1 = self._snap_range(x1 + (cx - self.move_anchor[0]), step, 0, img_w - w)
        ny1 = self._snap_range(y1 + (cy - self.move_anchor[1]), step, 0, img_h - h)
        self.crop_box = (nx1, ny1, nx1 + w, ny1 + h)
        self._draw_selection()
        self._update_status_only()

    def on_button_release_3(self, event):
        self.move_anchor = None
        self.move_box0 = None
        self.pan_last = None

    # ================================================= мышь: панорама (средняя кнопка)
    def on_button_press_2(self, event):
        self.pan_last = (event.x, event.y)

    def on_mouse_drag_2(self, event):
        if self.image is None or self.pan_last is None:
            return
        self._pan(event.x - self.pan_last[0], event.y - self.pan_last[1])
        self.pan_last = (event.x, event.y)

    def on_button_release_2(self, event):
        self.pan_last = None

    def _pan(self, dx, dy):
        if self.image is None or (not dx and not dy):
            return
        # отложенный ЗУМ (он несёт новый масштаб) применяем сразу, иначе панорама его «съест».
        # отложенную «дозаполняющую» перерисовку самой панорамы, наоборот, не трогаем: применённая
        # на каждый motion-event, она превращает непрерывную панораму в череду полных ререндеров,
        # а ниже она всё равно будет заменена одной новой (на пачку событий).
        pending = self._pending_render
        if pending is not None and (pending[0] == "anchor" or pending[2] is not None):
            self._apply_pending_render()

        img_w, img_h = self.image.size
        disp_w = img_w * self.scale_ratio
        disp_h = img_h * self.scale_ratio
        cw = max(1, self.canvas.winfo_width())
        ch = max(1, self.canvas.winfo_height())

        # на экране обязана остаться приличная часть изображения, а не 80 пикселей из 700
        keep_x = min(disp_w, cw, max(EDGE_MARGIN, min(disp_w, cw) / 3.0))
        keep_y = min(disp_h, ch, max(EDGE_MARGIN, min(disp_h, ch) / 3.0))
        lo_x, hi_x = keep_x - disp_w, cw - keep_x
        lo_y, hi_y = keep_y - disp_h, ch - keep_y
        new_x = min(max(self.zoom_shift_x + dx, lo_x), hi_x) if lo_x <= hi_x else self.zoom_shift_x
        new_y = min(max(self.zoom_shift_y + dy, lo_y), hi_y) if lo_y <= hi_y else self.zoom_shift_y

        dx = new_x - self.zoom_shift_x
        dy = new_y - self.zoom_shift_y
        if not dx and not dy:
            return
        self.zoom_shift_x = new_x
        self.zoom_shift_y = new_y
        self.canvas.move("all", dx, dy)       # быстро: bitmap перемещаем, а не пересобираем
        self._schedule_render("keep", delay=250)   # дозаполняем запасную область вокруг видимой

    # ========================================================== зум / клавиатура
    def on_mouse_wheel(self, event):
        if self.image is None:
            return
        delta = getattr(event, "delta", 0)
        num = getattr(event, "num", 0)
        if num in (4, 5):
            zoom_in = (num == 4)
        elif delta:
            zoom_in = delta > 0
        else:
            return                             # горизонтальный скролл игнорируем
        factor = ZOOM_STEP_FAST if (getattr(event, "state", 0) & 0x0004) else ZOOM_STEP
        if not zoom_in:
            factor = 1.0 / factor
        # залп колеса: следующий шаг считаем от уже запланированного масштаба, иначе
        # десять щелчков за 40 мс схлопываются в один (и якорь последних кликов теряется)
        base = self.scale_ratio
        if self._pending_render is not None and self._pending_render[2] is not None:
            base = self._pending_render[2]
        self._zoom_to(base * factor, anchor=(event.x, event.y), debounce=True)

    def _zoom_to(self, new_scale, anchor=None, debounce=False):
        """new_scale — абсолютный масштаб (экранных пикселей на пиксель изображения)."""
        if self.image is None:
            return
        lo, hi = self._scale_limits(self._fit_ratio())
        new_scale = min(max(new_scale, lo), hi)
        current = self.scale_ratio
        if debounce and self._pending_render is not None and self._pending_render[2] is not None:
            current = self._pending_render[2]      # уже запланированный шаг зума
        if abs(new_scale - current) < 1e-9:
            return
        if debounce:
            self._schedule_render("anchor", anchor, scale=new_scale)
        else:
            self._render(anchor=anchor, scale=new_scale)

    def _zoom_by_keys(self, factor):
        if self.image is None or self._dialog_open:
            return
        cw = max(1, self.canvas.winfo_width())
        ch = max(1, self.canvas.winfo_height())
        self._zoom_to(self.scale_ratio * factor, anchor=(cw / 2.0, ch / 2.0))

    def reset_zoom(self):
        if self.image is None or self._dialog_open:
            return
        self._render(center=True)

    def zoom_one_to_one(self):
        """Один пиксель рабочего изображения — один пиксель экрана (и держим центр вида)."""
        if self.image is None or self._dialog_open:
            return
        img_w, img_h = self.image.size
        cx, cy = self._view_center_norm()      # центр вида, ограничен самими изображением
        self._render(anchor_image=(cx * img_w, cy * img_h), scale=1.0)

    def _on_arrow_key(self, event):
        if self.image is None or self._dialog_open:
            return
        step = PAN_KEY_STEP_FAST if (event.state & 0x0001) else PAN_KEY_STEP
        dx = {"Left": -step, "Right": step}.get(event.keysym, 0)
        dy = {"Up": -step, "Down": step}.get(event.keysym, 0)
        self._pan(dx, dy)

    # =================================================================== сохранение
    def _output_dir(self):
        if self.custom_dir_save.get() and self.save_dir:
            try:
                os.makedirs(self.save_dir, exist_ok=True)
                return self.save_dir
            except OSError as exc:
                self._set_status("Не удалось использовать папку %s: %s" % (self.save_dir, exc))
        if self.image_path:
            return os.path.dirname(os.path.abspath(self.image_path))
        return os.getcwd()

    def save_cropped_image(self):
        if self._dialog_open:
            return
        if self.image is None:
            self._set_status("Нет загруженного изображения.")
            return
        if not self.crop_box:
            self._set_status("Не выделена область кропа.")
            return

        x1, y1, x2, y2 = self.crop_box
        width, height = x2 - x1, y2 - y1
        if width < 1 or height < 1:
            self._set_status("Область кропа слишком маленькая.")
            return

        mask_mode = self.mask_only_save.get()
        out_dir = self._output_dir()
        base_name = os.path.splitext(os.path.basename(self.image_path))[0] if self.image_path else "image"

        if mask_mode:
            extension = ".png"
        else:
            extension = os.path.splitext(self.image_path)[1] if self.image_path else ""
            extension = extension if extension else ".png"

        suffix = "_mask" if mask_mode else "_crop"
        target = os.path.join(out_dir, base_name + suffix + extension)
        if self.version_index_save.get():
            target = self.versioned_path(target)

        converted = False
        try:
            os.makedirs(out_dir, exist_ok=True)

            if mask_mode:
                # ЧБ маска: чёрное поле рабочего разрешения + белый прямоугольник области
                mask = Image.new("L", self.image.size, 0)
                ImageDraw.Draw(mask).rectangle((x1, y1, x2 - 1, y2 - 1), fill=255)
                result = mask
            else:
                result = self.image.crop(self.crop_box)
                if extension.lower() in JPEG_EXT and result.mode not in ("RGB", "L", "CMYK"):
                    # JPEG понимает RGB, L и CMYK (CMYK-фото из полиграфии сохраняем как есть,
                    # иначе молча потеряли бы цветовой режим)
                    result = result.convert("RGB")

            try:
                result.save(target)
            except Exception:
                # редкий режим (CMYK, HSV, F...) этот формат не принимает — сохраняем в RGB
                result = result.convert("RGB")
                result.save(target)
                converted = True
        except Exception as exc:
            self._set_status("Ошибка при сохранении: %s" % exc)
            print("Ошибка при сохранении: %s" % exc)
            return

        if mask_mode:
            message = "Маска %dx%d сохранена: %s" % (self.image.size[0], self.image.size[1], target)
        else:
            message = "Кроп %dx%d сохранён: %s" % (width, height, target)
            if converted:
                message += "  (режим файла не подходил формату -> пересохранено в RGB)"
            if width % 2 or height % 2:
                message += "  (внимание: не кратно 2)"
        self._set_status(message)
        print(message)

    def versioned_path(self, image_path):
        """Имя вида base_crop_01.png по максимальному существующему счётчику."""
        folder = os.path.dirname(image_path) or "."
        base_name = os.path.splitext(os.path.basename(image_path))[0]
        extension = os.path.splitext(image_path)[1]

        pattern = re.compile(r"^%s_(\d+)%s$" % (re.escape(base_name), re.escape(extension)),
                             re.IGNORECASE)
        max_index = 0
        if os.path.isdir(folder):
            for file_name in os.listdir(folder):
                match = pattern.match(file_name)
                if match:
                    index = int(match.group(1))
                    if index > max_index:
                        max_index = index
        return os.path.join(folder, "%s_%02d%s" % (base_name, max_index + 1, extension))

    # ================================================================= статус/справка
    def _set_status(self, text):
        self.base_status = text
        self.status.config(text=text)

    def _update_status_only(self):
        self._update_status(None)

    def _update_status(self, message):
        if message is not None:
            self.base_status = message

        parts = [self.base_status]
        if self.image is not None:
            src_w, src_h = self.source_image.size
            work_w, work_h = self.image.size
            info = "рабочее %dx%d" % (work_w, work_h)
            if self.scale_mode == "none":
                info += " (исходник %dx%d)" % (src_w, src_h)
            else:
                side = "большей" if self.scale_mode == "long" else "меньшей"
                info += " (исходник %dx%d, %s сторона -> %d, k=%.4f%s)" % (
                    src_w, src_h, side, self.scale_target, self.scale_factor,
                    ", ограничен" if self.scale_clamped else "")
            parts.append(info)
            parts.append("зум %.0f%% (1 пикселя = %.2f экр.)" % (
                self.zoom_factor * 100.0, self.scale_ratio))

            if self.crop_box:
                x1, y1, x2, y2 = self.crop_box
                parts.append("кроп %s" % self._selection_label(x2 - x1, y2 - y1))

            mode = "маска (ЧБ)" if self.mask_only_save.get() else "кроп"
            if self.custom_dir_save.get():
                folder = self.save_dir if self.save_dir else "не выбрана"
                parts.append("сохранение: %s -> %s%s" % (mode, folder,
                                                         " (версии)" if self.version_index_save.get() else ""))
            else:
                parts.append("сохранение: %s -> рядом с оригиналом%s" % (
                    mode, " (версии)" if self.version_index_save.get() else ""))

        self.status.config(text="   |   ".join(parts))

    def show_help(self):
        if self._dialog_open:
            return
        self._dialog_open = True
        try:
            messagebox.showinfo(
                "Справка",
                "ЛКМ — выделить область кропа (рамка ходит рывками по сетке кратности).\n"
                "ПКМ внутри рамки — перенести выделение; ПКМ вне рамки — панорама.\n"
                "Средняя кнопка — панорама. Стрелки — тонкий сдвиг (Shift — крупный).\n"
                "Колесо — зум под курсором (Ctrl+колесо — быстрее), 0 — вписать в окно,\n"
                "плюс/минус — зум, Esc — сбросить выделение.\n"
                "Ctrl+S / кнопка Save — сохранить.\n\n"
                "Зум хранится как «экранных пикселей на пиксель изображения», поэтому 1:1\n"
                "остаётся 1:1 после изменения размера окна, поворота и смены масштаба.\n\n"
                "Опции:\n"
                "  Фиксировать разрешение — рамка 1536/1024/768/640/512 (если разрешение больше\n"
                "  картинки, кроп берётся по её границам — подпись рамки об этом пишет). Рамка\n"
                "  перестраивается при смене разрешения, кратности и масштаба исходника, так что\n"
                "  её размер всегда ровно заявленный. Вместе с «Фиксировать квадрат» получается\n"
                "  квадрат, кратный и разрешению, и сетке.\n"
                "  Кратность кропа — стороны прямоугольника кратны 2/4/8/16/32/64 (1 — свободно).\n"
                "  Масштаб исходника — рабочий размер по большей или меньшей стороне.\n"
                "  Повернуть 90° вправо/влево — выделение поворачивается вместе с картинкой.\n"
                "  Сохранять только маску кропа (ЧБ) — вместо кропа сохраняется чёрное поле\n"
                "  рабочего разрешения с белым прямоугольником области.\n"
                "  Сохранять в отдельную папку — каталог выбирается в меню.\n\n"
                "Повторный «Zoom 1:1» возвращает вид обратно в картинку, а панорама не даёт\n"
                "увести изображение так, чтобы от него на экране осталось меньше трети."
            )
        finally:
            self._dialog_open = False

    # ==================================================================== прочее
    def on_drop(self, event):
        try:
            paths = list(self.root.tk.splitlist(event.data))
        except tk.TclError:
            paths = [event.data.strip().strip("{}")]

        chosen = None
        for candidate in paths:
            candidate = os.path.normpath(candidate)
            if candidate and os.path.isfile(candidate):
                chosen = candidate
                break

        if chosen is None:
            self._set_status("В окне брошено не изображение (или несколько файлов сразу).")
            return
        self.load_image(chosen)

    def on_canvas_resize(self, event):
        """Tk сыплет Configure при каждом шаге изменения размера — перерисовку откладываем,
        но вид (точка изображения в центре окна) сохраняем."""
        if self.image is None:
            return
        if self._resize_job is not None:
            try:
                self.root.after_cancel(self._resize_job)
            except (ValueError, tk.TclError):
                pass
        try:
            self._resize_job = self.root.after(80, self._render_after_resize)
        except tk.TclError:
            self._resize_job = None
            self._render()

    def _render_after_resize(self):
        self._resize_job = None
        if self.image is None:
            return
        cw = max(1, self.canvas.winfo_width())
        ch = max(1, self.canvas.winfo_height())
        if (cw, ch) == self._last_canvas:
            #Tk шлёт Configure и когда окно просто переместили: канвас не изменился — не перерисовываем
            return
        if self._pending_render is not None:
            # отложенный зум/панорама дорисовываются уже под новый размер окна — вид не трогаем
            self._apply_pending_render()
            return
        # окно изменили: держим в центре то, что было видно в прежнем окне
        self._render(anchor_image=self._resize_anchor())


def main():
    try:
        root = TkinterDnD.Tk() if HAS_DND else tk.Tk()
    except Exception:
        # tkdnd может отсутствовать (RuntimeError у tkinterdnd2) — работаем без перетаскивания
        root = tk.Tk()
    CropImageApp(root)
    root.mainloop()


if __name__ == "__main__":
    main()
