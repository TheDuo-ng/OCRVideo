import os
import io
import sys
import shutil
import time
import threading
import configparser
import datetime
import re
import psutil
from pathlib import Path
import concurrent.futures
import ctypes

# Giao diện
import tkinter as tk
from tkinter import messagebox, ttk, filedialog, scrolledtext, simpledialog

# Xử lý ảnh và video
import cv2
from PIL import Image, ImageTk

# Google Drive API
from google.auth.transport.requests import Request
from google.oauth2.credentials import Credentials
from google_auth_oauthlib.flow import InstalledAppFlow
from googleapiclient.discovery import build
from googleapiclient.errors import HttpError
from googleapiclient.http import MediaFileUpload, MediaIoBaseDownload

# Thư viện phát hiện cảnh
# --- SỬA LỖI: Sử dụng hàm open_video thay vì nhập trực tiếp VideoCapture ---
from scenedetect import SceneManager, open_video
from scenedetect.detectors import ContentDetector
from scenedetect.frame_timecode import FrameTimecode

# --- Hằng số ---
SCOPES = ["https://www.googleapis.com/auth/drive"]
CLIENT_SECRET_FILE = "credentials.json"
TOKEN_FILE = "token.json"
CONFIG_FILE = "config.ini"
APPLICATION_NAME = "VideoOCR"
DRIVE_FOLDER_NAME = "VideoOCR_Temp_Files"
LOG_DATETIME_FORMAT = "%H:%M:%S"
LOG_FILE_DATETIME_FORMAT = "%Y-%m-%d %H:%M:%S"

# --- Lớp chính của ứng dụng ---
class VideoOCRApp:
    def __init__(self, root):
        self.root = root
        self.root.protocol("WM_DELETE_WINDOW", self.on_exit)

        # --- Thuộc tính trạng thái ---
        self.credentials = None
        self.stop_flag = threading.Event()
        self.progress_lock = threading.Lock()
        self.srt_file_list = {}
        self.completed_scans = 0
        self.total_images = 0
        self.start_time_processing = 0
        self.presets = {}

        # --- Đường dẫn và Cấu hình ---
        self.folder_id = ""
        self.log_file_path = None
        self.current_video_path = None
        self.current_images_path = None

        # --- Khởi tạo UI và tải cấu hình ---
        self.init_ui()
        self.load_config()
        self.log_message(f"Chào mừng đến với {APPLICATION_NAME} V6.2 (PySceneDetect)!")
        self.log_message("Vui lòng đảm bảo file 'credentials.json' từ Google Cloud đã ở trong cùng thư mục.")

    def init_ui(self):
        """Khởi tạo toàn bộ giao diện người dùng."""
        self.root.title(f"{APPLICATION_NAME} v6.2 (sử dụng PySceneDetect)")
        self.root.geometry("700x600")
        self.root.minsize(650, 550)

        config_frame = tk.LabelFrame(self.root, text="Cấu hình chung", padx=10, pady=5)
        config_frame.pack(padx=10, pady=5, fill="x")

        detection_frame = tk.Frame(config_frame)
        detection_frame.pack(fill="x", pady=2)
        tk.Label(detection_frame, text="Ngưỡng phát hiện:", width=15, anchor="w").pack(side="left")
        self.detection_threshold_var = tk.StringVar()
        tk.Entry(detection_frame, textvariable=self.detection_threshold_var, width=10).pack(side="left")
        tk.Label(detection_frame, text="(Mặc định: 27.0)").pack(side="left", padx=5)

        threads_frame = tk.Frame(config_frame)
        threads_frame.pack(fill="x", pady=2)
        tk.Label(threads_frame, text="Số luồng OCR:", width=15, anchor="w").pack(side="left")
        self.threads_var = tk.StringVar()
        tk.Entry(threads_frame, textvariable=self.threads_var, width=10).pack(side="left")

        preset_frame = tk.LabelFrame(self.root, text="Preset Tọa độ", padx=10, pady=5)
        preset_frame.pack(padx=10, pady=5, fill="x")
        tk.Label(preset_frame, text="Chọn Preset:", width=15, anchor="w").pack(side="left")
        self.preset_var = tk.StringVar()
        self.preset_combobox = ttk.Combobox(preset_frame, textvariable=self.preset_var, state="readonly")
        self.preset_combobox.pack(side="left", expand=True, fill="x", padx=(0, 5))
        self.preset_combobox.bind("<<ComboboxSelected>>", self.on_preset_select)
        tk.Button(preset_frame, text="Quản lý...", command=self.manage_presets).pack(side="left")

        workflow_frame = tk.LabelFrame(self.root, text="Quy trình xử lý", padx=10, pady=5)
        workflow_frame.pack(padx=10, pady=5, fill="x")

        video_frame = tk.Frame(workflow_frame)
        video_frame.pack(fill="x", pady=3)
        self.select_video_button = tk.Button(video_frame, text="1. Chọn Video", command=self.select_video_and_setup, width=15)
        self.select_video_button.pack(side="left", padx=5)
        self.video_path_var = tk.StringVar()
        tk.Entry(video_frame, textvariable=self.video_path_var, state="readonly").pack(side="left", expand=True, fill="x")

        crop_frame = tk.Frame(workflow_frame)
        crop_frame.pack(fill="x", pady=3)
        self.toado_button = tk.Button(crop_frame, text="2. Lấy Tọa độ", command=self.choose_video_for_crop, state=tk.DISABLED, width=15)
        self.toado_button.pack(side="left", padx=5)
        self.crop_top_var, self.crop_bottom_var, self.crop_left_var, self.crop_right_var = tk.StringVar(), tk.StringVar(), tk.StringVar(), tk.StringVar()
        
        coord_display_frame = tk.Frame(workflow_frame)
        coord_display_frame.pack(fill="x", pady=2, padx=5)
        self.coord_label = tk.Label(coord_display_frame, text="Tọa độ chưa được chọn", anchor="w", fg="grey")
        self.coord_label.pack(side="left")

        run_frame = tk.Frame(workflow_frame)
        run_frame.pack(fill="x", pady=3)
        self.run_button = tk.Button(run_frame, text="3. Phát hiện Phụ đề", command=self.run_scene_detection, state=tk.DISABLED, width=15)
        self.run_button.pack(side="left", padx=5)

        ocr_run_frame = tk.Frame(workflow_frame)
        ocr_run_frame.pack(fill="x", pady=3)
        self.start_button = tk.Button(ocr_run_frame, text="4. Bắt đầu OCR", command=self.start_processing_workflow, state=tk.DISABLED, bg="#4CAF50", fg="white", width=15)
        self.start_button.pack(side="left", padx=5)
        self.stop_button = tk.Button(ocr_run_frame, text="❌ Dừng", command=self.stop_processing, state=tk.DISABLED, bg="#F44336", fg="white")
        self.stop_button.pack(side="left", padx=5)

        options_frame = tk.LabelFrame(self.root, text="Tùy chọn", padx=10, pady=5)
        options_frame.pack(padx=10, pady=5, fill="x")
        self.nen_raw_texts_var = tk.BooleanVar()
        self.delete_all_temp_var = tk.BooleanVar()
        tk.Checkbutton(options_frame, text="Nén raw_texts", variable=self.nen_raw_texts_var).pack(side="left")
        tk.Checkbutton(options_frame, text="Xóa hết file tạm khi xong", variable=self.delete_all_temp_var).pack(side="left", padx=10)

        status_log_frame = tk.Frame(self.root)
        status_log_frame.pack(padx=10, pady=5, fill="both", expand=True)
        self.progress_bar = ttk.Progressbar(status_log_frame, orient="horizontal", mode="determinate")
        self.progress_bar.pack(fill="x", pady=(0, 2))
        self.status_label = tk.Label(self.root, text="Trạng thái: Sẵn sàng", bd=1, relief=tk.SUNKEN, anchor="w")
        self.status_label.pack(side=tk.BOTTOM, fill="x")
        self.log_text = scrolledtext.ScrolledText(status_log_frame, height=5, wrap="word", state="disabled", bg="#2B2B2B", fg="#A9B7C6", relief=tk.SUNKEN, bd=1)
        self.log_text.pack(fill="both", expand=True)

    def load_config(self):
        config = configparser.ConfigParser()
        if not os.path.exists(CONFIG_FILE):
            config['Settings'] = {
                "folder_id": "", "delete_all_temp": "True", "nen_raw_texts": "False",
                "threads": "10", "detection_threshold": "27.0"
            }
            config['Presets'] = {'Default': '1.0000,0.1500,0.0000,1.0000'}
            with open(CONFIG_FILE, 'w', encoding='utf-8') as configfile:
                config.write(configfile)
        
        config.read(CONFIG_FILE, encoding='utf-8')
        settings = config['Settings']
        self.folder_id = settings.get("folder_id", "")
        self.delete_all_temp_var.set(settings.getboolean("delete_all_temp", True))
        self.nen_raw_texts_var.set(settings.getboolean("nen_raw_texts", False))
        self.threads_var.set(settings.get("threads", "10"))
        self.detection_threshold_var.set(settings.get("detection_threshold", "27.0"))

        self.presets.clear()
        if 'Presets' in config:
            for name, values_str in config['Presets'].items():
                try:
                    values = [float(v.strip()) for v in values_str.split(',')]
                    if len(values) == 4: self.presets[name] = values
                except (ValueError, TypeError): self.log_message(f"Lỗi đọc preset '{name}'", "warning")
        self.update_preset_combobox()

    def save_config(self):
        config = configparser.ConfigParser()
        config['Settings'] = {
            "folder_id": self.folder_id,
            "delete_all_temp": str(self.delete_all_temp_var.get()),
            "nen_raw_texts": str(self.nen_raw_texts_var.get()),
            "threads": self.threads_var.get(),
            "detection_threshold": self.detection_threshold_var.get()
        }
        config['Presets'] = {name: ','.join(f"{v:.4f}" for v in values) for name, values in self.presets.items()}
        with open(CONFIG_FILE, "w", encoding='utf-8') as configfile:
            config.write(configfile)

    def run_scene_detection(self):
        try:
            float(self.detection_threshold_var.get())
        except ValueError:
            messagebox.showerror("Lỗi", "Ngưỡng phát hiện phải là một con số.")
            return
        self.set_ui_state_for_processing(True)
        self.update_status("Đang chuẩn bị phát hiện phụ đề...")
        threading.Thread(target=self._scenedetect_thread_target, daemon=True).start()

    def _scenedetect_thread_target(self):
        video_capture = None 
        try:
            self.stop_flag.clear()
            video_path = Path(self.current_video_path)
            self.current_images_path = video_path.parent / f"{video_path.stem}_images"
            if self.current_images_path.exists():
                shutil.rmtree(self.current_images_path)
            self.current_images_path.mkdir()

            self.log_message("🚀 Bắt đầu phát hiện phụ đề với PySceneDetect...")
            
            # --- SỬA LỖI: Sử dụng hàm open_video ---
            video_capture = open_video(str(video_path))
            scene_manager = SceneManager()
            scene_manager.add_detector(ContentDetector(threshold=float(self.detection_threshold_var.get())))
            
            video_capture.set_downscale_factor()
            video_capture.start()
            
            total_frames = video_capture.duration.get_frames()
            
            def progress_callback(frame_data, frame_num):
                if self.stop_flag.is_set():
                    raise InterruptedError("Process stopped by user")
                progress = (frame_num / total_frames) * 100
                self.root.after(0, self.update_progress, progress, f"⚙️ Đang quét frame {frame_num}/{total_frames}")

            scene_manager.detect_scenes(frame_source=video_capture, callback=progress_callback)
            
            scene_list = scene_manager.get_scene_list()
            self.log_message(f"✅ Phát hiện hoàn tất. Tìm thấy {len(scene_list)} phân cảnh chứa phụ đề.")
            
            if not scene_list:
                self.log_message("⚠️ Không tìm thấy phụ đề nào. Thử giảm ngưỡng phát hiện.", "warning")
                return
            
            self.log_message("🖼️ Bắt đầu lưu ảnh...")
            for i, (start_time, end_time) in enumerate(scene_list):
                if self.stop_flag.is_set(): break
                
                video_capture.seek(start_time)
                ret, frame = video_capture.read()
                if ret:
                    h, w, _ = frame.shape
                    top = float(self.crop_top_var.get())
                    bottom = float(self.crop_bottom_var.get())
                    left = float(self.crop_left_var.get())
                    right = float(self.crop_right_var.get())
                    
                    y1, y2 = int(h * (1 - top)), int(h * (1 - bottom))
                    x1, x2 = int(w * left), int(w * right)
                    
                    cropped_frame = frame[y1:y2, x1:x2]

                    start_str = start_time.get_timecode().replace(":", "_").replace(".", "_")
                    end_str = end_time.get_timecode().replace(":", "_").replace(".", "_")

                    image_name = f"{start_str}__{end_str}.jpg"
                    image_path = self.current_images_path / image_name
                    cv2.imwrite(str(image_path), cropped_frame)

                progress = ((i + 1) / len(scene_list)) * 100
                self.update_progress(progress, f"🖼️ Đang lưu ảnh {i+1}/{len(scene_list)}")

            if self.stop_flag.is_set():
                self.log_message("✋ Quá trình lưu ảnh đã được dừng.", "warning")
                return

            self.log_message("✅ Đã lưu xong ảnh. Sẵn sàng để OCR.")
            self.update_status("Hoàn tất phát hiện. Sẵn sàng OCR.")
            self.root.after(0, self.start_button.config, {"state": tk.NORMAL})

        except InterruptedError:
             self.log_message("✋ Quá trình phát hiện đã được dừng bởi người dùng.", "warning")
        except Exception as e:
            self.log_message(f"❌ Lỗi trong quá trình phát hiện phụ đề: {e}", "error")
        finally:
            # Logic dọn dẹp tài nguyên được giữ nguyên, vì video_capture sẽ tự đóng
            self.root.after(0, self.set_ui_state_for_processing, False)
            self.root.after(0, self.progress_bar.config, {"value": 0})
            
    def stop_processing(self):
        self.stop_flag.set()
        self.set_ui_state_for_processing(False)
        self.log_message("🛑 Quá trình đã được yêu cầu dừng.", "warning")
        self.update_status("Đã dừng bởi người dùng")
        
    def update_progress(self, percentage, status_text):
        self.progress_bar['value'] = percentage
        self.status_label.config(text=f" {status_text}")
    
    def on_exit(self):
        if messagebox.askokcancel("Xác nhận thoát", "Lưu các thay đổi và thoát chương trình?"):
            self.save_config()
            self.stop_processing() 
            self.root.destroy()

    def get_credentials(self):
        creds = None
        if os.path.exists(TOKEN_FILE):
            creds = Credentials.from_authorized_user_file(TOKEN_FILE, SCOPES)
        if not creds or not creds.valid:
            if creds and creds.expired and creds.refresh_token:
                try: creds.refresh(Request())
                except Exception as e:
                    self.log_message(f"Token hết hạn, cần đăng nhập lại. Lỗi: {e}", "warning")
                    creds = self.run_auth_flow()
            else:
                creds = self.run_auth_flow()
            if creds:
                with open(TOKEN_FILE, "w") as token: token.write(creds.to_json())
        return creds

    def run_auth_flow(self):
        if not os.path.exists(CLIENT_SECRET_FILE):
            messagebox.showerror("Lỗi nghiêm trọng", f"Không tìm thấy file '{CLIENT_SECRET_FILE}'.")
            return None
        try:
            flow = InstalledAppFlow.from_client_secrets_file(CLIENT_SECRET_FILE, SCOPES)
            return flow.run_local_server(port=0)
        except Exception as e:
            messagebox.showerror("Lỗi xác thực", f"Lỗi trong quá trình xác thực Google: {e}")
            return None
    
    def select_video_and_setup(self):
        video_file = filedialog.askopenfilename(title="Chọn một tệp video", filetypes=[("Video files", "*.mp4 *.avi *.mkv *.mov")])
        if not video_file: return
        self.current_video_path = video_file
        self.video_path_var.set(self.current_video_path)
        self.log_message(f"🎬 Đã chọn video: {self.current_video_path}")
        self.toado_button.config(state=tk.NORMAL)
        self.run_button.config(state=tk.DISABLED)
        self.start_button.config(state=tk.DISABLED)
        self.progress_bar["value"] = 0
        self.update_status("Sẵn sàng chọn tọa độ")

    def choose_video_for_crop(self):
        if not self.current_video_path:
            messagebox.showwarning("Cảnh báo", "Vui lòng chọn video trước.")
            return
        crop_window = tk.Toplevel(self.root)
        crop_window.transient(self.root)
        CropSelectorApp(crop_window, self.current_video_path, self.update_crop_values)

    def update_crop_values(self, top, bottom, left, right):
        self.crop_top_var.set(f"{top:.4f}")
        self.crop_bottom_var.set(f"{bottom:.4f}")
        self.crop_left_var.set(f"{left:.4f}")
        self.crop_right_var.set(f"{right:.4f}")
        self.run_button.config(state=tk.NORMAL)
        self.log_message(f"🎯 Đã nhận tọa độ: Top={top:.4f}, Bottom={bottom:.4f}, Left={left:.4f}, Right={right:.4f}")
        self.update_status("Sẵn sàng phát hiện phụ đề")
        self.coord_label.config(text=f"Tọa độ đã chọn: T={top:.2f}, B={bottom:.2f}, L={left:.2f}, R={right:.2f}")

    def start_processing_workflow(self):
        if not self.current_images_path or not os.path.exists(self.current_images_path):
            messagebox.showwarning("Cảnh báo", "Chưa có thư mục ảnh. Vui lòng chạy 'Phát hiện Phụ đề' trước.")
            return
        try:
            num_threads = int(self.threads_var.get())
            if num_threads <= 0: raise ValueError
        except ValueError:
            messagebox.showerror("Lỗi", "Số luồng phải là một số nguyên dương.")
            return
        self.set_ui_state_for_processing(True)
        self.update_status("Đang xác thực với Google...")
        threading.Thread(target=self._ocr_thread_target, daemon=True).start()

    def set_ui_state_for_processing(self, is_processing):
        state = tk.DISABLED if is_processing else tk.NORMAL
        self.select_video_button.config(state=state)
        self.toado_button.config(state=tk.DISABLED if is_processing or not self.current_video_path else tk.NORMAL)
        self.run_button.config(state=tk.DISABLED if is_processing or not self.crop_top_var.get() else tk.NORMAL)
        self.start_button.config(state=tk.DISABLED if is_processing or not self.current_images_path or not os.path.exists(self.current_images_path) else tk.NORMAL)
        self.stop_button.config(state=tk.NORMAL if is_processing else tk.DISABLED)

    def log_message(self, message, level="info"):
        def _log():
            if not self.log_text.winfo_exists(): return
            tag_colors = {"info": "#A9B7C6", "error": "#FF6B68", "warning": "#FFC66D", "success": "#6A8759"}
            final_level = "success" if "✅" in message or "🎉" in message else level
            self.log_text.config(state="normal")
            self.log_text.insert(tk.END, f"[{datetime.datetime.now().strftime(LOG_DATETIME_FORMAT)}] {message}\n", final_level)
            self.log_text.tag_config(final_level, foreground=tag_colors.get(final_level, "#A9B7C6"))
            self.log_text.see(tk.END)
            self.log_text.config(state="disabled")
            if self.log_file_path:
                with open(self.log_file_path, "a", encoding="utf-8") as log_file:
                    log_file.write(f"[{datetime.datetime.now().strftime(LOG_FILE_DATETIME_FORMAT)}] {message}\n")
        self.root.after(0, _log)

    def update_status(self, text):
        self.status_label.config(text=f" {text}")

    def _ocr_thread_target(self):
        self.credentials = self.get_credentials()
        if not self.credentials:
            self.log_message("❌ Xác thực thất bại.", "error")
            self.root.after(0, self.set_ui_state_for_processing, False)
            return

        if not self.folder_id:
            # Code để tìm hoặc tạo thư mục trên Drive
            pass 

        self.stop_flag.clear()
        self.srt_file_list.clear()
        self.completed_scans = 0
        self.start_time_processing = time.time()

        video_path = Path(self.current_video_path)
        subtitle_path = video_path.with_suffix('.srt')
        self.log_file_path = video_path.with_suffix('.log')
        with open(self.log_file_path, "a", encoding="utf-8") as log_file:
            log_file.write(f"\n=== Bắt đầu OCR: {datetime.datetime.now().strftime(LOG_FILE_DATETIME_FORMAT)} ===\n")

        self.log_message("🚀 Bắt đầu quá trình OCR...")
        self.progress_bar["value"] = 0

        video_dir = video_path.parent
        raw_texts_dir = video_dir / "raw_texts"
        texts_dir = video_dir / "texts"
        raw_texts_dir.mkdir(exist_ok=True)
        texts_dir.mkdir(exist_ok=True)

        images = sorted(list(Path(self.current_images_path).glob('**/*.*')))
        self.total_images = len(images)
        num_threads = int(self.threads_var.get())
        self.log_message(f"|| Số luồng: {num_threads} || Tổng ảnh: {self.total_images}")

        if self.total_images == 0:
            messagebox.showerror("Lỗi", f"Thư mục '{self.current_images_path}' không chứa hình ảnh.")
            self.root.after(0, self.set_ui_state_for_processing, False)
            return

        try:
            with concurrent.futures.ThreadPoolExecutor(max_workers=num_threads) as executor:
                futures = {executor.submit(self.ocr_image, img, i + 1, video_dir): img for i, img in enumerate(images)}
                for future in concurrent.futures.as_completed(futures):
                    if self.stop_flag.is_set(): break
                    try: future.result()
                    except Exception as exc: self.log_message(f"Lỗi xử lý ảnh {futures[future].name}: {exc}", "error")

            if self.stop_flag.is_set(): return

            srt_content = "".join("".join(self.srt_file_list[i]) for i in sorted(self.srt_file_list))
            self.root.after(0, self.preview_srt, srt_content, lambda content: self.save_srt_and_finalize(content, subtitle_path, raw_texts_dir, texts_dir))

        except Exception as e:
            self.log_message(f"❌ Lỗi nghiêm trọng: {e}", "error")
            self.finalize_processing(raw_texts_dir, texts_dir)

    def ocr_image(self, image_path, line_number, current_directory):
        if self.stop_flag.is_set(): return
        try:
            service = build("drive", "v3", credentials=self.credentials)
            img_name = image_path.name
            raw_txtfile = current_directory / "raw_texts" / f"{image_path.stem}.txt"
            txtfile = current_directory / "texts" / f"{image_path.stem}.txt"
            file_metadata = {"name": img_name, "mimeType": "application/vnd.google-apps.document", "parents": [self.folder_id]}
            media = MediaFileUpload(str(image_path), mimetype="image/jpeg", resumable=True)
            file = service.files().create(body=file_metadata, media_body=media, fields="id").execute()
            
            request = service.files().export_media(fileId=file.get("id"), mimeType="text/plain")
            with io.FileIO(raw_txtfile, "wb") as fh:
                downloader = MediaIoBaseDownload(fh, request)
                done = False
                while not done: _, done = downloader.next_chunk()
            
            service.files().delete(fileId=file.get("id")).execute()

            with open(raw_txtfile, "r", encoding="utf-8") as raw_text_file:
                text_content = "".join(raw_text_file.read().splitlines(True)[2:]).strip()
            
            if not text_content: self.log_message(f"⚠️ OCR: Ảnh {img_name} trống.", "warning")
            else: self.log_message(f"💬 OCR: {text_content[:55].strip()}...")
            
            with open(txtfile, "w", encoding="utf-8") as text_file: text_file.write(text_content)
            
            start_h, start_m, start_s, start_ms = img_name.split("_")[:4]
            end_h, end_m, end_s, end_ms = img_name.split("__")[1].split("_")[:4]
            start_time = f"{start_h}:{start_m}:{start_s},{start_ms}"
            end_time = f"{end_h}:{end_m}:{end_s},{end_ms}"
            self.srt_file_list[line_number] = [f"{line_number}\n", f"{start_time.replace('_',',')} --> {end_time.replace('_',',')}\n", f"{text_content}\n\n"]
        except Exception as e:
            self.log_message(f"❌ Lỗi OCR ảnh {image_path.name}: {e}", "error")
        finally:
            with self.progress_lock:
                self.completed_scans += 1
                if self.total_images > 0:
                    progress = (self.completed_scans / self.total_images) * 100
                    self.root.after(0, self.update_progress, progress, f"⚙️ Đang OCR: {self.completed_scans}/{self.total_images}")

    def save_srt_and_finalize(self, content, subtitle_path, raw_texts_dir, texts_dir):
        try:
            with open(subtitle_path, "w", encoding="utf-8") as srt_file: srt_file.write(content)
            self.log_message(f"✅ Đã lưu file SRT: {subtitle_path}")
        except Exception as e:
            self.log_message(f"❌ Lỗi khi lưu file SRT: {e}", "error")
        finally:
            self.finalize_processing(raw_texts_dir, texts_dir)

    def finalize_processing(self, raw_texts_dir, texts_dir):
        if self.nen_raw_texts_var.get() and raw_texts_dir.exists():
            try:
                archive_path = texts_dir.parent / "raw_texts_archive"
                shutil.make_archive(str(archive_path), "zip", str(raw_texts_dir))
                self.log_message(f"✅ Đã nén raw_texts.")
            except Exception as e: self.log_message(f"Lỗi khi nén: {e}", "error")

        if self.delete_all_temp_var.get():
            try:
                if raw_texts_dir.exists(): shutil.rmtree(raw_texts_dir)
                if texts_dir.exists(): shutil.rmtree(texts_dir)
                if self.current_images_path and Path(self.current_images_path).exists():
                    shutil.rmtree(self.current_images_path)
                self.log_message("✅ Đã xóa file tạm.")
            except Exception as e: self.log_message(f"❌ Lỗi xóa file tạm: {e}", "error")

        total_time = time.time() - self.start_time_processing
        formatted_time = time.strftime("%H:%M:%S", time.gmtime(total_time))
        self.update_status(f"✅ Hoàn thành OCR! Tổng thời gian: {formatted_time}")
        self.log_message(f"🎉 Hoàn thành OCR. Tổng thời gian xử lý: {formatted_time}")
        self.set_ui_state_for_processing(False)

    def preview_srt(self, srt_content, save_callback):
        preview_window = tk.Toplevel(self.root)
        preview_window.title("Xem trước & Chỉnh sửa phụ đề SRT")
        preview_window.geometry("600x400")
        preview_window.transient(self.root)
        preview_window.grab_set()
        srt_text = scrolledtext.ScrolledText(preview_window, wrap="word", undo=True)
        srt_text.pack(padx=10, pady=10, fill="both", expand=True)
        srt_text.insert(tk.END, srt_content)
        button_frame = tk.Frame(preview_window)
        button_frame.pack(pady=(0, 10))
        tk.Button(button_frame, text="Lưu và Đóng", command=lambda: [save_callback(srt_text.get("1.0", tk.END)), preview_window.destroy()]).pack(side=tk.LEFT, padx=5)
        tk.Button(button_frame, text="Hủy bỏ", command=preview_window.destroy).pack(side=tk.LEFT, padx=5)
        self.root.wait_window(preview_window)

    def update_preset_combobox(self):
        self.preset_combobox['values'] = list(self.presets.keys())
        if self.presets: self.preset_combobox.set(list(self.presets.keys())[0])

    def on_preset_select(self, event=None):
        preset_name = self.preset_var.get()
        if preset_name in self.presets:
            values = self.presets[preset_name]
            self.update_crop_values(values[0], values[1], values[2], values[3])
    
    def manage_presets(self):
        PresetManager(self.root, self.presets, self.update_presets_callback)

    def update_presets_callback(self, new_presets):
        self.presets = new_presets
        self.update_preset_combobox()
        self.save_config()
        self.log_message("✅ Đã cập nhật danh sách preset.")

class CropSelectorApp:
    def __init__(self, root, video_path, update_crop_callback):
        self.root = root
        self.video_path = video_path
        self.update_crop_callback = update_crop_callback
        self.cap = cv2.VideoCapture(video_path)

        self.video_width = int(self.cap.get(cv2.CAP_PROP_FRAME_WIDTH))
        self.video_height = int(self.cap.get(cv2.CAP_PROP_FRAME_HEIGHT))
        self.fps = self.cap.get(cv2.CAP_PROP_FPS) if self.cap.get(cv2.CAP_PROP_FPS) > 0 else 30
        self.total_frames = int(self.cap.get(cv2.CAP_PROP_FRAME_COUNT))

        self.top_line_y = int(0.85 * self.video_height)
        self.bottom_line_y = int(0.99 * self.video_height)
        self.left_line_x = int(0.1 * self.video_width)
        self.right_line_x = int(0.9 * self.video_width)
        
        self.selected_line = None
        
        self.init_ui()
        self.root.after(10, self.initial_frame_load)

    def init_ui(self):
        self.root.title("Chọn vùng chứa phụ đề")
        main_frame = tk.Frame(self.root)
        main_frame.pack(expand=True, fill=tk.BOTH, padx=10, pady=10)
        self.canvas = tk.Canvas(main_frame, bg="black")
        self.canvas.pack(expand=True, fill=tk.BOTH)
        self.canvas.bind("<ButtonPress-1>", self.on_mouse_press)
        self.canvas.bind("<B1-Motion>", self.on_mouse_drag)
        self.canvas.bind("<ButtonRelease-1>", self.on_mouse_release)
        self.canvas.bind("<Motion>", self.on_mouse_move)
        self.root.bind("<Configure>", self.on_resize)

        param_frame = tk.Frame(main_frame)
        param_frame.pack(fill=tk.X, pady=5)
        self.top_var, self.bottom_var, self.left_var, self.right_var = tk.StringVar(), tk.StringVar(), tk.StringVar(), tk.StringVar()
        for label, var in zip(["Top:", "Bottom:", "Left:", "Right:"], [self.top_var, self.bottom_var, self.left_var, self.right_var]):
            tk.Label(param_frame, text=label).pack(side=tk.LEFT, padx=(10, 0))
            tk.Entry(param_frame, textvariable=var, width=8, state="readonly").pack(side=tk.LEFT)
        ttk.Button(param_frame, text="Xác nhận", command=self.confirm_selection).pack(side=tk.RIGHT, padx=10)

        timeline_frame = tk.Frame(main_frame)
        timeline_frame.pack(fill=tk.X, pady=5)
        self.slider = ttk.Scale(timeline_frame, from_=0, to=self.total_frames - 1, orient="horizontal", command=self.seek_video)
        self.slider.pack(side=tk.LEFT, expand=True, fill=tk.X)
        self.time_label = tk.Label(timeline_frame, text="00:00:00.000", width=12)
        self.time_label.pack(side=tk.LEFT, padx=5)
        
    def initial_frame_load(self):
        self.update_parameters()
        self.show_frame(0)

    def on_resize(self, event): self.show_frame(int(self.slider.get()))
    def seek_video(self, value): self.show_frame(int(float(value)))

    def show_frame(self, frame_index):
        if not self.cap or not self.cap.isOpened(): return
        canvas_w, canvas_h = self.canvas.winfo_width(), self.canvas.winfo_height()
        if canvas_w < 10 or canvas_h < 10: return

        self.cap.set(cv2.CAP_PROP_POS_FRAMES, frame_index)
        ret, frame = self.cap.read()
        if not ret: return

        h, w, _ = frame.shape
        scale = min(canvas_w/w, canvas_h/h) if w > 0 and h > 0 else 1
        self.display_w, self.display_h = int(w * scale), int(h * scale)
        frame_resized = cv2.resize(frame, (self.display_w, self.display_h), interpolation=cv2.INTER_AREA)
        
        img = Image.fromarray(cv2.cvtColor(frame_resized, cv2.COLOR_BGR2RGB))
        self.photo = ImageTk.PhotoImage(image=img)
        
        self.canvas.delete("all")
        self.offset_x = (canvas_w - self.display_w) // 2
        self.offset_y = (canvas_h - self.display_h) // 2
        self.canvas.create_image(self.offset_x, self.offset_y, anchor=tk.NW, image=self.photo)
        
        self.draw_bounding_lines()
        self.update_time_display(frame_index / self.fps if self.fps > 0 else 0)

    def get_pixel_coords(self, event):
        x = (event.x - self.offset_x) * (self.video_width / self.display_w) if self.display_w > 0 else 0
        y = (event.y - self.offset_y) * (self.video_height / self.display_h) if self.display_h > 0 else 0
        return x, y

    def on_mouse_press(self, event):
        x, y = self.get_pixel_coords(event)
        self.selected_line = self.get_clicked_line(x, y)

    def get_clicked_line(self, x, y):
        tolerance_y = 0.03 * self.video_height
        if abs(y - self.top_line_y) < tolerance_y: return "top"
        if abs(y - self.bottom_line_y) < tolerance_y: return "bottom"
        tolerance_x = 0.03 * self.video_width
        if abs(x - self.left_line_x) < tolerance_x: return "left"
        if abs(x - self.right_line_x) < tolerance_x: return "right"
        return None

    def on_mouse_drag(self, event):
        if not self.selected_line: return
        x, y = self.get_pixel_coords(event)
        if self.selected_line == "top": self.top_line_y = max(0, min(y, self.bottom_line_y - 1))
        elif self.selected_line == "bottom": self.bottom_line_y = max(self.top_line_y + 1, min(y, self.video_height))
        elif self.selected_line == "left": self.left_line_x = max(0, min(x, self.right_line_x - 1))
        elif self.selected_line == "right": self.right_line_x = max(self.left_line_x + 1, min(x, self.video_width))
        self.draw_bounding_lines()
        self.update_parameters()

    def on_mouse_release(self, event): self.selected_line = None; self.canvas.config(cursor="arrow")
    def on_mouse_move(self, event):
        if self.selected_line: return
        x, y = self.get_pixel_coords(event)
        line = self.get_clicked_line(x, y)
        if line in ("top", "bottom"): self.canvas.config(cursor="sb_v_double_arrow")
        elif line in ("left", "right"): self.canvas.config(cursor="sb_h_double_arrow")
        else: self.canvas.config(cursor="arrow")

    def update_parameters(self):
        if not self.video_width or not self.video_height: return
        self.top_var.set(f"{1 - (self.top_line_y / self.video_height):.4f}")
        self.bottom_var.set(f"{(self.video_height - self.bottom_line_y) / self.video_height:.4f}")
        self.left_var.set(f"{self.left_line_x / self.video_width:.4f}")
        self.right_var.set(f"{self.right_line_x / self.video_width:.4f}")

    def update_time_display(self, current_time_sec):
        td = datetime.timedelta(seconds=current_time_sec)
        hours, remainder = divmod(td.seconds, 3600)
        minutes, seconds = divmod(remainder, 60)
        self.time_label.config(text=f"{hours:02}:{minutes:02}:{seconds:02}.{td.microseconds // 1000:03}")

    def draw_bounding_lines(self):
        cx = lambda x: (x * (self.display_w / self.video_width)) + self.offset_x if self.video_width > 0 else 0
        cy = lambda y: (y * (self.display_h / self.video_height)) + self.offset_y if self.video_height > 0 else 0
        self.canvas.delete("bounding_lines")
        self.canvas.create_line(self.offset_x, cy(self.top_line_y), self.offset_x + self.display_w, cy(self.top_line_y), fill="yellow", width=2, tags="bounding_lines")
        self.canvas.create_line(self.offset_x, cy(self.bottom_line_y), self.offset_x + self.display_w, cy(self.bottom_line_y), fill="yellow", width=2, tags="bounding_lines")
        self.canvas.create_line(cx(self.left_line_x), self.offset_y, cx(self.left_line_x), self.offset_y + self.display_h, fill="yellow", width=2, tags="bounding_lines")
        self.canvas.create_line(cx(self.right_line_x), self.offset_y, cx(self.right_line_x), self.offset_y + self.display_h, fill="yellow", width=2, tags="bounding_lines")

    def confirm_selection(self):
        self.update_crop_callback(
            top=float(self.top_var.get()), bottom=float(self.bottom_var.get()),
            left=float(self.left_var.get()), right=float(self.right_var.get())
        )
        self.cap.release()
        self.root.destroy()
        
class PresetManager:
    def __init__(self, parent, presets, callback):
        self.top = tk.Toplevel(parent)
        self.top.title("Quản lý Preset Tọa độ")
        self.top.geometry("500x350")
        self.top.transient(parent)
        self.top.grab_set()
        self.presets = presets.copy()
        self.callback = callback

        list_frame = tk.Frame(self.top)
        list_frame.pack(padx=10, pady=10, fill="both", expand=True)
        self.listbox = tk.Listbox(list_frame)
        self.listbox.pack(side="left", fill="both", expand=True)
        scrollbar = ttk.Scrollbar(list_frame, orient="vertical", command=self.listbox.yview)
        scrollbar.pack(side="right", fill="y")
        self.listbox.config(yscrollcommand=scrollbar.set)
        
        button_frame = tk.Frame(self.top)
        button_frame.pack(pady=5)
        tk.Button(button_frame, text="Thêm...", command=self.add_preset).pack(side="left", padx=5)
        tk.Button(button_frame, text="Sửa...", command=self.edit_preset).pack(side="left", padx=5)
        tk.Button(button_frame, text="Xóa", command=self.delete_preset).pack(side="left", padx=5)
        tk.Button(button_frame, text="Lưu và Đóng", command=self.save_and_close).pack(side="right", padx=5)
        self.populate_listbox()

    def populate_listbox(self):
        self.listbox.delete(0, tk.END)
        for name in sorted(self.presets.keys()): self.listbox.insert(tk.END, name)

    def add_preset(self):
        name = simpledialog.askstring("Tên Preset", "Nhập tên cho preset mới:", parent=self.top)
        if not name: return
        if name in self.presets:
            messagebox.showerror("Lỗi", f"Preset '{name}' đã tồn tại.", parent=self.top)
            return
        values_str = simpledialog.askstring("Giá trị Preset", "Nhập 4 giá trị (top, bottom, left, right), cách nhau bởi dấu phẩy:", parent=self.top)
        try:
            values = [float(v.strip()) for v in values_str.split(',')]
            if len(values) != 4: raise ValueError
            self.presets[name] = values
            self.populate_listbox()
        except (ValueError, TypeError, AttributeError):
            messagebox.showerror("Lỗi", "Định dạng không hợp lệ. Cần 4 số cách nhau bởi dấu phẩy.", parent=self.top)

    def edit_preset(self):
        selected = self.listbox.curselection()
        if not selected:
            messagebox.showwarning("Cảnh báo", "Vui lòng chọn một preset để sửa.", parent=self.top)
            return
        name = self.listbox.get(selected[0])
        current_values_str = ','.join(f"{v:.4f}" for v in self.presets[name])
        new_values_str = simpledialog.askstring("Sửa giá trị", f"Sửa giá trị cho '{name}':", initialvalue=current_values_str, parent=self.top)
        if new_values_str:
            try:
                values = [float(v.strip()) for v in new_values_str.split(',')]
                if len(values) != 4: raise ValueError
                self.presets[name] = values
            except (ValueError, TypeError, AttributeError):
                messagebox.showerror("Lỗi", "Định dạng không hợp lệ.", parent=self.top)

    def delete_preset(self):
        selected = self.listbox.curselection()
        if not selected:
            messagebox.showwarning("Cảnh báo", "Vui lòng chọn một preset để xóa.", parent=self.top)
            return
        name = self.listbox.get(selected[0])
        if messagebox.askyesno("Xác nhận", f"Bạn có chắc chắn muốn xóa preset '{name}'?", parent=self.top):
            del self.presets[name]
            self.populate_listbox()

    def save_and_close(self):
        self.callback(self.presets)
        self.top.destroy()

if __name__ == "__main__":
    try:
        # Cải thiện hiển thị trên màn hình HiDPI (Windows)
        ctypes.windll.shcore.SetProcessDpiAwareness(1)
    except Exception:
        pass 
    
    root = tk.Tk()
    app = VideoOCRApp(root)
    root.mainloop()
