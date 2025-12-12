import os
import json
import webbrowser
import tkinter as tk
from tkinter import messagebox, simpledialog, ttk, Menu
import random

# Check for dependencies
try:
    import pygame
    HAS_DEPS = True
except ImportError:
    HAS_DEPS = False
    print("Warning: 'pygame' not found. Please install it via pip for audio playback.")

class Song:
    """Data class to hold song metadata and file path."""
    def __init__(self, title, artist, path=None):
        self.title = title
        self.artist = artist
        self.path = path

    def __str__(self):
        return f"{self.title} - {self.artist}"

class Node:
    """Node class for Doubly Linked List."""
    def __init__(self, data):
        self.data = data
        self.next = None
        self.prev = None

class Stack:
    """LIFO Stack for Listening History."""
    def __init__(self):
        self.items = []

    def push(self, item):
        self.items.append(item)

    def pop(self):
        if not self.is_empty():
            return self.items.pop()
        return None

    def is_empty(self):
        return len(self.items) == 0

class DoublyLinkedList:
    """
    Doubly Linked List for the Active Queue.
    Supports O(1) pointer operations.
    """
    def __init__(self):
        self.head = None
        self.tail = None
        self.current = None
        self.size = 0

    def append(self, data):
        """Add song to the end. O(1)"""
        new_node = Node(data)
        if not self.head:
            self.head = new_node
            self.tail = new_node
            self.current = new_node
        else:
            new_node.prev = self.tail
            self.tail.next = new_node
            self.tail = new_node
        self.size += 1

    def clear(self):
        """Clears the list."""
        self.head = None
        self.tail = None
        self.current = None
        self.size = 0

    def remove_node(self, node):
        """Remove specific node. O(1)"""
        if not node: return
        if node == self.head: self.head = node.next
        if node == self.tail: self.tail = node.prev
        if node.prev: node.prev.next = node.next
        if node.next: node.next.prev = node.prev
        if node == self.current:
            self.current = node.next if node.next else node.prev
        node.next = None
        node.prev = None
        self.size -= 1

    def find(self, query):
        """Linear Search. O(N)"""
        results = []
        temp = self.head
        while temp:
            if (query.lower() in temp.data.title.lower() or 
                query.lower() in temp.data.artist.lower()):
                results.append(temp)
            temp = temp.next
        return results

    def get_node_at_index(self, index):
        """O(N) Access"""
        if index < 0 or index >= self.size: return None
        temp = self.head
        for _ in range(index): temp = temp.next
        return temp

    def swap_nodes(self, node1, node2):
        """Swap adjacent nodes. O(1)"""
        if not node1 or not node2 or node1.next != node2: return
        prev_node = node1.prev
        next_node = node2.next
        if prev_node: prev_node.next = node2
        else: self.head = node2
        if next_node: next_node.prev = node1
        else: self.tail = node1
        node2.prev = prev_node
        node2.next = node1
        node1.prev = node2
        node1.next = next_node

    def shuffle(self):
        """Fisher-Yates Shuffle. O(N)"""
        if self.size < 2: return
        nodes = []
        temp = self.head
        while temp:
            nodes.append(temp)
            temp = temp.next
        n = len(nodes)
        for i in range(n - 1, 0, -1):
            j = random.randint(0, i)
            nodes[i], nodes[j] = nodes[j], nodes[i]
        self.head = nodes[0]
        self.tail = nodes[-1]
        self.head.prev = None
        self.tail.next = None
        for k in range(n):
            if k > 0: nodes[k].prev = nodes[k-1]
            if k < n - 1: nodes[k].next = nodes[k+1]

# ==========================================
# Main Application
# ==========================================

class HarmoniaApp:
    def __init__(self, root):
        self.root = root
        self.root.title("Harmonia")
        self.root.geometry("1000x700")
        self.root.configure(bg="#121212")

        if not HAS_DEPS:
            messagebox.showwarning("Missing Dependencies", 
                                   "Required library (pygame) not found.\nRun: pip install pygame")

        # --- Setup Paths ---
        # Path: FINAL_PROJECT_DSA/Harmonia/Harmonia.py -> FINAL_PROJECT_DSA/Assets/songs
        base_dir = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
        self.songs_dir = os.path.join(base_dir, 'Assets', 'songs')
        if not os.path.exists(self.songs_dir):
            os.makedirs(self.songs_dir)
        self.playlists_file = os.path.join(base_dir, 'Assets', 'playlists.txt')

        # --- Audio Init ---
        if HAS_DEPS:
            pygame.mixer.init()

        # --- Data ---
        self.queue = DoublyLinkedList() # The active playing queue
        self.history = Stack()
        self.library = [] # List of Song objects (All songs)
        self.playlists = {} # Dict {name: [Song, Song]}
        self.current_view_songs = [] # Songs currently displayed in UI
        self.active_playlist_name = "Library" # "Library" or playlist name
        self.is_looping = False
        self.is_shuffled = False
        self.is_playing = False
        self.is_dragging = False
        self.song_length = 0
        self.start_time = 0
        self.current_time = 0

        self.setup_ui()
        self.refresh_library()
        self.load_playlists()
        self.update_progress()

    def setup_ui(self):
        # Styles
        bg_color = "#121212"
        sidebar_color = "#000000"
        player_color = "#181818"
        text_color = "#FFFFFF"
        accent_color = "#1DB954" # Spotify Green

        # --- Layout Frames ---
        self.root.grid_rowconfigure(0, weight=1)
        self.root.grid_columnconfigure(1, weight=1)

        # Sidebar (Left)
        self.sidebar = tk.Frame(self.root, bg=sidebar_color, width=200, padx=10, pady=10)
        self.sidebar.grid(row=0, column=0, sticky="ns")
        self.sidebar.grid_propagate(False)

        # Main Content (Right)
        self.main_area = tk.Frame(self.root, bg=bg_color)
        self.main_area.grid(row=0, column=1, sticky="nsew")

        # Player Bar (Bottom)
        self.player_bar = tk.Frame(self.root, bg=player_color, height=100, padx=20)
        self.player_bar.grid(row=1, column=0, columnspan=2, sticky="ew")
        self.player_bar.grid_propagate(False)

        # --- Sidebar Content ---
        tk.Label(self.sidebar, text="Harmonia", bg=sidebar_color, fg=text_color, font=("Helvetica", 18, "bold")).pack(anchor="w", pady=(0, 20))
        
        btn_style = {"bg": sidebar_color, "fg": "#B3B3B3", "activebackground": sidebar_color, "activeforeground": text_color, "bd": 0, "font": ("Helvetica", 11), "anchor": "w", "cursor": "hand2"}
        
        tk.Button(self.sidebar, text="🏠 Home", command=self.show_library, **btn_style).pack(fill="x", pady=5)
        tk.Button(self.sidebar, text="≡ Queue", command=self.show_queue, **btn_style).pack(fill="x", pady=5)
        
        tk.Label(self.sidebar, text="PLAYLISTS", bg=sidebar_color, fg=text_color, font=("Helvetica", 10, "bold")).pack(anchor="w", pady=(20, 10))
        tk.Button(self.sidebar, text="➕ Create Playlist", command=self.create_playlist, **btn_style).pack(fill="x", pady=5)
        
        self.playlist_frame = tk.Frame(self.sidebar, bg=sidebar_color)
        self.playlist_frame.pack(fill="both", expand=True)

        # --- Main Area Content ---
        # Search Bar
        self.search_var = tk.StringVar()
        self.search_var.trace("w", self.filter_songs)
        search_frame = tk.Frame(self.main_area, bg=bg_color, pady=10, padx=20)
        search_frame.pack(fill="x")
        tk.Entry(search_frame, textvariable=self.search_var, bg="#333333", fg=text_color, insertbackground=text_color, font=("Helvetica", 12), relief="flat").pack(fill="x", ipady=5)

        # Song List (Treeview)
        style = ttk.Style()
        style.theme_use("clam")
        style.configure("Treeview", background=bg_color, foreground=text_color, fieldbackground=bg_color, borderwidth=0, rowheight=30, font=("Helvetica", 10))
        style.configure("Treeview.Heading", background="#181818", foreground="#B3B3B3", borderwidth=0, font=("Helvetica", 10, "bold"))
        style.map("Treeview", background=[('selected', '#333333')])

        self.tree = ttk.Treeview(self.main_area, columns=("Title", "Artist"), show="headings", selectmode="browse")
        self.tree.heading("Title", text="TITLE", anchor="w")
        self.tree.heading("Artist", text="ARTIST", anchor="w")
        self.tree.column("Title", anchor="w", width=300)
        self.tree.column("Artist", anchor="w", width=200)
        self.tree.pack(fill="both", expand=True, padx=20, pady=10)
        
        self.tree.bind("<Double-1>", self.on_song_double_click)
        self.tree.bind("<Button-3>", self.show_context_menu) # Right click

        # Empty State
        self.frame_empty = tk.Frame(self.main_area, bg=bg_color)
        empty_content = tk.Frame(self.frame_empty, bg=bg_color)
        empty_content.place(relx=0.5, rely=0.5, anchor="center")
        tk.Label(empty_content, text="There is no songs at the current moment.", bg=bg_color, fg=text_color, font=("Helvetica", 14)).pack()
        lbl_link = tk.Label(empty_content, text="How to export a song from youtube", bg=bg_color, fg="#3366ff", font=("Helvetica", 12, "underline"), cursor="hand2")
        lbl_link.pack(pady=5)
        lbl_link.bind("<Button-1>", lambda e: webbrowser.open("https://ytmp3.as/AOPR/"))

        # --- Player Bar Content ---
        # Left: Now Playing Info
        self.lbl_now_title = tk.Label(self.player_bar, text="Not Playing", bg=player_color, fg=text_color, font=("Helvetica", 11, "bold"))
        self.lbl_now_title.pack(side="left", padx=(0, 5))
        self.lbl_now_artist = tk.Label(self.player_bar, text="", bg=player_color, fg="#B3B3B3", font=("Helvetica", 10))
        self.lbl_now_artist.pack(side="left")

        # Right: Controls & Progress
        self.right_container = tk.Frame(self.player_bar, bg=player_color)
        self.right_container.pack(side="right", padx=20)

        # Controls (Top)
        controls_frame = tk.Frame(self.right_container, bg=player_color)
        controls_frame.pack(side="top", pady=(15, 5))

        ctrl_btn_style = {"bg": player_color, "fg": text_color, "activebackground": player_color, "activeforeground": accent_color, "bd": 0, "font": ("Helvetica", 14), "cursor": "hand2"}
        
        self.btn_shuffle = tk.Button(controls_frame, text="🔀", command=self.toggle_shuffle, **ctrl_btn_style)
        self.btn_shuffle.pack(side="left", padx=10)
        tk.Button(controls_frame, text="⏮", command=self.play_prev, **ctrl_btn_style).pack(side="left", padx=10)
        self.btn_play = tk.Button(controls_frame, text="▶", command=self.toggle_play, **dict(ctrl_btn_style, font=("Helvetica", 20)))
        self.btn_play.pack(side="left", padx=10)
        tk.Button(controls_frame, text="⏭", command=self.play_next, **ctrl_btn_style).pack(side="left", padx=10)
        self.btn_loop = tk.Button(controls_frame, text="🔁", command=self.toggle_loop, **ctrl_btn_style)
        self.btn_loop.pack(side="left", padx=10)

        # Progress (Bottom)
        self.progress_frame = tk.Frame(self.right_container, bg=player_color)
        self.progress_frame.pack(side="bottom", pady=(0, 15))

        self.lbl_current_time = tk.Label(self.progress_frame, text="0:00", bg=player_color, fg="#B3B3B3", font=("Helvetica", 9))
        self.lbl_current_time.pack(side="left", padx=5)

        self.slider = tk.Canvas(self.progress_frame, height=15, width=400, bg=player_color, highlightthickness=0, cursor="hand2")
        self.slider.pack(side="left", padx=5)
        self.slider.bind("<Button-1>", self.on_slider_click)
        self.slider.bind("<B1-Motion>", self.on_slider_drag)
        self.slider.bind("<ButtonRelease-1>", self.on_slider_release)
        self.slider.bind("<Configure>", lambda e: self.update_slider_display())

        self.lbl_total_time = tk.Label(self.progress_frame, text="0:00", bg=player_color, fg="#B3B3B3", font=("Helvetica", 9))
        self.lbl_total_time.pack(side="left", padx=5)

        self.context_menu = Menu(self.root, tearoff=0, bg="#282828", fg="white")

    def refresh_library(self):
        """Scans the songs folder and updates the library list."""
        self.library = []
        if os.path.exists(self.songs_dir):
            for f in os.listdir(self.songs_dir):
                if f.endswith(('.mp3', '.wav', '.ogg', '.m4a', '.webm')):
                    # Simple parsing: assume "Artist - Title.ext" or just "Title.ext"
                    name = os.path.splitext(f)[0]
                    if " - " in name:
                        parts = name.split(" - ", 1)
                        artist, title = parts[0], parts[1]
                    else:
                        artist, title = "Unknown Artist", name
                    
                    full_path = os.path.join(self.songs_dir, f)
                    self.library.append(Song(title, artist, full_path))
        
        if self.active_playlist_name == "Library":
            self.current_view_songs = self.library
            self.update_song_list()

    def update_song_list(self):
        """Updates the Treeview with current_view_songs."""
        for item in self.tree.get_children():
            self.tree.delete(item)
        
        if not self.current_view_songs:
            self.tree.pack_forget()
            self.frame_empty.pack(fill="both", expand=True)
        else:
            self.frame_empty.pack_forget()
            self.tree.pack(fill="both", expand=True, padx=20, pady=10)
            for song in self.current_view_songs:
                self.tree.insert("", "end", values=(song.title, song.artist), tags=(song.path,))

    def filter_songs(self, *args):
        """Search filter logic."""
        query = self.search_var.get().lower()
        if not query:
            self.current_view_songs = self.library if self.active_playlist_name == "Library" else self.playlists[self.active_playlist_name]
        else:
            source = self.library if self.active_playlist_name == "Library" else self.playlists[self.active_playlist_name]
            self.current_view_songs = [s for s in source if query in s.title.lower() or query in s.artist.lower()]
        self.update_song_list()

    def save_playlists(self):
        """Saves playlists to a text file (JSON format)."""
        data = {}
        for name, songs in self.playlists.items():
            data[name] = [s.path for s in songs]
        
        try:
            with open(self.playlists_file, 'w') as f:
                json.dump(data, f)
        except Exception as e:
            print(f"Error saving playlists: {e}")

    def load_playlists(self):
        """Loads playlists from the text file."""
        if not os.path.exists(self.playlists_file): return
        try:
            with open(self.playlists_file, 'r') as f:
                data = json.load(f)
                for name, paths in data.items():
                    self.playlists[name] = []
                    for path in paths:
                        # Find the song in the library by path to ensure valid object
                        song = next((s for s in self.library if s.path == path), None)
                        if song:
                            self.playlists[name].append(song)
            self.refresh_sidebar_playlists()
        except Exception as e:
            print(f"Error loading playlists: {e}")

    def create_playlist(self):
        dialog = tk.Toplevel(self.root)
        dialog.title("New Playlist")
        dialog.geometry("400x220")
        dialog.configure(bg="#282828")
        dialog.transient(self.root)
        dialog.grab_set()

        # Center the dialog relative to the main window
        x = self.root.winfo_rootx() + (self.root.winfo_width() // 2) - 200
        y = self.root.winfo_rooty() + (self.root.winfo_height() // 2) - 110
        dialog.geometry(f"+{x}+{y}")

        tk.Label(dialog, text="Playlist Name", bg="#282828", fg="white", font=("Helvetica", 16, "bold")).pack(pady=(30, 10))
        
        entry = tk.Entry(dialog, font=("Helvetica", 14), bg="#3E3E3E", fg="white", insertbackground="white", relief="flat")
        entry.pack(pady=10, padx=30, fill="x", ipady=3)
        entry.focus_set()

        def submit(event=None):
            name = entry.get().strip()
            if name:
                if name in self.playlists:
                    messagebox.showerror("Error", "Playlist exists.", parent=dialog)
                else:
                    self.playlists[name] = []
                    self.save_playlists()
                    self.refresh_sidebar_playlists()
                    dialog.destroy()

        entry.bind("<Return>", submit)

        btn_frame = tk.Frame(dialog, bg="#282828")
        btn_frame.pack(pady=20)
        
        tk.Button(btn_frame, text="Cancel", command=dialog.destroy, font=("Helvetica", 11), bg="#535353", fg="white", relief="flat", padx=10).pack(side="left", padx=10)
        tk.Button(btn_frame, text="Create", command=submit, font=("Helvetica", 11, "bold"), bg="#1DB954", fg="white", relief="flat", padx=10).pack(side="left", padx=10)

        self.root.wait_window(dialog)

    def refresh_sidebar_playlists(self):
        for widget in self.playlist_frame.winfo_children():
            widget.destroy()
        
        for name in self.playlists:
            btn = tk.Button(self.playlist_frame, text=f"🎵 {name}", 
                            command=lambda n=name: self.show_playlist(n),
                            bg="#000000", fg="#B3B3B3", bd=0, anchor="w", font=("Helvetica", 11), cursor="hand2")
            btn.pack(fill="x", pady=2)
            btn.bind("<Button-3>", lambda e, n=name: self.show_playlist_context_menu(e, n))

    def show_library(self):
        self.active_playlist_name = "Library"
        self.search_var.set("")
        self.refresh_library()

    def show_playlist(self, name):
        self.active_playlist_name = name
        self.search_var.set("")
        self.current_view_songs = self.playlists[name]
        self.update_song_list()

    def show_queue(self):
        self.active_playlist_name = "Queue"
        self.search_var.set("")
        songs = []
        temp = self.queue.head
        while temp:
            songs.append(temp.data)
            temp = temp.next
        self.current_view_songs = songs
        self.update_song_list()

    def show_playlist_context_menu(self, event, name):
        menu = Menu(self.root, tearoff=0, bg="#282828", fg="white")
        menu.add_command(label="Add to Queue", command=lambda: self.add_playlist_to_queue(name))
        
        submenu = Menu(menu, tearoff=0, bg="#282828", fg="white")
        for other_name in self.playlists:
            if other_name != name:
                submenu.add_command(label=other_name, command=lambda s=name, t=other_name: self.add_playlist_to_playlist(s, t))
        menu.add_cascade(label="Add to Playlist", menu=submenu)
        
        menu.add_separator()
        menu.add_command(label="Delete Playlist", command=lambda: self.delete_playlist(name))
        menu.post(event.x_root, event.y_root)

    def delete_playlist(self, name):
        dialog = tk.Toplevel(self.root)
        dialog.title("Delete Playlist")
        dialog.geometry("400x200")
        dialog.configure(bg="#282828")
        dialog.transient(self.root)
        dialog.grab_set()

        # Center the dialog relative to the main window
        x = self.root.winfo_rootx() + (self.root.winfo_width() // 2) - 200
        y = self.root.winfo_rooty() + (self.root.winfo_height() // 2) - 100
        dialog.geometry(f"+{x}+{y}")

        tk.Label(dialog, text="Delete Playlist?", bg="#282828", fg="white", font=("Helvetica", 16, "bold")).pack(pady=(30, 10))
        tk.Label(dialog, text=f"Are you sure you want to delete '{name}'?", bg="#282828", fg="#B3B3B3", font=("Helvetica", 11)).pack(pady=5)

        def confirm():
            del self.playlists[name]
            self.save_playlists()
            self.refresh_sidebar_playlists()
            if self.active_playlist_name == name:
                self.show_library()
            dialog.destroy()

        btn_frame = tk.Frame(dialog, bg="#282828")
        btn_frame.pack(pady=20)
        
        tk.Button(btn_frame, text="Cancel", command=dialog.destroy, font=("Helvetica", 11), bg="#535353", fg="white", relief="flat", padx=10).pack(side="left", padx=10)
        tk.Button(btn_frame, text="Delete", command=confirm, font=("Helvetica", 11, "bold"), bg="#E91429", fg="white", relief="flat", padx=10).pack(side="left", padx=10)

        self.root.wait_window(dialog)

    def add_playlist_to_queue(self, name):
        songs = self.playlists[name]
        for song in songs:
            self.queue.append(song)
        messagebox.showinfo("Queue", f"Added {len(songs)} songs to queue.")

    def add_playlist_to_playlist(self, source_name, target_name):
        source_songs = self.playlists[source_name]
        target_songs = self.playlists[target_name]
        count = 0
        for song in source_songs:
            if song not in target_songs:
                target_songs.append(song)
                count += 1
        self.save_playlists()
        messagebox.showinfo("Playlist", f"Added {count} songs to {target_name}.")

    def add_single_song_to_queue(self, song):
        self.queue.append(song)
        messagebox.showinfo("Queue", f"Added '{song.title}' to queue.")

    def remove_from_queue_ui(self, index):
        node = self.queue.get_node_at_index(index)
        if node:
            is_current = (node == self.queue.current)
            self.queue.remove_node(node)
            if is_current:
                if self.is_playing:
                    pygame.mixer.music.stop()
                    self.is_playing = False
                    self.btn_play.config(text="▶")
                    self.lbl_now_title.config(text="Not Playing")
                    self.lbl_now_artist.config(text="")
                    self.lbl_total_time.config(text="0:00")
                    self.current_time = 0
                    self.update_slider_display()
            self.show_queue()

    def show_context_menu(self, event):
        item = self.tree.identify_row(event.y)
        if item:
            self.tree.selection_set(item)
            self.context_menu.delete(0, tk.END)
            
            index = self.tree.index(item)
            if 0 <= index < len(self.current_view_songs):
                song = self.current_view_songs[index]
            else:
                return
            
            if self.active_playlist_name == "Queue":
                self.context_menu.add_command(label="Remove from Queue", command=lambda: self.remove_from_queue_ui(index))
                
                submenu = Menu(self.context_menu, tearoff=0, bg="#282828", fg="white")
                for pl_name in self.playlists:
                    submenu.add_command(label=pl_name, command=lambda p=pl_name, s=song: self.add_to_playlist(p, s))
                
                self.context_menu.add_cascade(label="Add to Playlist", menu=submenu)
            else:
                self.context_menu.add_command(label="Add to Queue", command=lambda: self.add_single_song_to_queue(song))
                
                submenu = Menu(self.context_menu, tearoff=0, bg="#282828", fg="white")
                for pl_name in self.playlists:
                    submenu.add_command(label=pl_name, command=lambda p=pl_name, s=song: self.add_to_playlist(p, s))
                self.context_menu.add_cascade(label="Add to Playlist", menu=submenu)
            
            self.context_menu.post(event.x_root, event.y_root)

    def add_to_playlist(self, pl_name, song):
        if song not in self.playlists[pl_name]:
            self.playlists[pl_name].append(song)
            self.save_playlists()
            messagebox.showinfo("Success", f"Added to {pl_name}")

    def play_specific_song(self, song):
        # Load context into Queue (DLL)
        self.queue.clear()
        start_node = None
        for s in self.current_view_songs:
            self.queue.append(s)
            if s == song:
                start_node = self.queue.tail
        
        self.queue.current = start_node
        
        if self.is_shuffled:
            self.queue.shuffle()
            
        self.play_current()

    def on_song_double_click(self, event):
        item = self.tree.selection()[0]
        vals = self.tree.item(item)['values']
        song = next((s for s in self.current_view_songs if s.title == vals[0] and s.artist == vals[1]), None)
        if song:
            self.play_specific_song(song)

    def play_current(self):
        if not self.queue.current or not HAS_DEPS: return
        
        song = self.queue.current.data
        try:
            # Get duration
            try:
                sound = pygame.mixer.Sound(song.path)
                self.song_length = sound.get_length()
                self.lbl_total_time.config(text=self.format_time(self.song_length))
            except Exception:
                self.song_length = 0
                self.lbl_total_time.config(text="0:00")
            self.current_time = 0
            self.update_slider_display()
            pygame.mixer.music.load(song.path)
            pygame.mixer.music.play()
            self.is_playing = True
            self.btn_play.config(text="⏸")
            self.lbl_now_title.config(text=song.title)
            self.lbl_now_artist.config(text=song.artist)
            
            # Highlight in treeview
            for item in self.tree.get_children():
                if self.tree.item(item)['tags'][0] == song.path:
                    self.tree.selection_set(item)
                    self.tree.see(item)
                    break
            
            self.start_time = 0
            # Check for song end
            self.check_music_end()
        except Exception as e:
            print(f"Playback error: {e}")

    def check_music_end(self):
        if self.is_playing and not pygame.mixer.music.get_busy():
            self.play_next()
        else:
            self.root.after(1000, self.check_music_end)

    def toggle_play(self):
        if not HAS_DEPS: return
        
        # Check for selection in treeview
        sel = self.tree.selection()
        selected_song = None
        if sel:
             vals = self.tree.item(sel[0])['values']
             selected_song = next((s for s in self.current_view_songs if s.title == vals[0] and s.artist == vals[1]), None)
        
        if selected_song and (not self.queue.current or self.queue.current.data != selected_song):
             self.play_specific_song(selected_song)
             return

        if self.is_playing:
            pygame.mixer.music.pause()
            self.is_playing = False
            self.btn_play.config(text="▶")
        else:
            is_paused = False
            try:
                if pygame.mixer.music.get_pos() != -1:
                    is_paused = True
            except:
                pass

            if self.queue.current and is_paused:
                pygame.mixer.music.unpause()
                if not pygame.mixer.music.get_busy(): # If stopped
                    pygame.mixer.music.play()
                self.is_playing = True
                self.btn_play.config(text="⏸")
                self.check_music_end()
            elif self.current_view_songs:
                self.play_specific_song(self.current_view_songs[0])

    def play_next(self):
        if not self.queue.current: return
        
        self.history.push(self.queue.current)
        
        if self.queue.current.next:
            self.queue.current = self.queue.current.next
            self.play_current()
        elif self.is_looping:
            self.queue.current = self.queue.head
            self.play_current()
        else:
            self.is_playing = False
            self.btn_play.config(text="▶")

    def play_prev(self):
        if not self.history.is_empty():
            self.queue.current = self.history.pop()
            self.play_current()
        elif self.queue.current and self.queue.current.prev:
            self.queue.current = self.queue.current.prev
            self.play_current()

    def toggle_shuffle(self):
        self.is_shuffled = not self.is_shuffled
        self.btn_shuffle.config(fg="#1DB954" if self.is_shuffled else "#FFFFFF")
        
        if self.is_shuffled:
            self.queue.shuffle()
        else:
            # Restore order from current view
            current_data = self.queue.current.data if self.queue.current else None
            self.queue.clear()
            target_node = None
            for s in self.current_view_songs:
                self.queue.append(s)
                if current_data and s == current_data:
                    target_node = self.queue.tail
            self.queue.current = target_node

    def toggle_loop(self):
        self.is_looping = not self.is_looping
        self.btn_loop.config(fg="#1DB954" if self.is_looping else "#FFFFFF")

    def on_slider_click(self, event):
        self.is_dragging = True
        self.seek_from_event(event)

    def on_slider_drag(self, event):
        self.seek_from_event(event)

    def seek_from_event(self, event):
        w = self.slider.winfo_width()
        margin = 8
        draw_w = w - 2 * margin
        if draw_w <= 0: return
        
        click_x = event.x - margin
        ratio = click_x / draw_w
        ratio = max(0, min(1, ratio))
        self.current_time = ratio * self.song_length
        self.lbl_current_time.config(text=self.format_time(self.current_time))
        self.update_slider_display()

    def on_slider_release(self, event):
        self.is_dragging = False
        if self.is_playing and self.song_length > 0:
            try:
                pygame.mixer.music.play(start=self.current_time)
                self.start_time = self.current_time
            except Exception as e:
                print(f"Seek error: {e}")

    def update_slider_display(self):
        self.slider.delete("all")
        w = self.slider.winfo_width()
        h = self.slider.winfo_height()
        margin = 8
        draw_w = w - 2 * margin
        
        ratio = self.current_time / self.song_length if self.song_length > 0 else 0
        ratio = max(0, min(1, ratio))
        x = margin + (ratio * draw_w)
        cy = h / 2
        self.slider.create_line(margin, cy, w - margin, cy, fill="#535353", width=4, capstyle=tk.ROUND)
        if x > margin: self.slider.create_line(margin, cy, x, cy, fill="#FFFFFF", width=4, capstyle=tk.ROUND)
        self.slider.create_oval(x-6, cy-6, x+6, cy+6, fill="#FFFFFF", outline="")

    def format_time(self, seconds):
        minutes = int(seconds // 60)
        seconds = int(seconds % 60)
        return f"{minutes}:{seconds:02d}"

    def update_progress(self):
        if HAS_DEPS and self.is_playing and not self.is_dragging and self.song_length > 0:
            try:
                current_ms = pygame.mixer.music.get_pos()
                if current_ms != -1:
                    current_sec = (current_ms / 1000) + self.start_time
                    self.current_time = current_sec
                    self.lbl_current_time.config(text=self.format_time(current_sec))
                    self.update_slider_display()
            except Exception:
                pass
        self.root.after(500, self.update_progress)

root = tk.Tk()
app = HarmoniaApp(root)
root.mainloop()