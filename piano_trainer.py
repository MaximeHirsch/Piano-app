#!/usr/bin/env python3
"""
Piano Trainer — apprends tes morceaux avec la notation anglo-saxonne.

- Charge une partition MusicXML (.musicxml, .xml ou .mxl compressé).
- Les notes tombent vers le clavier, avec leur lettre (C D E F G A B) et le Do Ré Mi.
- Mode "attente" : la musique avance au tempo, puis s'arrête sur une note ou un
  accord tant que tu ne l'as pas joué(e).
- Joue avec un VRAI PIANO : l'appli t'écoute au micro et reconnaît les notes / accords attendus.
  (Le clavier de l'ordinateur, la souris et un clavier MIDI marchent aussi.)

Dépendances :
  pip install pygame                 (son + MIDI, optionnel)
  pip install numpy sounddevice      (écoute du piano au micro)
"""
import array
import bisect
import collections
import io
import math
import sys
import threading
import time
import traceback
import wave
import zipfile
import tkinter as tk
from tkinter import filedialog, messagebox, ttk
import xml.etree.ElementTree as ET

try:
    import pygame
except ImportError:
    pygame = None

try:
    import numpy as np
except ImportError:
    np = None

try:
    import sounddevice as sd
except Exception:          # absent, ou PortAudio introuvable
    sd = None

LETTER_TO_SEMITONE = {'C': 0, 'D': 2, 'E': 4, 'F': 5, 'G': 7, 'A': 9, 'B': 11}
SEMITONE_NAMES = ['C', 'C#', 'D', 'D#', 'E', 'F', 'F#', 'G', 'G#', 'A', 'A#', 'B']
SOLFEGE = {'C': 'Do', 'D': 'Ré', 'E': 'Mi', 'F': 'Fa', 'G': 'Sol', 'A': 'La', 'B': 'Si'}
BLACK = {1, 3, 6, 8, 10}

# Touches du clavier d'ordinateur : demi-tons 0, 1, 2, ... à partir du Do de l'octave choisie
PC_KEYS = 'awsedftgyhujkolpm'
CHORD_WINDOW = 0.6   # secondes max entre la 1re et la dernière note d'un accord


# --------------------------------------------------------------------------- notes
def note_number(step, octave, alter=0):
    return (int(octave) + 1) * 12 + LETTER_TO_SEMITONE[step] + int(alter)


def note_name(n):
    return f'{SEMITONE_NAMES[n % 12]}{n // 12 - 1}'


def solfege(n):
    base = SEMITONE_NAMES[n % 12]
    return SOLFEGE[base[0]] + ('#' if '#' in base else '') + str(n // 12 - 1)


# --------------------------------------------------------------------------- MusicXML
def local(tag):
    return tag.rsplit('}', 1)[-1]


def find(el, name):
    return next((x for x in el if local(x.tag) == name), None)


def load_root(path):
    if zipfile.is_zipfile(path):                      # .mxl compressé
        with zipfile.ZipFile(path) as z:
            names = z.namelist()
            target = None
            if 'META-INF/container.xml' in names:
                container = ET.fromstring(z.read('META-INF/container.xml'))
                for el in container.iter():
                    if local(el.tag) == 'rootfile' and el.get('full-path'):
                        target = el.get('full-path')
                        break
            if target is None:
                target = next(n for n in names
                              if not n.startswith('META-INF') and n.lower().endswith(('.xml', '.musicxml')))
            return ET.fromstring(z.read(target))
    return ET.parse(path).getroot()


def parse_musicxml(path):
    """Retourne (événements, tempo). Un événement = notes jouées en même temps (accord, 2 mains)."""
    root = load_root(path)
    tempo = None
    for el in root.iter():
        if local(el.tag) == 'sound' and el.get('tempo'):
            tempo = float(el.get('tempo'))
            break
    if tempo is None:
        for el in root.iter():
            if local(el.tag) == 'per-minute' and el.text:
                try:
                    tempo = float(el.text)
                    break
                except ValueError:
                    pass
    tempo = tempo or 90

    onsets = {}   # beat -> {midi: (durée, portée)}
    for part in (p for p in root if local(p.tag) == 'part'):
        divisions, part_pos = 1.0, 0.0
        for measure in (m for m in part if local(m.tag) == 'measure'):
            cursor = longest = last_onset = 0.0
            for el in measure:
                tag = local(el.tag)
                if tag == 'attributes':
                    d = find(el, 'divisions')
                    if d is not None and d.text:
                        divisions = max(1.0, float(d.text))
                elif tag in ('backup', 'forward'):
                    d = find(el, 'duration')
                    amount = float(d.text) / divisions if d is not None and d.text else 0.0
                    cursor += amount if tag == 'forward' else -amount
                elif tag == 'note':
                    if find(el, 'grace') is not None:
                        continue
                    d = find(el, 'duration')
                    dur = float(d.text) / divisions if d is not None and d.text else 0.0
                    is_chord = find(el, 'chord') is not None
                    onset = last_onset if is_chord else cursor
                    if not is_chord:
                        last_onset = cursor
                        cursor += dur
                    pitch = find(el, 'pitch')
                    tied_stop = any(local(x.tag) == 'tie' and x.get('type') == 'stop' for x in el)
                    if pitch is not None and find(el, 'rest') is None and not tied_stop:
                        step = find(pitch, 'step').text
                        octave = find(pitch, 'octave').text
                        alter = find(pitch, 'alter')
                        number = note_number(step, octave, int(float(alter.text)) if alter is not None and alter.text else 0)
                        staff = find(el, 'staff')
                        staff = int(staff.text) if staff is not None and staff.text else 1
                        slot = onsets.setdefault(round(part_pos + onset, 4), {})
                        old = slot.get(number)
                        slot[number] = (max(dur, old[0]) if old else dur, staff)
                longest = max(longest, cursor)
            part_pos += longest
    if not onsets:
        raise ValueError('Aucune note trouvée dans ce fichier.')
    return [{'beat': b, 'notes': onsets[b]} for b in sorted(onsets)], tempo


def demo_song():
    melody = [64, 64, 65, 67, 67, 65, 64, 62, 60, 60, 62, 64, 64, 62, 62]
    durs = [1] * 12 + [1.5, 0.5, 2]
    events, t = [], 0.0
    for n, d in zip(melody, durs):
        events.append({'beat': t, 'notes': {n: (d, 1)}})
        t += d
    return events, 90


# --------------------------------------------------------------------------- son
def make_wav(midi, seconds=1.4):
    rate = 44100
    freq = 440 * 2 ** ((midi - 69) / 12)
    data = array.array('h')
    for i in range(int(rate * seconds)):
        t = i / rate
        env = min(1.0, i / (rate * 0.004)) * math.exp(-3.0 * t)
        w = 2 * math.pi * freq * t
        v = math.sin(w) + 0.5 * math.sin(2 * w) * math.exp(-2 * t) + 0.25 * math.sin(3 * w) * math.exp(-4 * t)
        data.append(int(7000 * env * v / 1.75))
    if sys.byteorder == 'big':
        data.byteswap()
    buf = io.BytesIO()
    with wave.open(buf, 'wb') as f:
        f.setnchannels(1)
        f.setsampwidth(2)
        f.setframerate(rate)
        f.writeframes(data.tobytes())
    buf.seek(0)
    return buf


# --------------------------------------------------------------------------- écoute micro
class MicListener:
    """Écoute le micro et vérifie quelles notes ATTENDUES viennent d'être jouées.

    On ne retranscrit pas tout à l'aveugle : pour chaque note attendue on mesure l'énergie
    à sa fréquence fondamentale (FFT), puis on exige une *attaque* (hausse nette par rapport
    aux ~0,9 s précédentes) pour ne pas valider une note encore en train de résonner.
    """
    RATE = 44100
    WIN = 12288            # ≈ 0,28 s d'analyse
    NFFT = 32768
    LO, HI = 21, 108       # A0 … C8

    def __init__(self):
        self.ring = np.zeros(self.RATE, dtype=np.float32)
        self.lock = threading.Lock()
        self.stream = None
        self.level = 0.0
        self.window = np.hanning(self.WIN).astype(np.float32)
        df = self.RATE / self.NFFT
        self.ranges = []
        for m in range(self.LO, self.HI + 1):
            f = 440 * 2 ** ((m - 69) / 12)
            a = max(1, int(f * 2 ** (-0.45 / 12) / df))
            b = int(math.ceil(f * 2 ** (0.45 / 12) / df)) + 1
            self.ranges.append((a, b))
        self.lo_bin, self.hi_bin = int(60 / df), int(4200 / df)
        self.hist = collections.deque(maxlen=60)

    # -- flux audio
    def start(self, device=None):
        self.stop()
        self.stream = sd.InputStream(samplerate=self.RATE, channels=1, dtype='float32',
                                     device=device, blocksize=1024, callback=self._callback)
        self.stream.start()

    def stop(self):
        if self.stream is not None:
            try:
                self.stream.stop()
                self.stream.close()
            except Exception:
                pass
            self.stream = None
        self.hist.clear()

    def _callback(self, indata, frames, _time, _status):
        x = indata[:, 0]
        with self.lock:
            self.ring = np.roll(self.ring, -len(x))
            self.ring[-len(x):] = x

    # -- analyse
    def analyze(self, samples=None):
        """Force de chaque note (A0…C8), en multiples du bruit de fond du spectre."""
        if samples is None:
            with self.lock:
                samples = self.ring[-self.WIN:].copy()
        self.level = float(np.sqrt(np.mean(samples ** 2)))
        if self.level < 0.002:                       # silence
            return np.zeros(self.HI - self.LO + 1)
        spec = np.abs(np.fft.rfft(samples * self.window, self.NFFT))
        floor = float(np.median(spec[self.lo_bin:self.hi_bin])) + 1e-9
        return np.array([spec[a:b].max() for a, b in self.ranges]) / floor

    def update(self, required, sens, now, samples=None):
        """Retourne (notes attendues entendues, note la plus grave audible ou None)."""
        P = self.analyze(samples)
        self.hist.append((now, P))
        thr = 80.0 / max(1, sens)                    # sensibilité 5 → seuil 16
        gmax = float(P.max())
        heard = set()
        for n in required:
            i = n - self.LO
            if not 0 <= i < len(P):
                continue
            s = P[i]
            if s < thr or s < 0.1 * gmax:
                continue
            # un vrai pic dépasse nettement ses voisines (sinon c'est le « clac » d'une autre note)
            if s < 4 * max(float(np.median(P[max(0, i - 6):i + 7])), 1.0):
                continue
            # harmonique d'une note plus grave (octave en dessous) ? on ne valide pas
            if i >= 12 and (n - 12) not in required and P[i - 12] > 1.2 * s:
                continue
            past = [p[i] for t, p in self.hist if now - 0.3 <= t <= now - 0.1]
            base = min(past) if past else 0.0
            if s >= 1.6 * max(base, 1.0):            # attaque nette
                heard.add(n)
        guess = None
        if gmax >= thr:
            for i in range(len(P)):
                left = P[i - 1] if i > 0 else 0
                right = P[i + 1] if i < len(P) - 1 else 0
                if P[i] >= 0.5 * gmax and P[i] >= left and P[i] >= right:
                    guess = i + self.LO
                    break
        return heard, guess


# --------------------------------------------------------------------------- application
class PianoTrainer(tk.Tk):
    PPB = 80   # pixels par temps pour les notes qui tombent

    def __init__(self):
        super().__init__()
        self.title('Piano Trainer — notation anglo-saxonne')
        self.geometry('1100x720')
        self.minsize(800, 560)

        self.events, self.onsets = [], []
        self.idx, self.pos = 0, 0.0
        self.playing = self.waiting = False
        self.wait_start = 0.0
        self.recent, self.flash = {}, {}
        self.down, self._rel = set(), {}
        self.range = (48, 84)
        self._geom, self._top, self._kbh = {}, 0, 100
        self._shown = None
        self._sounds = {}
        self.audio_ok = False
        self.midi_in = None

        self.mic = None
        self.mic_clock = 0.0
        self.mic_guess = None
        self.mic_devices = []
        self.mic_on = tk.BooleanVar(value=False)
        self.mic_sens = tk.IntVar(value=5)
        self.mic_device = tk.StringVar(value='Micro par défaut')
        self.tempo = tk.IntVar(value=90)
        self.octave = tk.IntVar(value=4)
        self.wait_mode = tk.BooleanVar(value=True)
        self.status = tk.StringVar(value='Ouvre un fichier MusicXML ou lance le morceau de démo.')

        self.setup_style()
        self.make_ui()
        self.init_audio()
        self.init_midi()

        self.bind_all('<KeyPress>', self.on_key_press)
        self.bind_all('<KeyRelease>', self.on_key_release)
        self.bind_all('<space>', self.on_space)
        self.protocol('WM_DELETE_WINDOW', self.on_close)
        self.last = time.perf_counter()
        self.tick()

    # ---- interface
    def setup_style(self):
        bg, fg = '#f2f3f7', '#1f2430'
        self.configure(bg=bg)
        s = ttk.Style(self)
        try:
            s.theme_use('clam')          # thème identique partout, couleurs respectées
        except tk.TclError:
            pass
        s.configure('.', background=bg, foreground=fg)
        s.configure('TFrame', background=bg)
        s.configure('TLabel', background=bg, foreground=fg)
        s.configure('TButton', padding=(10, 6), background='#e1e5ee', foreground=fg)
        s.map('TButton', background=[('active', '#cfd6e6')])
        s.configure('TCheckbutton', background=bg, foreground=fg)
        s.configure('TSpinbox', fieldbackground='white', foreground=fg)
        s.configure('Big.TLabel', font=('Arial', 40, 'bold'), foreground='#2457a6')
        s.configure('Sub.TLabel', font=('Arial', 16), foreground='#5a6275')
        s.configure('Status.TLabel', font=('Arial', 11), foreground='#3a4256')

    def make_ui(self):
        top = ttk.Frame(self, padding=(12, 10))
        top.pack(fill='x')
        for text, cmd in (('Ouvrir une partition', self.open_file), ('Morceau de démo', self.load_demo)):
            ttk.Button(top, text=text, command=cmd, takefocus=0).pack(side='left', padx=(0, 6))
        self.play_btn = ttk.Button(top, text='▶ Lecture', command=self.toggle, takefocus=0)
        self.play_btn.pack(side='left', padx=(12, 6))
        ttk.Button(top, text='↺ Recommencer', command=self.restart, takefocus=0).pack(side='left')

        ttk.Label(top, text='Tempo').pack(side='left', padx=(20, 4))
        ttk.Spinbox(top, from_=30, to=240, increment=5, textvariable=self.tempo, width=5,
                    command=lambda: self.canvas.focus_set()).pack(side='left')
        ttk.Label(top, text='Octave touches PC').pack(side='left', padx=(20, 4))
        ttk.Spinbox(top, from_=1, to=6, textvariable=self.octave, width=3, state='readonly',
                    command=lambda: self.canvas.focus_set()).pack(side='left')
        ttk.Checkbutton(top, text='Attendre la bonne note', variable=self.wait_mode,
                        takefocus=0).pack(side='left', padx=(20, 0))

        mic_row = ttk.Frame(self, padding=(12, 0, 12, 4))
        mic_row.pack(fill='x')
        ttk.Checkbutton(mic_row, text='🎤 Jouer sur un vrai piano (écoute au micro)', variable=self.mic_on,
                        command=self.toggle_mic, takefocus=0).pack(side='left')
        ttk.Label(mic_row, text='Sensibilité').pack(side='left', padx=(16, 4))
        ttk.Spinbox(mic_row, from_=1, to=10, textvariable=self.mic_sens, width=3, state='readonly',
                    command=lambda: self.canvas.focus_set()).pack(side='left')
        if sd is not None:
            try:
                self.mic_devices = [(i, d['name']) for i, d in enumerate(sd.query_devices())
                                    if d['max_input_channels'] > 0]
            except Exception:
                self.mic_devices = []
            names = ['Micro par défaut'] + [name for _i, name in self.mic_devices]
            combo = ttk.Combobox(mic_row, textvariable=self.mic_device, values=names,
                                 state='readonly', width=34)
            combo.pack(side='left', padx=(16, 0))
            combo.bind('<<ComboboxSelected>>', lambda _e: (self.toggle_mic(), self.canvas.focus_set()))

        ttk.Label(self, textvariable=self.status, style='Status.TLabel', padding=(12, 0)).pack(anchor='w')
        self.big = ttk.Label(self, text='—', style='Big.TLabel')
        self.big.pack(pady=(10, 0))
        self.small = ttk.Label(self, text='', style='Sub.TLabel')
        self.small.pack()

        self.canvas = tk.Canvas(self, bg='#1b1d26', highlightthickness=0, height=380)
        self.canvas.pack(fill='both', expand=True, padx=14, pady=10)
        self.canvas.bind('<Button-1>', self.on_click)
        self.canvas.focus_set()

        self.listbox = tk.Listbox(self, height=5, font=('Consolas', 12), bg='white', fg='#1f2430',
                                  selectbackground='#2457a6', selectforeground='white',
                                  highlightthickness=0, activestyle='none')
        self.listbox.pack(fill='x', padx=14, pady=(0, 12))
        self.listbox.bind('<Double-Button-1>', self.on_list_jump)

    # ---- audio / midi
    def init_audio(self):
        if pygame is None:
            self.status.set('pygame absent → pas de son. Installe-le avec : pip install pygame')
            return
        try:
            pygame.mixer.init(44100, -16, 1, 512)
            pygame.mixer.set_num_channels(32)
            self.audio_ok = True
        except Exception as exc:
            self.status.set(f'Son indisponible : {exc}')

    def init_midi(self):
        if pygame is None:
            return
        try:
            import pygame.midi as pm
            pm.init()
            for i in range(pm.get_count()):
                info = pm.get_device_info(i)
                if info[2] == 1:   # entrée
                    self.midi_in = pm.Input(i)
                    self.status.set(f'Clavier MIDI détecté : {info[1].decode(errors="ignore")}')
                    break
        except Exception:
            self.midi_in = None

    def play_sound(self, n):
        if not self.audio_ok:
            return
        try:
            snd = self._sounds.get(n)
            if snd is None:
                snd = self._sounds[n] = pygame.mixer.Sound(file=make_wav(n))
            snd.play()
        except Exception:
            pass

    def toggle_mic(self):
        if not self.mic_on.get():
            if self.mic:
                self.mic.stop()
            self.mic_guess = None
            self.status.set('Écoute micro désactivée.')
            return
        if np is None or sd is None:
            self.mic_on.set(False)
            messagebox.showinfo('Écoute micro indisponible',
                                "Il faut installer deux modules :\n\n    pip install numpy sounddevice\n\n"
                                "puis relancer l'application.")
            return
        try:
            if self.mic is None:
                self.mic = MicListener()
            device = next((i for i, name in self.mic_devices if name == self.mic_device.get()), None)
            self.mic.start(device)
            self.status.set('🎤 Écoute du piano activée — joue les notes en vert (vérifie la barre de niveau).')
        except Exception as exc:
            self.mic_on.set(False)
            messagebox.showerror('Micro inaccessible', str(exc))

    def mark_heard(self, n):
        now = time.perf_counter()
        self.flash[n] = now
        self.recent[n] = now
        self.check_wait()

    def process_mic(self, now):
        if not (self.mic_on.get() and self.mic and self.mic.stream):
            return
        if now - self.mic_clock < 0.05:
            return
        self.mic_clock = now
        required = set(self.events[self.idx]['notes']) if self.events and self.idx < len(self.events) else set()
        try:
            sens = int(self.mic_sens.get())
        except (tk.TclError, ValueError):
            sens = 5
        heard, guess = self.mic.update(required, sens, now)
        if guess is not None:
            self.flash[guess] = now
        if self.playing and self.waiting:
            for n in heard:
                self.mark_heard(n)
            if guess is not None and guess not in required and not heard and self.waiting:
                self.status.set(f'J’entends ~{note_name(guess)} — attendu : '
                                + ' + '.join(note_name(x) for x in sorted(required)))

    def on_close(self):
        try:
            if self.mic:
                self.mic.stop()
        except Exception:
            pass
        try:
            if self.midi_in:
                self.midi_in.close()
                import pygame.midi as pm
                pm.quit()
        except Exception:
            pass
        self.destroy()

    # ---- morceau
    def open_file(self):
        path = filedialog.askopenfilename(
            filetypes=[('MusicXML', '*.musicxml *.xml *.mxl'), ('Tous les fichiers', '*.*')])
        if not path:
            return
        try:
            events, tempo = parse_musicxml(path)
        except Exception as exc:
            messagebox.showerror('Partition illisible', str(exc))
            return
        self.set_song(events, tempo)

    def load_demo(self):
        self.set_song(*demo_song())

    def set_song(self, events, tempo):
        self.events = events
        self.onsets = [e['beat'] for e in events]
        notes = sorted(n for e in events for n in e['notes'])
        lo, hi = notes[0] // 12 * 12, (notes[-1] // 12 + 1) * 12
        if hi - lo < 24:
            hi = lo + 24
        self.range = (lo, hi)
        self.tempo.set(int(round(tempo)))
        self.octave.set(max(1, min(6, notes[len(notes) // 2] // 12 - 1)))
        self.listbox.delete(0, 'end')
        for i, e in enumerate(events):
            self.listbox.insert('end', f'{i + 1:>4}   ' + '  +  '.join(note_name(n) for n in sorted(e['notes'])))
        self.restart()
        self.status.set(f'{len(events)} étapes chargées — tempo {self.get_tempo()} BPM. '
                        f'Appuie sur Lecture (ou Espace).')

    def restart(self):
        self.playing = self.waiting = False
        self.idx = 0
        self.pos = (self.events[0]['beat'] - 3) if self.events else 0.0
        self.recent.clear()
        self.play_btn.config(text='▶ Lecture')
        if self.events:
            self.status.set('Prêt — appuie sur Lecture (ou Espace).')

    def toggle(self):
        if not self.events:
            return
        if self.idx >= len(self.events):
            self.restart()
        self.playing = not self.playing
        self.last = time.perf_counter()
        self.play_btn.config(text='⏸ Pause' if self.playing else '▶ Lecture')
        self.status.set('Joue les notes en vert !' if self.playing else 'En pause.')

    def on_space(self, event):
        if isinstance(event.widget, (tk.Entry, ttk.Entry)):
            return
        self.toggle()
        return 'break'

    def on_list_jump(self, _event):
        sel = self.listbox.curselection()
        if sel and self.events:
            self.idx = sel[0]
            self.pos = self.events[self.idx]['beat'] - 1
            self.waiting = False

    def get_tempo(self):
        try:
            return max(20, min(300, int(self.tempo.get())))
        except (tk.TclError, ValueError):
            return 90

    # ---- saisie
    def pc_map(self):
        try:
            base = (int(self.octave.get()) + 1) * 12
        except (tk.TclError, ValueError):
            base = 60
        return {ch: base + i for i, ch in enumerate(PC_KEYS)}

    def on_key_press(self, e):
        if isinstance(e.widget, (tk.Entry, ttk.Entry)):
            return
        k = e.keysym.lower()
        if k in self._rel:                      # répétition automatique de l'OS
            self.after_cancel(self._rel.pop(k))
        if k in self.down:
            return
        self.down.add(k)
        n = self.pc_map().get(k)
        if n is not None:
            self.note_on(n)

    def on_key_release(self, e):
        k = e.keysym.lower()

        def forget():
            self.down.discard(k)
            self._rel.pop(k, None)
        self._rel[k] = self.after(40, forget)

    def on_click(self, e):
        self.canvas.focus_set()
        if e.y < self._top:
            return
        black_h = self._kbh * 0.62
        hit = None
        if e.y <= self._top + black_h:
            hit = next((n for n, (x0, x1, blk) in self._geom.items() if blk and x0 <= e.x <= x1), None)
        if hit is None:
            hit = next((n for n, (x0, x1, blk) in self._geom.items() if not blk and x0 <= e.x < x1), None)
        if hit is not None:
            self.note_on(hit)

    def note_on(self, n):
        now = time.perf_counter()
        self.flash[n] = now
        self.recent[n] = now
        self.play_sound(n)
        if self.playing and self.waiting and self.idx < len(self.events):
            required = self.events[self.idx]['notes']
            if n not in required:
                self.status.set('Essaie encore : ' + ' + '.join(note_name(x) for x in sorted(required)))
            self.check_wait()

    def check_wait(self):
        if not (self.playing and self.waiting and self.idx < len(self.events)):
            return
        required = list(self.events[self.idx]['notes'])
        times = [self.recent.get(n) for n in required]
        if None in times:
            return
        if min(times) < self.wait_start - 0.2 or max(times) - min(times) > CHORD_WINDOW:
            return
        for n in required:
            self.recent.pop(n, None)
        self.idx += 1
        self.waiting = False
        self.status.set('Bien joué ✔')

    # ---- boucle principale
    def tick(self):
        self.after(25, self.tick)
        try:
            now = time.perf_counter()
            dt = min(now - self.last, 0.1)
            self.last = now
            self.poll_midi()
            self.process_mic(now)
            if self.playing:
                if self.waiting and not self.wait_mode.get():
                    self.waiting = False
                if not self.waiting:
                    self.pos += dt * self.get_tempo() / 60
                    while self.idx < len(self.events) and self.pos >= self.events[self.idx]['beat']:
                        ev = self.events[self.idx]
                        if self.wait_mode.get():
                            self.pos = ev['beat']
                            self.waiting = True
                            self.wait_start = now
                            self.check_wait()
                            break
                        for n in ev['notes']:           # mode écoute : l'appli joue
                            self.play_sound(n)
                            self.flash[n] = now
                        self.idx += 1
                if self.idx >= len(self.events) and not self.waiting:
                    self.playing = False
                    self.play_btn.config(text='▶ Lecture')
                    self.status.set('Terminé — bravo ! (Lecture pour rejouer)')
            self.sync_labels()
            self.draw()
        except Exception:
            traceback.print_exc()

    def poll_midi(self):
        if not self.midi_in:
            return
        try:
            if self.midi_in.poll():
                for (status, d1, d2, _), _ts in self.midi_in.read(32):
                    if status & 0xF0 == 0x90 and d2 > 0:
                        self.note_on(d1)
        except Exception:
            self.midi_in = None

    def sync_labels(self):
        key = (self.idx, bool(self.events))
        if key == self._shown:
            return
        self._shown = key
        if not self.events:
            self.big.config(text='—')
            self.small.config(text='')
        elif self.idx >= len(self.events):
            self.big.config(text='Terminé !')
            self.small.config(text='')
        else:
            notes = sorted(self.events[self.idx]['notes'])
            self.big.config(text='  +  '.join(note_name(n) for n in notes))
            self.small.config(text='  +  '.join(solfege(n) for n in notes))
            self.listbox.selection_clear(0, 'end')
            self.listbox.selection_set(self.idx)
            self.listbox.see(self.idx)

    # ---- dessin
    def layout(self, width):
        lo, hi = self.range
        whites = [n for n in range(lo, hi + 1) if n % 12 not in BLACK]
        kw = width / len(whites)
        geom, seen = {}, 0
        for n in range(lo, hi + 1):
            if n % 12 in BLACK:
                cx = seen * kw
                geom[n] = (cx - kw * 0.3, cx + kw * 0.3, True)
            else:
                geom[n] = (seen * kw, (seen + 1) * kw, False)
                seen += 1
        return geom, kw

    def draw(self):
        c = self.canvas
        w, h = c.winfo_width(), c.winfo_height()
        if w < 100 or h < 150:
            return
        c.delete('all')
        now = time.perf_counter()
        kbh = max(100, int(h * 0.28))
        top = h - kbh
        geom, kw = self.layout(w)
        self._geom, self._top, self._kbh = geom, top, kbh
        black_h = kbh * 0.62
        ppb = self.PPB

        required = set()
        if self.events and self.idx < len(self.events):
            required = set(self.events[self.idx]['notes'])

        # repères : octaves et temps
        for n, (x0, _x1, blk) in geom.items():
            if n % 12 == 0:
                c.create_line(x0, 0, x0, top, fill='#262a38')
        for b in range(math.floor(self.pos), math.ceil(self.pos + top / ppb) + 1):
            y = top - (b - self.pos) * ppb
            if 0 <= y <= top:
                c.create_line(0, y, w, y, fill='#262a38')

        # notes qui tombent
        if self.events:
            i = bisect.bisect_left(self.onsets, self.pos - 8)
            while i < len(self.events):
                ev = self.events[i]
                yb = top - (ev['beat'] - self.pos) * ppb
                if yb < 0:
                    break
                for n, (dur, staff) in ev['notes'].items():
                    if n not in geom:
                        continue
                    yt = yb - dur * ppb + 3
                    if yt >= top:
                        continue
                    x0, x1, _ = geom[n]
                    color = '#5fe08a' if i == self.idx else ('#ffb347' if staff == 2 else '#4da3ff')
                    y_bot = min(yb, top) - 1
                    c.create_rectangle(x0 + 2, max(yt, -5), x1 - 2, y_bot, fill=color, outline='')
                    if y_bot - max(yt, 0) > 18 and kw > 14:
                        c.create_text((x0 + x1) / 2, y_bot - 9, text=SEMITONE_NAMES[n % 12],
                                      fill='#0b1020', font=('Arial', max(7, min(11, int(kw / 3))), 'bold'))
                i += 1

        c.create_line(0, top, w, top, fill='#5fe08a' if self.waiting else '#69708a', width=2)

        pc_letters = {n: ch.upper() for ch, n in self.pc_map().items()}
        fs = max(7, min(11, int(kw / 3)))

        def fill_for(n, blk):
            t = self.flash.get(n)
            if t is not None and now - t < 0.25:
                return '#7cc4ff'
            if n in required:
                return '#5fe08a'
            return '#111111' if blk else '#fafafa'

        for n, (x0, x1, blk) in geom.items():
            if blk:
                continue
            c.create_rectangle(x0, top, x1, h, fill=fill_for(n, False), outline='#8a8f9c')
            label = note_name(n) if n % 12 == 0 else SEMITONE_NAMES[n % 12]
            c.create_text((x0 + x1) / 2, h - 14, text=label, fill='#444', font=('Arial', fs))
            if n in pc_letters:
                c.create_text((x0 + x1) / 2, h - 34, text=pc_letters[n], fill='#2457a6',
                              font=('Arial', fs, 'bold'))
        for n, (x0, x1, blk) in geom.items():
            if not blk:
                continue
            c.create_rectangle(x0, top, x1, top + black_h, fill=fill_for(n, True), outline='#000')
            if n in pc_letters:
                c.create_text((x0 + x1) / 2, top + black_h - 12, text=pc_letters[n], fill='#9db8ff',
                              font=('Arial', fs, 'bold'))

        if self.mic_on.get() and self.mic and self.mic.stream:
            level = min(1.0, self.mic.level * 15)
            c.create_text(w - 150, 14, text='🎤', fill='#c9cee0', font=('Arial', 11))
            c.create_rectangle(w - 135, 8, w - 15, 20, outline='#69708a')
            c.create_rectangle(w - 135, 8, w - 135 + 120 * level, 20, fill='#5fe08a' if level < 0.9 else '#ff6b6b',
                               outline='')

        if not self.events:
            c.create_text(w / 2, top / 2, text='Ouvre une partition MusicXML ou lance le morceau de démo',
                          fill='#8a90a6', font=('Arial', 16))


if __name__ == '__main__':
    PianoTrainer().mainloop()