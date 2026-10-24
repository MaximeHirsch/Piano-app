#!/usr/bin/env python3
"""
Piano Trainer — apprends tes morceaux avec la notation anglo-saxonne.

- Charge une partition MusicXML (.musicxml, .xml ou .mxl compressé).
- Les notes tombent vers le clavier, avec leur lettre (C D E F G A B) et le Do Ré Mi.
- Mode "attente" : la musique avance au tempo, puis s'arrête sur une note ou un
  accord tant que tu ne l'as pas joué(e).
- Joue avec un VRAI PIANO : l'appli t'écoute au micro et reconnaît les notes / accords attendus.
  (Le clavier de l'ordinateur, la souris et un clavier MIDI marchent aussi.)
- Choisis la taille de TON clavier : le morceau est transposé (en octaves) et les notes qui
  dépasseraient encore sont ramenées dans ta tessiture, pour que tout soit jouable.
- Tolérance sur les accords : on peut continuer même si seulement 2 notes sur 3 sont reconnues.
  Et « Passer » (bouton ou flèche →) saute une étape si vraiment ça ne passe pas.

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
CHORD_WINDOW = 0.6    # secondes max entre la 1re et la dernière note d'un accord
PARTIAL_GRACE = 0.5   # en mode tolérant : on laisse 0,5 s pour que les notes manquantes arrivent

# Tolérance sur les accords : nom affiché -> mode
TOLERANCES = {
    'Strict : toutes les notes': 0,
    'Souple : toutes sauf 1 (accords de 3+ notes)': 1,
    'Très souple : au moins la moitié des notes': 2,
}

# Tessiture des claviers (numéros MIDI, Do central = 60). Un clavier 61 touches sonne de C2 à C7.
KEYBOARDS = {
    '25 touches (2 octaves)': (48, 72),
    '37 touches (3 octaves)': (48, 84),
    '49 touches (4 octaves)': (36, 84),
    '61 touches (5 octaves)': (36, 96),
    '76 touches': (28, 103),
    '88 touches (piano)': (21, 108),
}


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

    Principe : un piano n'émet pas qu'une fréquence par note, mais une fondamentale + des
    harmoniques (×2, ×3, ×4…). On modélise chaque touche par son « peigne » d'harmoniques, puis
    on décompose le son entendu en somme de touches (moindres carrés non négatifs).
    Une *attaque* (hausse nette d'énergie) est exigée pour ne pas valider une note qui résonne encore.

    Robustesse au bruit grave (ventilateur, souffle, vibrations du micro d'ordinateur) :
      1. PLANCHER LOCAL : chaque pic est comparé au bruit de SA zone de fréquences (±4 demi-tons),
         et non à un bruit global. Un micro de portable a beaucoup de bruit dans les graves : avec
         un plancher global, ces graves ressemblaient à des « notes ».
      2. PROFIL DE BRUIT : on suit le minimum récent de chaque pic (statistiques de minimum) et on le
         retire. Un bruit continu disparaît, une frappe de piano (brève et forte) reste.
      3. CANDIDATS RESTREINTS : on ne cherche que les notes de l'étape en cours, de la précédente et
         de la suivante, plus leurs « confondeurs » (octaves, quintes, demi-tons voisins). Le bruit
         ne peut donc plus s'attribuer à des touches qui n'ont rien à voir avec le morceau.
    """
    RATE = 44100
    WIN = 16384            # ≈ 0,37 s d'analyse : assez fin pour séparer les graves
    NFFT = 65536
    GRID_LO = 21           # A0 : première case de la grille « demi-tons »
    GRID_N = 92            # … jusqu'à ≈ 5 kHz
    HARMS = (1, 2, 3, 4, 5, 6, 8)
    HW = {1: 1.0, 2: 0.9, 3: 0.8, 4: 0.6, 5: 0.5, 6: 0.4, 8: 0.3}
    NOISE_T = 6.0          # en dessous de 6× le bruit local, un pic est ignoré
    FLOOR_SEMI = 4         # demi-largeur (en demi-tons) de la zone du plancher de bruit local
    NOISE_RISE = 1.01      # le profil de bruit peut remonter de 1 % par analyse (≈ ×1,2 / s)
    NOISE_SUB = 0.9        # part du profil de bruit retirée des pics
    SPARSE = 1.0           # pénalité de parcimonie (évite les notes « fantômes »)
    SWIN = 4096            # fenêtre courte (≈ 93 ms) : sert uniquement à repérer les ATTAQUES
    SNFFT = 8192
    ONSET_RATIO = 1.3      # hausse minimale d'énergie pour compter une nouvelle frappe
    ONSET_HOLD = 0.5       # une frappe reste « valable » 0,5 s
    BASS_W = (0.4, 0.9)    # poids (fondamentale, 2e harmonique) du modèle des graves (< C3)
    BASS_REL = 0.3         # part minimale de la note la plus forte, pour les graves (< C3)
    REL_CUT = 0.15         # idem pour les autres notes (assez bas pour laisser passer les accords)
    THR_MIN = 2.0          # le seuil ne descend jamais sous cette valeur, même à sensibilité 10
    CONFUSERS = (0, 12, -12, 24, -24, 19, -19, 7, -7, 1, -1, 2, -2)

    def __init__(self, lo=36, hi=96):
        self.ring = np.zeros(self.RATE, dtype=np.float32)
        self.lock = threading.Lock()
        self.stream = None
        self.level = 0.0
        self.window = np.hanning(self.WIN).astype(np.float32)
        df = self.RATE / self.NFFT
        self.grid, self.floor_rng = [], []
        for k in range(self.GRID_N):
            f = 440 * 2 ** ((self.GRID_LO + k - 69) / 12)
            a = max(1, int(f * 2 ** (-0.5 / 12) / df))
            b = max(a + 1, int(math.ceil(f * 2 ** (0.5 / 12) / df)) + 1)
            self.grid.append((a, b))
            fa = max(1, int(f * 2 ** (-self.FLOOR_SEMI / 12) / df))
            fb = min(self.NFFT // 2, int(f * 2 ** (self.FLOOR_SEMI / 12) / df) + 1)
            if fb - fa < 24:
                fb = min(self.NFFT // 2, fa + 24)
            self.floor_rng.append((fa, fb))
        self.noise_prof = None
        self.swindow = np.hanning(self.SWIN).astype(np.float32)
        self.hist = collections.deque(maxlen=80)
        self.set_range(lo, hi)

    def set_range(self, lo, hi):
        """Notes possibles = touches du clavier (on ne cherche pas ce qu'on ne peut pas jouer)."""
        self.lo, self.hi = max(self.GRID_LO, int(lo)), min(108, int(hi))
        m_count = self.hi - self.lo + 1
        A = np.zeros((self.GRID_N, m_count))
        for j, m in enumerate(range(self.lo, self.hi + 1)):
            for h in self.HARMS:
                k = m + int(round(12 * math.log2(h))) - self.GRID_LO
                if k >= self.GRID_N:
                    continue
                w = self.HW[h]
                if m < 48 and h in (1, 2):    # graves : fondamentale faible (petits haut-parleurs) et peu précise
                    w = self.BASS_W[h - 1]
                A[k, j] += w
        self.A = A
        # bandes (±½ ton) des 6 premières harmoniques de chaque touche, pour repérer les attaques
        sdf = self.RATE / self.SNFFT
        idx, wts = [], []
        for m in range(self.lo, self.hi + 1):
            f0 = 440 * 2 ** ((m - 69) / 12)
            for h in range(1, 7):
                f = f0 * h
                if f > 5500:
                    idx += [1, 2]
                    wts.append(0.0)
                    continue
                a = max(1, int(f * 2 ** (-0.5 / 12) / sdf))
                b = max(a + 1, int(math.ceil(f * 2 ** (0.5 / 12) / sdf)) + 1)
                idx += [a, b]
                wts.append(1.0 / h ** 0.5)
        self.o_idx = np.array(idx)
        self.o_w = np.array(wts).reshape(m_count, 6)
        self.onset_t = np.full(m_count, -1e9)
        self.prev_jump = np.zeros(m_count, dtype=bool)
        self.noise_prof = None
        self.hist.clear()

    def mask_for(self, notes):
        """Touches à examiner : les notes données + leurs « confondeurs » (octaves, quintes, voisines)."""
        m = np.zeros(self.hi - self.lo + 1, dtype=bool)
        for n in notes:
            for d in self.CONFUSERS:
                k = n + d - self.lo
                if 0 <= k < len(m):
                    m[k] = True
        return m

    # -- flux audio
    def start(self, device=None):
        self.stop()
        self.noise_prof = None
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
    def analyze(self, samples=None, mask=None):
        """Retourne la « force » de chaque touche du clavier (vecteur de lo…hi, 0 hors candidats)."""
        if samples is None:
            with self.lock:
                samples = self.ring[-self.WIN:].copy()
        self.level = float(np.sqrt(np.mean(samples ** 2)))
        count = self.hi - self.lo + 1
        if self.level < 0.0008:                      # silence
            return np.zeros(count)
        spec = np.abs(np.fft.rfft((samples - samples.mean()) * self.window, self.NFFT))
        # 1) plancher de bruit LOCAL (médiane de la zone autour de chaque demi-ton)
        floors = np.array([np.median(spec[a:b]) for a, b in self.floor_rng]) + 1e-9
        peaks = np.array([spec[a:b].max() for a, b in self.grid]) / floors
        # 2) profil de bruit : minimum récent de chaque pic (bruit continu = reste bas, frappe = pic bref)
        if self.noise_prof is None:
            self.noise_prof = peaks.copy()
        else:
            self.noise_prof = np.minimum(self.noise_prof * self.NOISE_RISE, peaks)
        y = np.sqrt(np.maximum(peaks - self.NOISE_T - self.NOISE_SUB * self.noise_prof, 0.0))
        if not y.any():
            return np.zeros(count)
        # 3) uniquement les touches candidates
        if mask is None:
            idx = np.arange(count)
        else:
            idx = np.nonzero(mask)[0]
        if not len(idx):
            return np.zeros(count)
        A = self.A[:, idx]
        AtA = A.T @ A
        aty = A.T @ y
        x = np.ones(len(idx))
        for _ in range(120):                          # moindres carrés non négatifs (mises à jour multiplicatives)
            x *= aty / (AtA @ x + self.SPARSE)
        full = np.zeros(count)
        full[idx] = x
        return full

    def onset_energy(self, samples):
        """Énergie courte durée dans les harmoniques de chaque touche + niveau de bruit."""
        short = samples[-self.SWIN:]
        if len(short) < self.SWIN:
            short = np.concatenate([np.zeros(self.SWIN - len(short), dtype=np.float32), short])
        mag = np.abs(np.fft.rfft((short - short.mean()) * self.swindow, self.SNFFT))
        mx = np.maximum.reduceat(mag, self.o_idx)[::2].reshape(-1, 6)
        noise = float(np.median(mag[10:1000])) + 1e-9
        return (mx * self.o_w).sum(axis=1), 2.0 * noise * float(self.o_w[0].sum())

    def _thr(self, sens):
        """Seuil de force : sensibilité 5 → 2,4 ; la sensibilité 10 ne descend plus sous THR_MIN."""
        return max(self.THR_MIN, 12.0 / max(1, sens))

    def _strong(self, X, j, sens, rel):
        """La touche j est-elle assez forte (en absolu ET par rapport à la plus forte) ?"""
        thr = self._thr(sens)
        xmax = float(X.max()) if len(X) else 0.0
        return xmax >= thr and X[j] >= max(thr, rel * xmax)

    def decide(self, X, required, sens, now):
        """(notes attendues entendues avec attaque, ensemble des notes audibles)."""
        prev = [x for t, _o, x in self.hist if now - 0.13 <= t <= now - 0.04]
        heard = set()
        for n in required:
            j = n - self.lo
            if not 0 <= j < len(X):
                continue
            # une octave au-dessus d'une note demandée : ses harmoniques se confondent avec celles du dessous
            rel = (self.BASS_REL if n < 48 else self.REL_CUT) * (0.35 if (n - 12) in required else 1.0)
            if (self._strong(X, j, sens, rel) and prev
                    and all(self._strong(x, j, sens, rel) for x in prev)
                    and now - self.onset_t[j] <= self.ONSET_HOLD):
                heard.add(n)
        thr = self._thr(sens)
        xmax = float(X.max()) if len(X) else 0.0
        present = set()
        if xmax >= thr:
            present = {self.lo + int(j) for j in np.nonzero(X >= max(thr, self.REL_CUT * xmax))[0]}
        return heard, present

    def consume(self, notes):
        """Une frappe validée ne doit pas valider la note suivante : on l'oublie."""
        for n in notes:
            j = n - self.lo
            if 0 <= j < len(self.onset_t):
                self.onset_t[j] = -1e9

    def update(self, required, sens, now, samples=None, mask=None):
        if samples is None:
            with self.lock:
                samples = self.ring[-self.WIN:].copy()
        X = self.analyze(samples, mask)
        O, floor_o = self.onset_energy(samples)
        past = [o for t, o, _x in self.hist if now - 0.16 <= t <= now - 0.09]
        base = np.min(past, axis=0) if past else np.zeros_like(O)
        jump = (O >= self.ONSET_RATIO * np.maximum(base, floor_o))
        self.onset_t[jump & ~self.prev_jump] = now      # front montant = nouvelle frappe
        self.prev_jump = jump
        self.hist.append((now, O, X))
        return self.decide(X, required, sens, now)


# --------------------------------------------------------------------------- application
class PianoTrainer(tk.Tk):
    PPB = 80   # pixels par temps pour les notes qui tombent

    def __init__(self):
        super().__init__()
        self.title('Piano Trainer — notation anglo-saxonne')
        self.geometry('1100x740')
        self.minsize(800, 580)

        self.src_events = []          # morceau tel qu'écrit dans la partition
        self.events, self.onsets = [], []   # morceau adapté à ton clavier
        self.idx, self.pos = 0, 0.0
        self.playing = self.waiting = False
        self.wait_start = 0.0
        self.partial_since = None     # moment où assez de notes (mais pas toutes) ont été reconnues
        self.recent, self.flash = {}, {}
        self.down, self._rel = set(), {}
        self.range = (36, 96)
        self._geom, self._top, self._kbh = {}, 0, 100
        self._shown = None
        self._sounds = {}
        self.audio_ok = False
        self.midi_in = None

        self.mic = None
        self.mic_clock = 0.0
        self.mic_guess = None
        self.mic_present = set()
        self.mic_devices = []
        self.mic_on = tk.BooleanVar(value=False)
        self.mic_sens = tk.IntVar(value=5)
        self.mic_device = tk.StringVar(value='Micro par défaut')
        self.kb_choice = tk.StringVar(value='61 touches (5 octaves)')
        self.tol_choice = tk.StringVar(value=next(iter(TOLERANCES)))
        self.shift = tk.IntVar(value=0)
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
        self.bind_all('<Right>', self.on_skip_key)
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

        kb_row = ttk.Frame(self, padding=(12, 0, 12, 4))
        kb_row.pack(fill='x')
        ttk.Label(kb_row, text='Mon clavier').pack(side='left')
        kb_combo = ttk.Combobox(kb_row, textvariable=self.kb_choice, values=list(KEYBOARDS),
                                state='readonly', width=24)
        kb_combo.pack(side='left', padx=(6, 0))
        kb_combo.bind('<<ComboboxSelected>>', lambda _e: (self.on_kb_change(), self.canvas.focus_set()))
        ttk.Label(kb_row, text='Transposition (octaves)').pack(side='left', padx=(20, 4))
        ttk.Spinbox(kb_row, from_=-4, to=4, textvariable=self.shift, width=3, state='readonly',
                    command=self.on_shift_change).pack(side='left')
        ttk.Button(kb_row, text='Auto', command=self.on_auto_shift, takefocus=0).pack(side='left', padx=(6, 0))

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

        tol_row = ttk.Frame(self, padding=(12, 0, 12, 4))
        tol_row.pack(fill='x')
        ttk.Label(tol_row, text='Accords').pack(side='left')
        tol_combo = ttk.Combobox(tol_row, textvariable=self.tol_choice, values=list(TOLERANCES),
                                 state='readonly', width=42)
        tol_combo.pack(side='left', padx=(6, 0))
        tol_combo.bind('<<ComboboxSelected>>', lambda _e: (self.canvas.focus_set(), self.check_wait()))
        ttk.Button(tol_row, text='⏭ Passer (→)', command=self.skip, takefocus=0).pack(side='left', padx=(20, 0))

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
            self.mic_present = set()
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
                self.mic = MicListener(*self.kb_range())
            else:
                self.mic.set_range(*self.kb_range())
            device = next((i for i, name in self.mic_devices if name == self.mic_device.get()), None)
            self.mic.start(device)
            self.status.set('🎤 Écoute du piano activée — reste silencieux 1 s le temps de mesurer le bruit '
                            'ambiant, puis joue les notes en vert.')
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
        have = bool(self.events) and self.idx < len(self.events)
        required = set(self.events[self.idx]['notes']) if have else set()
        # notes candidates : étape précédente (encore en train de sonner), courante et suivante
        near, prev_notes = set(), set()
        for k in (self.idx - 1, self.idx, self.idx + 1):
            if 0 <= k < len(self.events):
                near |= set(self.events[k]['notes'])
        if 0 <= self.idx - 1 < len(self.events):
            prev_notes = set(self.events[self.idx - 1]['notes'])
        mask = self.mic.mask_for(near) if near else None
        try:
            sens = int(self.mic_sens.get())
        except (tk.TclError, ValueError):
            sens = 5
        heard, present = self.mic.update(required, sens, now, mask=mask)
        self.mic_present = present
        for n in present:                 # les touches entendues s'allument en bleu clair
            self.flash[n] = now
        if not (have and self.playing and self.wait_mode.get()):
            return
        # on accepte aussi une note jouée juste AVANT la ligne (0,35 s), pour ceux qui anticipent
        ahead = (self.events[self.idx]['beat'] - self.pos) * 60 / self.get_tempo()
        if not (self.waiting or ahead <= 0.35):
            return
        idx0 = self.idx
        for n in heard:
            if self.idx != idx0:
                break
            self.mark_heard(n)
        if self.waiting and self.idx == idx0 and not heard:
            related = {r + d for r in required for d in (12, -12, 24, -24, 19, -19)}   # harmoniques / octaves
            wrong = present - required - prev_notes - related
            if wrong:
                self.status.set('J’entends ' + ' '.join(note_name(x) for x in sorted(wrong)[:4])
                                + ' — attendu : ' + ' + '.join(note_name(x) for x in sorted(required)))

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
        self.src_events = events
        self.onsets = [e['beat'] for e in events]
        self.tempo.set(int(round(tempo)))
        self.idx = 0
        self.shift.set(self.best_shift())
        msg = self.adapt()
        notes = sorted(n for e in self.events for n in e['notes'])
        self.octave.set(max(1, min(6, notes[len(notes) // 2] // 12 - 1)))
        self.restart()
        self.status.set(f'{len(events)} étapes — tempo {self.get_tempo()} BPM. {msg} '
                        f'Appuie sur Lecture (ou Espace).')

    # ---- adaptation au clavier
    def kb_range(self):
        return KEYBOARDS.get(self.kb_choice.get(), (36, 96))

    def get_shift(self):
        try:
            return max(-4, min(4, int(self.shift.get())))
        except (tk.TclError, ValueError):
            return 0

    def best_shift(self):
        """Décalage en octaves qui laisse le moins de notes hors du clavier (puis le plus petit)."""
        lo, hi = self.kb_range()
        best = None
        for sh in range(-4, 5):
            out = sum(1 for e in self.src_events for n in e['notes'] if not lo <= n + 12 * sh <= hi)
            key = (out, abs(sh))
            if best is None or key < best[0]:
                best = (key, sh)
        return best[1] if best else 0

    def adapt(self):
        """Transpose le morceau (en octaves) puis ramène dans le clavier les notes qui dépassent encore."""
        lo, hi = self.kb_range()
        self.range = (lo, hi)
        shift = self.get_shift()
        folded = 0
        events = []
        for e in self.src_events:
            notes = {}
            for n, (dur, staff) in e['notes'].items():
                m = n + 12 * shift
                if not lo <= m <= hi:
                    folded += 1
                    while m < lo:
                        m += 12
                    while m > hi:
                        m -= 12
                old = notes.get(m)
                notes[m] = (max(dur, old[0]) if old else dur, staff)
            events.append({'beat': e['beat'], 'notes': notes})
        self.events = events
        self._shown = None
        self.listbox.delete(0, 'end')
        for i, e in enumerate(events):
            self.listbox.insert('end', f'{i + 1:>4}   ' + '  +  '.join(note_name(n) for n in sorted(e['notes'])))
        if self.mic:
            self.mic.set_range(lo, hi)
        keys = self.kb_choice.get().split(' (')[0]
        bits = []
        if shift:
            bits.append(f'transposé de {shift:+d} octave(s)')
        if folded:
            bits.append(f'{folded} note(s) ramenée(s) dans ta tessiture')
        return f'Clavier {keys} : ' + (', '.join(bits) if bits else 'le morceau tient tel quel') + '.'

    def on_kb_change(self):
        if not self.src_events:
            return
        self.shift.set(self.best_shift())
        self.status.set(self.adapt())

    def on_shift_change(self):
        if self.src_events:
            self.status.set(self.adapt())
        self.canvas.focus_set()

    def on_auto_shift(self):
        if self.src_events:
            self.shift.set(self.best_shift())
            self.status.set(self.adapt())
        self.canvas.focus_set()

    def restart(self):
        self.playing = self.waiting = False
        self.partial_since = None
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

    def on_skip_key(self, event):
        if isinstance(event.widget, (tk.Entry, ttk.Entry, ttk.Combobox, ttk.Spinbox)):
            return
        self.skip()
        return 'break'

    def skip(self):
        """Dernier recours : saute l'étape en cours (si une note ne veut vraiment pas être reconnue)."""
        if not (self.events and self.idx < len(self.events)):
            return
        if self.mic:
            self.mic.consume(list(self.events[self.idx]['notes']))
        for n in self.events[self.idx]['notes']:
            self.recent.pop(n, None)
        self.idx += 1
        self.waiting = False
        self.partial_since = None
        self.status.set('Étape passée ⏭')
        self.canvas.focus_set()

    def on_list_jump(self, _event):
        sel = self.listbox.curselection()
        if sel and self.events:
            self.idx = sel[0]
            self.pos = self.events[self.idx]['beat'] - 1
            self.waiting = False
            self.partial_since = None

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

    def needed(self, count):
        """Nombre de notes d'une étape à reconnaître pour continuer, selon la tolérance choisie."""
        mode = TOLERANCES.get(self.tol_choice.get(), 0)
        if mode == 1:
            return count - 1 if count >= 3 else count
        if mode == 2:
            return max(1, math.ceil(count / 2))
        return count

    def check_wait(self):
        if not (self.playing and self.waiting and self.idx < len(self.events)):
            return
        now = time.perf_counter()
        required = list(self.events[self.idx]['notes'])
        got = {n: self.recent[n] for n in required
               if self.recent.get(n) is not None and self.recent[n] >= self.wait_start - 0.5}
        if got:                                       # notes jouées « en même temps » (fenêtre d'accord)
            newest = max(got.values())
            got = {n: t for n, t in got.items() if newest - t <= CHORD_WINDOW}
        if len(got) < self.needed(len(required)):
            self.partial_since = None
            return
        if len(got) < len(required):                  # assez de notes, mais pas toutes : petit délai de grâce
            if self.partial_since is None:
                self.partial_since = now
            if now - self.partial_since < PARTIAL_GRACE:
                return
        for n in required:
            self.recent.pop(n, None)
        if self.mic:
            self.mic.consume(required)       # la frappe est « utilisée » : elle ne validera pas la note suivante
        self.idx += 1
        self.waiting = False
        self.partial_since = None
        if len(got) == len(required):
            self.status.set('Bien joué ✔')
        else:
            missing = ' + '.join(note_name(n) for n in sorted(set(required) - set(got)))
            self.status.set(f'OK ✔ ({len(got)}/{len(required)} notes reconnues — non entendue : {missing})')

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
                if self.waiting and self.partial_since is not None:
                    self.check_wait()                   # laisse finir le délai de grâce
                if self.waiting and not self.wait_mode.get():
                    self.waiting = False
                if not self.waiting:
                    self.pos += dt * self.get_tempo() / 60
                    while self.idx < len(self.events) and self.pos >= self.events[self.idx]['beat']:
                        ev = self.events[self.idx]
                        if self.wait_mode.get():
                            self.pos = ev['beat']
                            self.waiting = True
                            self.partial_since = None
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
            heard_txt = ' '.join(note_name(n) for n in sorted(self.mic_present)[:6]) or '…'
            c.create_text(10, 14, text='🎤 J’entends : ' + heard_txt, fill='#9fd8ff', anchor='w',
                          font=('Arial', 11, 'bold'))
            c.create_text(w - 150, 14, text='niveau', fill='#c9cee0', font=('Arial', 9))
            c.create_rectangle(w - 135, 8, w - 15, 20, outline='#69708a')
            c.create_rectangle(w - 135, 8, w - 135 + 120 * level, 20, fill='#5fe08a' if level < 0.9 else '#ff6b6b',
                               outline='')

        if not self.events:
            c.create_text(w / 2, top / 2, text='Ouvre une partition MusicXML ou lance le morceau de démo',
                          fill='#8a90a6', font=('Arial', 16))


if __name__ == '__main__':
    PianoTrainer().mainloop()