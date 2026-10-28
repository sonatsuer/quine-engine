"""Empirical checks for the Python Morse quine.

    python3 check.py [file.py]

The default file is morse.py in this folder, written by `lake exe quine`, together with morse.txt,
the Morse code that Lean's `render` predicts. The program runs with a stand-in for tkinter that
records the window's colour changes and the delays between them, without opening a window. The
recorded light is then decoded as Morse code by timing alone.

morse.txt lists the code of each character, separated by spaces, with `/` for a space and a line
break after each line-break code (`.-.-`, the prosign AA).
"""

import os
import random
import sys
import types

HERE = os.path.dirname(os.path.abspath(__file__))
UNIT = 60                                   # ms
KEYS = 'abcdefghijklmnopqrstuvwxyz0123456789.,?!/()&:;=+-_$@"\'\n '
CODES = ('.- -... -.-. -.. . ..-. --. .... .. .--- -.- .-.. -- -. --- .--. --.- .-. ... - ..- ...- '
         '.-- -..- -.-- --.. ----- .---- ..--- ...-- ....- ..... -.... --... ---.. ----. .-.-.- '
         '--..-- ..--.. -.-.-- -..-. -.--. -.--.- .-... ---... -.-.-. -...- .-.-. -....- ..--.- '
         '...-..- .--.-. .-..-. .----. .-.-').split() + ['']
MORSE = dict(zip(KEYS, CODES))      # International Morse (ITU-R M.1677-1), with ! $ _ and AA
READ = {w: ch for ch, w in MORSE.items()}
START, END = '-.-.-', '...-.-'      # the prosigns KA and SK
with open(os.path.join(HERE, 'morse.py.inc'), encoding='ascii') as f:
    LIB = f.read()


class Window:
    """Records `configure(bg=…)` and runs `after` callbacks in order, on a virtual clock."""

    def __init__(self):
        self.now, self.light, self.queue, self.trace = 0, None, [], []

    def title(self, _): pass
    def geometry(self, _): pass

    def configure(self, bg):
        if bg not in ('white', 'black'):
            raise SystemExit(f'unexpected colour {bg!r}')
        self.trace.append((self.now, bg == 'white'))

    def after(self, ms, f):
        self.queue.append((self.now + ms, f))

    def destroy(self):
        self.destroyed = self.now

    def mainloop(self):
        while self.queue:
            self.queue.sort(key=lambda e: e[0])
            self.now, f = self.queue.pop(0)
            f()


def record(source):
    """Run a program and return the light as a list of (on, duration in units)."""
    windows = []
    stub = types.ModuleType('tkinter')
    stub.Tk = lambda: windows.append(Window()) or windows[-1]
    saved = sys.modules.get('tkinter')
    sys.modules['tkinter'] = stub
    try:
        exec(compile(source, 'quine', 'exec'), {'__name__': '__main__'})
    finally:
        if saved is not None:
            sys.modules['tkinter'] = saved
        else:
            del sys.modules['tkinter']
    if len(windows) != 1:
        raise SystemExit('the program must open exactly one window')
    w = windows[0]
    trace = w.trace + [(w.destroyed, False)]
    spans = []
    for (t0, on), (t1, _) in zip(trace, trace[1:]):
        if t1 > t0:
            if spans and spans[-1][0] == on:
                spans[-1] = (on, spans[-1][1] + t1 - t0)
            else:
                spans.append((on, t1 - t0))
    if spans and not spans[0][0]:
        spans = spans[1:]                   # the dark wait before the message
    for _, d in spans:
        if d % UNIT:
            raise SystemExit(f'a duration of {d} ms is not a whole number of units')
    return [(on, d // UNIT) for on, d in spans]


def decode(spans):
    """Decode the light by timing: dot 1, dash 3; gaps 1 (in a letter), 3 (between letters),
    and 4 more per space. Returns the words between the starting and ending prosigns."""
    words, word = [], ''
    for on, d in spans:
        if on:
            if d not in (1, 3):
                raise SystemExit(f'a flash of {d} units')
            word += '.' if d == 1 else '-'
        elif d != 1:
            if (d - 3) % 4 or d < 3:
                raise SystemExit(f'a gap of {d} units')
            words.append(word)
            words += [''] * ((d - 3) // 4)
            word = ''
    if word:
        words.append(word)
    if not words or words[0] != START or words[-1] != END:
        raise SystemExit('the message is not framed by ka and sk')
    return words[1:-1]


def fmt(words):
    return ''.join(('/' if w == '' else w) + ('\n' if w == MORSE['\n'] else ' ') for w in words)


def read(words):
    if any(w not in READ for w in words):
        raise SystemExit('an unknown Morse code')
    return ''.join(READ[w] for w in words)


def quoted(t):
    """Lean's `quoteWith`: a file that binds `t`, in hexadecimal, to `v` and blinks it."""
    return 'v=bytes.fromhex("' + t.encode().hex() + '").decode();exec("""' + LIB + 'blink(v)""")\n'


def check_library():
    rng = random.Random(1)
    tests = [KEYS, ' ' + KEYS[::-1] + '  x', 'e']
    for _ in range(8):
        tests.append(''.join(rng.choice(KEYS) for _ in range(rng.randrange(1, 200))))
    for t in tests:
        if read(decode(record(quoted(t)))) != t:
            raise SystemExit(f'library: the blinking of {t!r} does not decode to it')
    print(f'library: {len(tests)} texts, including every character, blink their own Morse code')


def check_quine(path):
    with open(path, encoding='ascii') as f:
        source = f.read()
    spans = record(source)
    words = decode(spans)
    predicted = os.path.join(os.path.dirname(path), 'morse.txt')
    if os.path.exists(predicted):
        with open(predicted, encoding='ascii') as f:
            if fmt(words) != f.read():
                raise SystemExit(f'{path}: the blinking differs from morse.txt (Lean)')
        print(f'{path}: the blinking is morse.txt, as Lean predicts')
    if read(words) != source:
        raise SystemExit(f'{path}: the blinking does not decode to the source')
    minutes = sum(d for _, d in spans) * UNIT / 60000
    print(f'{path}: {len(source)} characters blink for {minutes:.0f} minutes and decode to the '
          'source')


check_library()
check_quine(sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, 'morse.py'))
