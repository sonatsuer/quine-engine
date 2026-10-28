"""Empirical checks for the Verilog quine.

    python3 check.py [file.v]

The default file is quine.v in this folder, written by `lake exe quine`. With it comes quine.txt,
the frames that Lean's `render` predicts: one line of ten bits per byte, start bit first.

Each file is simulated with Icarus Verilog (`iverilog -g2012`, then `vvp`), which writes the tx
pin to quine.vcd. The pin is then decoded in two ways:
- by this script, as asynchronous serial: from each falling edge, it samples ten bits at their
  centres;
- by sigrok's UART decoder, an independent one, if `sigrok-cli` is installed.

If Yosys is installed, the circuit is also synthesized, to show that it is hardware and not only
a simulation.
"""

import bisect
import os
import random
import re
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
BAUD = 9600
with open(os.path.join(HERE, 'code-a.v.inc'), encoding='ascii') as f:
    CODE_A = f.read()
with open(os.path.join(HERE, 'code-b.v.inc'), encoding='ascii') as f:
    CODE_B = f.read()


def esc(t):
    return t.replace('\\', '\\\\').replace('"', '\\"').replace('\n', '\\n')


def sub(c, x):
    """Lean's `sub`: the `define` line holding `x`, then the code `c`."""
    return '`define s "' + esc(x) + '"\n' + c


def simulate(source, d):
    """Simulate a file in directory `d`; return the path of the VCD it writes."""
    path = os.path.join(d, 'quine.v')
    with open(path, 'w', encoding='ascii') as f:
        f.write(source)
    r = subprocess.run(['iverilog', '-g2012', '-o', 'sim', 'quine.v'], cwd=d,
                       capture_output=True, text=True)
    if r.returncode:
        raise SystemExit(f'iverilog failed:\n{r.stderr}')
    r = subprocess.run(['vvp', '-n', 'sim'], cwd=d, capture_output=True, text=True)
    if r.returncode:
        raise SystemExit(f'vvp failed:\n{r.stderr}')
    return os.path.join(d, 'quine.vcd')


def read_vcd(path):
    """The tx pin as (times, values) of its changes, and the time unit in seconds."""
    with open(path, encoding='ascii') as f:
        text = f.read()
    m = re.search(r'\$timescale\s*(\d+)\s*(s|ms|us|ns|ps|fs)\s*\$end', text)
    unit = int(m.group(1)) * {'s': 1, 'ms': 1e-3, 'us': 1e-6, 'ns': 1e-9, 'ps': 1e-12,
                              'fs': 1e-15}[m.group(2)]
    ident = re.search(r'\$var\s+\w+\s+1\s+(\S+)\s+tx\s', text).group(1)
    times, values, now = [], [], 0
    for line in text[text.index('$enddefinitions'):].split('\n')[1:]:
        line = line.strip()
        if line.startswith('#'):
            now = int(line[1:])
        elif line[1:] == ident and line[0] in '01':
            times.append(now)
            values.append(int(line[0]))
    return times, values, unit


def decode(times, values, unit):
    """Decode 8N1 serial: from each falling edge, sample the ten bits at their centres."""
    period = 1 / BAUD / unit
    level = lambda t: values[bisect.bisect_right(times, t) - 1]
    if values[0] != 1 or values[-1] != 1:
        raise SystemExit('the line does not start and end idle')
    frames, t = [], 0
    while True:
        k = bisect.bisect_right(times, t)
        falls = [times[j] for j in range(k, len(times)) if values[j] == 0]
        if not falls:
            break
        t0 = falls[0]
        w = [level(t0 + (b + 0.5) * period) for b in range(10)]
        if w[0] != 0 or w[9] != 1:
            raise SystemExit(f'a frame without its start or stop bit at {t0 * unit:.6f} s')
        frames.append(w)
        t = t0 + 9.5 * period
    return frames


def read(frames):
    return bytes(sum(b << i for i, b in enumerate(w[1:9])) for w in frames).decode('ascii')


def sigrok(vcd):
    """Decode the pin with sigrok's UART decoder; None if sigrok-cli is not installed."""
    exe = shutil.which('sigrok-cli')
    if exe is None:
        return None
    # libsigrok's VCD reader stops at Icarus's `$comment` and `$dumpall` blocks, which carry no
    # signal data, so they are dropped from a copy. The VCD is in picoseconds; 1 MHz suffices.
    with open(vcd, encoding='ascii') as f:
        text = f.read()
    text = re.sub(r'\$comment.*?\$end\n', '', text, flags=re.S)
    text = re.sub(r'\$dumpall\s*\$end\n', '', text)
    vcd = vcd + '.sigrok'
    with open(vcd, 'w', encoding='ascii') as f:
        f.write(text)
    r = subprocess.run([exe, '-I', 'vcd:downsample=1000000', '-i', vcd,
                        '-P', f'uart:rx=tx:baudrate={BAUD}:format=hex', '-A', 'uart=rx-data'],
                       capture_output=True, text=True)
    if r.returncode:
        raise SystemExit(f'sigrok-cli failed:\n{r.stderr}')
    return bytes(int(x, 16) for x in re.findall(r'\b([0-9A-Fa-f]{2})\b', r.stdout)).decode(
        'latin1')


def yosys(source, d):
    """Synthesize the circuit with Yosys; False if Yosys is not installed."""
    exe = shutil.which('yosys')
    if exe is None:
        return False
    path = os.path.join(d, 'synth.v')
    with open(path, 'w', encoding='ascii') as f:
        f.write(source)
    r = subprocess.run([exe, '-q', '-p', 'read_verilog -sv synth.v; synth -top quine'], cwd=d,
                       capture_output=True, text=True)
    if r.returncode:
        raise SystemExit(f'yosys failed:\n{r.stdout}{r.stderr}')
    return True


def check_library():
    """The show code (`full = 0`) sends its data: Lean's `quoteWith`."""
    rng = random.Random(1)
    every = ''.join(map(chr, range(32, 127))) + '\n'
    tests = [every, every[::-1], 'e', '"\\\n\\n"']
    for _ in range(4):
        tests.append(''.join(rng.choice(every) for _ in range(rng.randrange(1, 200))))
    by_sigrok = 0
    with tempfile.TemporaryDirectory() as d:
        for t in tests:
            vcd = simulate(sub(CODE_A + '0' + CODE_B, t), d)
            if read(decode(*read_vcd(vcd))) != t:
                raise SystemExit(f'library: the pin of {t!r} does not decode to it')
            got = sigrok(vcd)
            if got is not None:
                if got != t:
                    raise SystemExit(f'library: sigrok decodes the pin of {t!r} as {got!r}')
                by_sigrok += 1
    print(f'library: {len(tests)} texts, including every character, are sent on the pin'
          + (f'; sigrok agrees on all {by_sigrok}' if by_sigrok else ''))


def check_quine(path):
    with open(path, encoding='ascii') as f:
        source = f.read()
    with tempfile.TemporaryDirectory() as d:
        vcd = simulate(source, d)
        times, values, unit = read_vcd(vcd)
        frames = decode(times, values, unit)
        predicted = os.path.join(os.path.dirname(path), 'quine.txt')
        if os.path.exists(predicted):
            with open(predicted, encoding='ascii') as f:
                if ''.join(''.join(map(str, w)) + '\n' for w in frames) != f.read():
                    raise SystemExit(f'{path}: the frames differ from quine.txt (Lean)')
            print(f'{path}: the frames are quine.txt, as Lean predicts')
        if read(frames) != source:
            raise SystemExit(f'{path}: the pin does not decode to the source')
        print(f'{path}: {len(source)} bytes, sent in {times[-1] * unit:.1f} s of simulated '
              'time, decode to the source')
        got = sigrok(vcd)
        if got is None:
            print('sigrok-cli is not installed; skipped the independent decoder')
        elif got != source:
            raise SystemExit(f'{path}: sigrok decodes the pin differently ({len(got)} bytes)')
        else:
            print(f'{path}: sigrok decodes the pin to the source')
        if yosys(source, d):
            print(f'{path}: Yosys synthesizes the circuit')
        else:
            print('Yosys is not installed; skipped synthesis')


check_library()
check_quine(sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, 'quine.v'))
