"""A simulator for the subset of RS274NGC (LinuxCNC G-code) that the stencil quine uses.

    from ngcsim import run
    cuts = run(text)          # the closed loops cut while the laser is on

Written from the LinuxCNC documentation ("G-code overview", "O codes"):

- Lines are read with whitespace removed and letters upper-cased; there are no comments.
- Words: G0, G1, G21, G90 (G21 and G90 are accepted and ignored: millimetres, absolute), M2 (end),
  M3 (laser on), M5 (laser off), F, S, X, Y.
- Parameters: `#n=value`. All assignments on a line take effect after the line is read.
  `#n` and `#[expr]` read parameter n. Parameters #1-#30 are local to a subroutine call.
- Expressions: `[...]` with `**`, then `*` `/` `MOD`, then `+` `-`, then `EQ NE GT GE LT LE`, then
  `AND OR XOR`, all left associative; the function `FIX[...]` (round down).
- O-words: SUB/ENDSUB, CALL with `[arg]...`, WHILE/ENDWHILE, IF/ELSE/ENDIF.

Anything else raises `NgcError`, so the simulator never guesses. Moving with G0 while the laser is
on is an error too, since it would burn a path that is not part of the job.
"""

import math
import re


class NgcError(Exception):
    pass


NUM = re.compile(r'[+-]?(\d+\.?\d*|\.\d+)')
BINARY = [['**'], ['*', '/', 'MOD'], ['+', '-'], ['EQ', 'NE', 'GT', 'GE', 'LT', 'LE'],
          ['AND', 'OR', 'XOR']]


def apply(op, a, b):
    if op == '**': return a ** b
    if op == '*': return a * b
    if op == '/': return a / b
    if op == 'MOD': return math.fmod(a, b)
    if op == '+': return a + b
    if op == '-': return a - b
    if op == 'EQ': return float(a == b)
    if op == 'NE': return float(a != b)
    if op == 'GT': return float(a > b)
    if op == 'GE': return float(a >= b)
    if op == 'LT': return float(a < b)
    if op == 'LE': return float(a <= b)
    if op == 'AND': return float(a != 0 and b != 0)
    if op == 'OR': return float(a != 0 or b != 0)
    if op == 'XOR': return float((a != 0) != (b != 0))
    raise NgcError(op)


class Parser:
    """Parse one line into an AST; values are tuples evaluated by `Machine.value`."""

    def __init__(self, s):
        self.s, self.i = s, 0

    def peek(self, t):
        return self.s.startswith(t, self.i)

    def eat(self, t):
        if not self.peek(t):
            raise NgcError(f'expected {t!r} at {self.s[self.i:]!r} in {self.s!r}')
        self.i += len(t)

    def value(self):
        """A real value: number, parameter, [expression] or FIX[...]."""
        if self.peek('['):
            self.eat('[')
            e = self.expr(len(BINARY) - 1)
            self.eat(']')
            return e
        if self.peek('#'):
            self.eat('#')
            return ('param', self.value())
        if self.peek('FIX['):
            self.eat('FIX')
            return ('fix', self.value())
        m = NUM.match(self.s, self.i)
        if not m:
            raise NgcError(f'expected a value at {self.s[self.i:]!r}')
        self.i = m.end()
        return ('num', float(m.group()))

    def expr(self, level):
        if level < 0:
            return self.value()
        e = self.expr(level - 1)
        while True:
            for op in BINARY[level]:
                if self.peek(op):
                    self.eat(op)
                    e = ('op', op, e, self.expr(level - 1))
                    break
            else:
                return e

    def done(self):
        return self.i == len(self.s)


def parse_line(line):
    s = re.sub(r'\s', '', line).upper()
    if not s:
        return ('nop',)
    p = Parser(s)
    if s.startswith('O'):
        p.eat('O')
        m = re.compile(r'\d+').match(s, p.i)
        if not m:
            raise NgcError(f'bad O-word {s!r}')
        p.i = m.end()
        num = int(m.group())
        for kw in ['ENDSUB', 'SUB', 'CALL', 'ENDWHILE', 'WHILE', 'ENDIF', 'ELSE', 'IF']:
            if p.peek(kw):
                p.eat(kw)
                args = []
                if kw == 'CALL':
                    while p.peek('['):
                        args.append(p.value())
                elif kw in ('WHILE', 'IF'):
                    args.append(p.value())
                if not p.done():
                    raise NgcError(f'trailing text in {s!r}')
                return ('o', num, kw, args)
        raise NgcError(f'unknown O-word {s!r}')
    words, assigns = [], []
    while not p.done():
        if p.peek('#'):
            p.eat('#')
            n = p.value()
            p.eat('=')
            assigns.append((n, p.value()))
            continue
        letter = s[p.i]
        if letter not in 'GMFSXY':
            raise NgcError(f'unsupported word {letter!r} in {s!r}')
        p.i += 1
        words.append((letter, p.value()))
    return ('block', words, assigns)


class Machine:
    def __init__(self, text, max_steps=50_000_000):
        self.lines = [parse_line(l) for l in text.split('\n')]
        self.params = {}
        self.max_steps = max_steps
        self.subs, self.blocks = {}, {}
        self.index()
        self.x = self.y = 0.0
        self.motion = None
        self.laser = False
        self.cuts, self.path = [], None

    def index(self):
        """Match each O-word with the lines of its structure."""
        stack = []
        for i, l in enumerate(self.lines):
            if l[0] != 'o':
                continue
            _, num, kw, _ = l
            if kw in ('SUB', 'WHILE', 'IF'):
                stack.append((num, kw, i, []))
            elif kw == 'ELSE':
                if not stack or stack[-1][:2] != (num, 'IF'):
                    raise NgcError(f'unmatched O{num}ELSE')
                stack[-1][3].append(i)
            elif kw in ('ENDSUB', 'ENDWHILE', 'ENDIF'):
                if not stack or stack[-1][:2] != (num, kw[3:]):
                    raise NgcError(f'unmatched O{num}{kw}')
                _, opener, j, elses = stack.pop()
                self.blocks[j] = (elses[0] if elses else None, i)
                for e in elses:
                    self.blocks[e] = (None, i)
                self.blocks[i] = (None, j)
                if opener == 'SUB':
                    if num in self.subs:
                        raise NgcError(f'O{num} defined twice')
                    self.subs[num] = j
        if stack:
            raise NgcError(f'unclosed O{stack[-1][0]}{stack[-1][1]}')

    def get(self, n):
        n = int(n)
        if n != n or n < 1:
            raise NgcError(f'bad parameter #{n}')
        return self.params.get(n, 0.0)

    def value(self, e):
        kind = e[0]
        if kind == 'num': return e[1]
        if kind == 'param':
            n = self.value(e[1])
            if n != int(n):
                raise NgcError(f'parameter number {n} is not an integer')
            return self.get(n)
        if kind == 'fix': return float(math.floor(self.value(e[1])))
        if kind == 'op': return apply(e[1], self.value(e[2]), self.value(e[3]))
        raise NgcError(kind)

    def block(self, words, assigns):
        values = [(n, self.value(n), self.value(v)) for n, v in assigns]
        target = {}
        for letter, v in words:
            v = self.value(v)
            if letter == 'G':
                if v in (0, 1):
                    self.motion = int(v)
                elif v not in (21, 90):
                    raise NgcError(f'unsupported G{v:g}')
            elif letter == 'M':
                if v == 3:
                    self.laser, self.path = True, [(self.x, self.y)]
                elif v == 5:
                    if self.laser and len(self.path) > 1:
                        self.cuts.append(self.path)
                    self.laser, self.path = False, None
                elif v == 2:
                    return 'end'
                else:
                    raise NgcError(f'unsupported M{v:g}')
            elif letter in 'FS':
                pass
            else:
                target[letter] = v
        if target:
            if self.motion is None:
                raise NgcError('motion without G0 or G1')
            x, y = target.get('X', self.x), target.get('Y', self.y)
            if self.motion == 0 and self.laser:
                raise NgcError('G0 with the laser on')
            self.x, self.y = x, y
            if self.laser:
                self.path.append((x, y))
        for n, num, v in values:
            if num != int(num) or not 1 <= num <= 5399:
                raise NgcError(f'bad parameter #{num}')
            self.params[int(num)] = v

    def run(self):
        pc, frames, steps = 0, [], 0
        while pc < len(self.lines):
            steps += 1
            if steps > self.max_steps:
                raise NgcError('too many steps')
            l = self.lines[pc]
            if l[0] == 'nop':
                pc += 1
            elif l[0] == 'block':
                if self.block(l[1], l[2]) == 'end':
                    if frames:
                        raise NgcError('M2 inside a subroutine')
                    return self.cuts
                pc += 1
            else:
                _, num, kw, args = l
                if kw == 'SUB':
                    pc = self.blocks[pc][1] + 1          # definitions are skipped
                elif kw == 'ENDSUB':
                    pc, saved = frames.pop()
                    self.params.update(saved)
                elif kw == 'CALL':
                    if num not in self.subs:
                        raise NgcError(f'call of undefined O{num}')
                    vals = [self.value(a) for a in args]
                    saved = {i: self.params.get(i, 0.0) for i in range(1, 31)}
                    for i in range(1, 31):
                        self.params[i] = vals[i - 1] if i <= len(vals) else 0.0
                    frames.append((pc + 1, saved))
                    pc = self.subs[num] + 1
                elif kw == 'WHILE':
                    pc = pc + 1 if self.value(args[0]) else self.blocks[pc][1] + 1
                elif kw == 'ENDWHILE':
                    pc = self.blocks[pc][1]
                elif kw == 'IF':
                    other, end = self.blocks[pc]
                    skip = (other if other is not None else end) + 1
                    pc = pc + 1 if self.value(args[0]) else skip
                elif kw == 'ELSE':
                    pc = self.blocks[pc][1] + 1
                elif kw == 'ENDIF':
                    pc += 1
        raise NgcError('the program ends without M2')


def run(text):
    return Machine(text).run()
