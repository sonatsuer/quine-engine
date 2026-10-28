#!/usr/bin/env python3
"""Generate stencil.ngc.inc from the 5x7 font of the SvgText quine.

    python3 gen_stencil.py

The library is RS274NGC (LinuxCNC G-code). It holds the glyphs of the alphabet below as parameters
#2002-#2040 (bit 5*r + c is pixel (c, r), with r counted from the top), and defines:

- O7, which cuts one bar: pixels #1..#2 of row #3 in the current cell;
- O1, which cuts the character with code #1 at the current cell and advances (code 1 is newline);
- O8, which cuts the number #1 in #2 decimal digits;
- O100, which cuts the text stored in #1001, #1002, ... (7 two-digit codes each, up to a zero
  parameter), preceded in mode #1 = 1 by the text of the data lines themselves.

The quine ends with `O100CALL[m]` and `M2`, which Lean appends. Every line is at most 32
characters, and only characters of the alphabet occur.
"""

from pathlib import Path

HERE = Path(__file__).resolve().parent
ALPHABET = '\n0123456789#=[].-+*/ABCDEFGHILMNOQSTUWXY'   # code of ALPHABET[i] is i + 1
PITCH = 0.6           # pixel pitch (mm); a cell is 6 x 9 pixels
ROWS = 80             # rows of text to a column
COLUMN = 120          # column pitch (mm): 32 cells and a margin, 200 pixels

glyph = {}
for line in (HERE.parent / 'SvgText' / 'font5x7.txt').read_text().splitlines():
    code, *rows = line.split(' ')
    glyph[chr(int(code, 16))] = sum(1 << (5 * r + c) for r, row in enumerate(rows)
                                    for c, ch in enumerate(row) if ch == '#')

font = [f'#{2001 + i}={glyph[ch]}' for i, ch in enumerate(ALPHABET) if ch != '\n']

LIBRARY = f'''G21G90F600S1000
{chr(10).join(font)}
O7SUB
#4=[FIX[#3001/{ROWS}]*{COLUMN}]
#4=[#4+#3002*{6 * PITCH:g}]
#5=[#4+#1*{PITCH:g}+.06]
#6=[#4+#2*{PITCH:g}+.54]
#7=[[#3001MOD{ROWS}]*{9 * PITCH:g}]
#7=[0-#7-#3*{PITCH:g}-.12]
#8=[#7-.36]
G0X#5Y#7
M3
G1X#6
Y#8
X#5
Y#7
M5
O7ENDSUB
O1SUB
O2IF[#1EQ1]
#3002=0
#3001=[#3001+1]
O2ELSE
#2=#[2000+#1]
#3=0
O3WHILE[#3LT7]
#5=-1
#4=0
O4WHILE[#4LE5]
#8=0
O5IF[#4LT5]
#8=[FIX[#2/2**[5*#3+#4]]MOD2]
O5ENDIF
O6IF[[#8EQ1]AND[#5LT0]]
#5=#4
O6ENDIF
O9IF[[#8EQ0]AND[#5GE0]]
O7CALL[#5][#4-1][#3]
#5=-1
O9ENDIF
#4=[#4+1]
O4ENDWHILE
#3=[#3+1]
O3ENDWHILE
#3002=[#3002+1]
O2ENDIF
O1ENDSUB
O8SUB
#3=[#2-1]
O11WHILE[#3GE0]
#4=[FIX[#1/10**#3]MOD10]
O1CALL[#4+2]
#3=[#3-1]
O11ENDWHILE
O8ENDSUB
O100SUB
#3001=0
#3002=0
O101IF[#1EQ1]
#10=1001
#13=1
O102WHILE[#13EQ1]
O1CALL[12]
O8CALL[#10][4]
O1CALL[13]
O8CALL[#[#10]][14]
O1CALL[1]
#13=[#[#10]NE0]
#10=[#10+1]
O102ENDWHILE
O101ENDIF
#10=1001
O103WHILE[#[#10]NE0]
#14=#[#10]
#11=6
O104WHILE[#11GE0]
#12=[FIX[#14/100**#11]MOD100]
O105IF[#12NE0]
O1CALL[#12]
O105ENDIF
#11=[#11-1]
O104ENDWHILE
#10=[#10+1]
O103ENDWHILE
O100ENDSUB
'''

if __name__ == '__main__':
    assert ALPHABET.index('0') == 1 and ALPHABET.index('#') == 11 and ALPHABET.index('=') == 12
    for line in LIBRARY.split('\n'):
        assert len(line) <= 32, line
    assert set(LIBRARY) <= set(ALPHABET), set(LIBRARY) - set(ALPHABET)
    (HERE / 'stencil.ngc.inc').write_text(LIBRARY)
    print(f'wrote stencil.ngc.inc ({len(LIBRARY)} bytes)')
