# A Python program that prints itself in braille.
#
# The output is the North American Computer Braille Code (NABCC), the 8-dot code of refreshable
# braille displays, written as Unicode braille cells. Each line of the program becomes one line
# of cells, one cell per character.
import sys

# The 6-dot cells of the characters from space to underscore (Braille ASCII); dot k is bit k-1.
ASCII = [0, 46, 16, 60, 43, 41, 47, 4, 55, 62, 33, 44, 32, 36, 40, 12,
         52, 2, 6, 18, 50, 34, 22, 54, 38, 20, 49, 48, 35, 63, 28, 57,
         8, 1, 3, 9, 25, 17, 11, 27, 19, 10, 26, 5, 7, 13, 29, 21,
         15, 31, 23, 14, 30, 37, 39, 58, 45, 61, 53, 42, 51, 59, 24, 56]

def cell(c):
    n = ord(c)
    if n == 10:
        return c
    if n < 96:
        dots = ASCII[n - 32]
        if 64 <= n < 95:
            dots += 64  # dot 7: capital letters and @ [ ] ^ and the backslash
    else:
        dots = ASCII[n - 64]  # lower case: the cell of the character 32 below, without dot 7
    return chr(0x2800 + dots)

def braille(s):
    sys.stdout.buffer.write(''.join(map(cell, s)).encode())

