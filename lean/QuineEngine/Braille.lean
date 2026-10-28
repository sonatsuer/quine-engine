/-!
# Braille ASCII

The table shared by the braille quines: the 6-dot cells of the 64 characters from space to
underscore, in the North American Braille ASCII code. Dot `k` is bit `k - 1`, as in the Unicode
braille block, where the cell with dots `m` is `U+2800 + m`.
-/

namespace QuineEngine.Braille

def ASCII : List Nat :=
  [0, 46, 16, 60, 43, 41, 47, 4, 55, 62, 33, 44, 32, 36, 40, 12,
   52, 2, 6, 18, 50, 34, 22, 54, 38, 20, 49, 48, 35, 63, 28, 57,
   8, 1, 3, 9, 25, 17, 11, 27, 19, 10, 26, 5, 7, 13, 29, 21,
   15, 31, 23, 14, 30, 37, 39, 58, 45, 61, 53, 42, 51, 59, 24, 56]

end QuineEngine.Braille
