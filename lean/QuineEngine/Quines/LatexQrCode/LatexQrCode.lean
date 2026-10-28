import QuineEngine.Barcode
import QuineEngine.TexScript

/-!
# A pdfLaTeX file that typesets a color QR code of itself as a field of mathematics

The file has the shape of `QuineEngine.TexScript`:
```
PRE  x  |
```
`PRE` sets up the page and reads every byte up to `|` verbatim into `\v`. It then runs the
captured code `x` with `\scantokens`.
- The code starts with `\iffalse PRE \fi`, a copy of the prefix that the template reads back.
- Then comes the library `lib` (`library.inc`). It holds a QR encoder, and a routine that
  typesets a color QR code as a grid of colored cells, each carrying a Greek letter or operator.
- Last comes the template `epi`. It rebuilds the whole file, splits it into thirds, and encodes
  each third as a version-40 QR code in one RGB channel.

The color code is the abstract `Codec` of `QuineEngine.Barcode`. Its three channels are hidden
inside it, so its capacity is 3 × 2,953 = 8,859, the byte capacity of three version-40 symbols.
The library is trusted to implement such a codec, and `check.mjs` tests this with pdfLaTeX, jsQR
and ZXing.

The `decide +kernel` facts are split along the file's own `++` structure, with `List.all_append`
and `List.length_append`. Each piece is then small enough to reduce without exhausting the
kernel's stack.
-/

namespace QuineEngine.LatexQrCode

open QuineEngine.Barcode QuineEngine.TexScript

set_option maxRecDepth 100000

/-- The fixed byte strings of the file. -/
def P : Parts where
  pre := (include_str "pre.inc").toList
  lib := (include_str "library.inc").toList
  epi := (include_str "epilogue.inc").toList

theorem facts : Facts P where
  tmpl_safe := by
    simp only [tmplCode, safe, List.all_append]
    decide +kernel
  pre_printable := by decide +kernel

abbrev system (Q : Codec) := TexScript.system P Q

/-- The engine's output: a pdfLaTeX file that typesets a color QR code of itself. -/
def quine : Text := TexScript.quine P

theorem quine_length : quine.length ≤ 8859 := by
  show (TexScript.quine P).length ≤ 8859
  rw [TexScript.quine, sub, if_pos rfl]
  simp only [tmpl, tmplCode, List.length_append, List.length_cons]
  decide +kernel

theorem quine_printable : quine.all printable = true := by
  show (TexScript.quine P).all printable = true
  rw [TexScript.quine, sub, if_pos rfl]
  simp only [tmpl, tmplCode, List.all_append, List.all_cons]
  decide +kernel

theorem quine_correct (Q : Codec) (hC : 8859 ≤ Q.C) : (system Q).IsQuine quine :=
  TexScript.quine_correct P facts Q quine_printable (Nat.le_trans quine_length hC)

end QuineEngine.LatexQrCode
