import QuineEngine

open QuineEngine

/-- A picture as a plain PBM image (1 is black), `w` × `h` pixels, with `y` pointing up. -/
def pbm (pic : Nat → Nat → Bool) (w h : Nat) : String :=
  let rows := (List.range h).reverse.map fun Y =>
    String.mk ((List.range w).map fun X => if pic X Y then '1' else '0')
  s!"P1\n{w} {h}\n" ++ "\n".intercalate rows ++ "\n"

/-- Lean's own evaluation of the self-plotting formula, over the text block plus a margin. -/
def formulaPlot : String :=
  match SelfPlottingFormula.formulaPlot SelfPlottingFormula.quine with
  | some pic => pbm pic (4 * SelfPlottingFormula.W + 8) 18
  | none => ""

/-- A bitmap as a plain PBM image (1 is black), with `y` pointing down as in SVG. -/
def pbmDown (b : SvgText.Bitmap) : String :=
  let rows := (List.range b.h).map fun Y =>
    String.mk ((List.range b.w).map fun X => if b.px X Y then '1' else '0')
  s!"P1\n{b.w} {b.h}\n" ++ "\n".intercalate rows ++ "\n"

/-- The stencil that the G-code quine should cut, as a bitmap with one pixel per 0.6 mm: each line
of text is a row of 6 × 9 pixel cells, 80 rows to a column of 200 pixels. -/
def stencil (t : List Char) : SvgText.Bitmap :=
  let lines := (String.mk t).splitOn "\n" |>.map String.toList |>.toArray
  { w := 200 * ((lines.size + 79) / 80)
    h := 9 * 80
    px := fun X Y =>
      let line := X / 200 * 80 + Y / 9
      let col := X % 200 / 6
      decide (X % 200 % 6 < 5) && decide (Y % 9 < 7) &&
        match (lines[line]?).bind (·[col]?) with
        | some c => SvgText.gbit (SvgText.glyph c) (Y % 9) (X % 200 % 6)
        | none => false }

/-- The Morse code that the Morse quine should blink: the code of each character, separated by
spaces, with `/` for a space and a line break after each line-break code. -/
def morse (t : List Char) : String :=
  String.join (t.map fun c =>
    String.mk (if c = ' ' then ['/'] else PythonMorse.cell c) ++ if c = '\n' then "\n" else " ")

/-- Four lowercase hex digits. -/
def hex4 (n : Nat) : String :=
  String.mk ((List.range 4).reverse.map fun i => "0123456789abcdef".toList[n / 16 ^ i % 16]!)

/-- The frames that the modem quine should play: one line of ten bits per byte, start bit first. -/
def frames (t : List Char) : String :=
  String.join (t.map fun c => String.mk ((Uart.cell c).map (if · then '1' else '0')) ++ "\n")

/-- The files produced by the examples: each quine, saved in its own folder (paths relative to the
repository root), and the predictions that their checks compare with: the pictures of the formula
and text quines, the braille and Morse code of the braille and Morse quines, the frames of the
modem and Verilog quines, the segments of the stereogram quine, and the stencil of the G-code
quine. -/
def outputs : List (System.FilePath × String) :=
  [("lean/QuineEngine/Quines/Underload/underload.ul", String.mk Underload.quine),
   ("lean/QuineEngine/Quines/SvgQrCode/qr-code.svg", String.mk SvgQrCode.quine),
   ("lean/QuineEngine/Quines/PostScriptQrCode/qr-code.ps", String.mk PostScriptQrCode.quine),
   ("lean/QuineEngine/Quines/GnuplotQrCode/qr-code.gp", String.mk GnuplotQrCode.quine),
   ("lean/QuineEngine/Quines/LatexQrCode/qr-code.tex", String.mk LatexQrCode.quine),
   ("lean/QuineEngine/Quines/SvgColorQrCode/color-qr.svg", String.mk SvgColorQrCode.quine),
   ("lean/QuineEngine/Quines/PostScriptColorQrCode/color-qr.ps",
    String.mk PostScriptColorQrCode.quine),
   ("lean/QuineEngine/Quines/SvgAztec/aztec.svg", String.mk SvgAztec.quine),
   ("lean/QuineEngine/Quines/PostScriptAztec/aztec.ps", String.mk PostScriptAztec.quine),
   ("lean/QuineEngine/Quines/PythonBraille/braille.py", String.mk PythonBraille.quine),
   ("lean/QuineEngine/Quines/PythonBraille/braille.txt",
    String.mk (PythonBraille.quine.map PythonBraille.cell)),
   ("lean/QuineEngine/Quines/PythonMorse/morse.py", String.mk PythonMorse.quine),
   ("lean/QuineEngine/Quines/PythonMorse/morse.txt", morse PythonMorse.quine),
   ("lean/QuineEngine/Quines/PythonModem/modem.py", String.mk PythonModem.quine),
   ("lean/QuineEngine/Quines/PythonModem/modem.txt", frames PythonModem.quine),
   ("lean/QuineEngine/Quines/VerilogUart/quine.v", String.mk VerilogUart.quine),
   ("lean/QuineEngine/Quines/VerilogUart/quine.txt", frames VerilogUart.quine),
   ("lean/QuineEngine/Quines/PythonStereogram/stereogram.py", String.mk PythonStereogram.quine),
   ("lean/QuineEngine/Quines/PythonStereogram/stereogram.txt",
    String.join (PythonStereogram.quine.map fun c => hex4 (PythonStereogram.cell c) ++ "\n")),
   ("lean/QuineEngine/Quines/PythonSpectrogram/spectrogram.py", String.mk PythonSpectrogram.quine),
   ("lean/QuineEngine/Quines/ScadBraille/braille.scad", String.mk ScadBraille.quine),
   ("lean/QuineEngine/Quines/ScadBraille/braille.txt",
    String.mk (ScadBraille.quine.map ScadBraille.cell)),
   ("lean/QuineEngine/Quines/NgcStencil/stencil.ngc", String.mk NgcStencil.quine),
   ("lean/QuineEngine/Quines/NgcStencil/stencil.pbm", pbmDown (stencil NgcStencil.quine)),
   ("lean/QuineEngine/Quines/SvgText/text.svg", String.mk SvgText.quine),
   ("lean/QuineEngine/Quines/SvgText/expected.pbm", pbmDown (SvgText.typeset SvgText.quine)),
   ("lean/QuineEngine/Quines/SelfPlottingFormula/formula.txt",
    String.mk SelfPlottingFormula.quine),
   ("lean/QuineEngine/Quines/SelfPlottingFormula/plot.pbm", formulaPlot)]

/-- Write every output file. Quines hold exactly their characters, with no trailing newline.
Run from the repository root (`lake exe quine`). -/
def main : IO Unit := do
  for (file, contents) in outputs do
    IO.FS.writeFile file contents
    IO.println s!"wrote {file} ({contents.length} bytes)"
