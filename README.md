# Quine engine

A quine is a program that prints its own source code. This repository studies a generalization.
A program's output may be an object of another kind, such as a picture. It is compared with the
program after decoding: a *generalized quine* is a program whose output decodes back to the program
itself. For example, an SVG file that draws a QR code whose payload is the file itself is a
generalized quine.

Ordinary quines can be derived from Kleene's recursion theorem. Generalized quines come from a
fixed point theorem of the same kind, whose proof adapts the construction used to prove Ershov's
recursion theorem for precomplete numberings.

The repository contains a paper with the proof, `docs/quine-engine.tex`, and a Lean 4 formalization
of it. The formalization is a "quine engine": for a language that satisfies the theorem's
hypotheses, it computes a quine and proves it correct.

## The quines

Each quine has its own folder under `lean/QuineEngine/Quines/`, with the Lean module, a README
describing the development, and the file that `lake exe quine` writes.

- [`Underload/`](lean/QuineEngine/Quines/Underload/README.md): an ordinary quine,
  `(:aSS):aSS`, in the esoteric stack language Underload.
- [`SvgQrCode/`](lean/QuineEngine/Quines/SvgQrCode/README.md): an SVG file whose script draws
  a QR code whose payload is the file itself.
- [`SelfPlottingFormula/`](lean/QuineEngine/Quines/SelfPlottingFormula/README.md): an
  inequality in `x` and `y` whose solution set in ℕ² is a picture of the inequality.
- [`PostScriptQrCode/`](lean/QuineEngine/Quines/PostScriptQrCode/README.md): a PostScript file
  that prints a QR code whose payload is the file itself.
- [`GnuplotQrCode/`](lean/QuineEngine/Quines/GnuplotQrCode/README.md): a gnuplot script that plots
  a QR code of itself.
- [`LatexQrCode/`](lean/QuineEngine/Quines/LatexQrCode/README.md): a pdfLaTeX file whose PDF is a
  color QR code of itself, drawn as a field of Greek letters and operators.
- [`SvgText/`](lean/QuineEngine/Quines/SvgText/README.md): an SVG file whose script draws its
  own source text in a pixel font, read back by a scanner that is proved correct.
- [`SvgColorQrCode/`](lean/QuineEngine/Quines/SvgColorQrCode/README.md): an SVG file whose script
  draws a color QR code (three QR codes in the red, green and blue channels) of the file itself.
- [`PostScriptColorQrCode/`](lean/QuineEngine/Quines/PostScriptColorQrCode/README.md): a
  PostScript file that prints a color QR code of itself.
- [`SvgAztec/`](lean/QuineEngine/Quines/SvgAztec/README.md): an SVG file whose script draws an
  Aztec code of the file itself.
- [`PostScriptAztec/`](lean/QuineEngine/Quines/PostScriptAztec/README.md): a PostScript file that
  prints an Aztec code of itself, with its encoder stored compressed.
- [`PythonBraille/`](lean/QuineEngine/Quines/PythonBraille/README.md): a Python program that prints
  its own source in 8-dot computer braille (NABCC).
- [`PythonMorse/`](lean/QuineEngine/Quines/PythonMorse/README.md): a Python program that opens a
  window and blinks its own source in Morse code.
- [`PythonModem/`](lean/QuineEngine/Quines/PythonModem/README.md): a Python program that plays its
  own source as the sound of a 300-baud modem.
- [`PythonStereogram/`](lean/QuineEngine/Quines/PythonStereogram/README.md): a Python program that
  writes a PDF of autostereograms in which its own source is hidden, as raised characters.
- [`PythonSpectrogram/`](lean/QuineEngine/Quines/PythonSpectrogram/README.md): a Python program
  whose sound has a spectrogram that is a QR code of its own source.
- [`VerilogUart/`](lean/QuineEngine/Quines/VerilogUart/README.md): a Verilog circuit that, when
  simulated, sends its own description on a serial pin.
- [`ScadBraille/`](lean/QuineEngine/Quines/ScadBraille/README.md): an OpenSCAD file whose 3D model
  is a set of printable braille plates that emboss the file's own source.
- [`NgcStencil/`](lean/QuineEngine/Quines/NgcStencil/README.md): a LinuxCNC G-code program that
  laser-cuts its own source out of a sheet as stencil lettering.

## Layout

```
docs/quine-engine.tex                     the paper: the theorem, the Lean development, the quines
lean/QuineEngine/Engine.lean              the abstract engine: hypotheses and fixed point theorems
lean/QuineEngine/Barcode.lean             the abstract barcode codec shared by the barcode quines
lean/QuineEngine/SvgScript.lean           the model of SVG files with a script, shared by SVG quines
lean/QuineEngine/SvgCodec.lean            the engine instance shared by the SVG barcode quines
lean/QuineEngine/PsScript.lean            the model of the PostScript files, shared by those quines
lean/QuineEngine/PsCodec.lean             the engine instance shared by PostScript barcode quines
lean/QuineEngine/PyScript.lean            the model of Python files that execute a string literal
lean/QuineEngine/ScadScript.lean          the model of OpenSCAD files that rebuild their own text
lean/QuineEngine/NgcScript.lean           the model of G-code files that store their text as numbers
lean/QuineEngine/GpScript.lean            the model of gnuplot scripts that evaluate their code
lean/QuineEngine/TexScript.lean           the model of pdfLaTeX files that read their own text
lean/QuineEngine/VlogScript.lean          the model of Verilog files that send their own text
lean/QuineEngine/Braille.lean             the Braille ASCII table shared by the braille quines
lean/QuineEngine/Uart.lean                the UART frames shared by the modem and Verilog quines
lean/QuineEngine/Quines/                  one folder per quine: Lean module, README, output file
lean/QuineEngine.lean                     imports all modules
lean/Main.lean                            executable that writes each quine's files into its folder
lakefile.toml, lean-toolchain             Lake project files
```

## Building

### Lean

Install [elan](https://github.com/leanprover/elan). The toolchain (Lean 4.24.0) is pinned in
`lean-toolchain`, and elan fetches it on first use. No Mathlib is needed.

```sh
lake build        # check all proofs
lake exe quine    # write each computed quine into its folder
```

To work on the proofs in VS Code, open the repository root with the Lean 4 extension installed.

### Dependencies of the checks and the quines

Lean alone builds the proofs and writes the quines. Running a quine or its empirical check needs
more tools, and each quine's README lists what it needs. The table gathers them, with the versions
they were tested with (on Linux, x86-64). The package names are those of Debian and Ubuntu, as a
guide for other systems.

| Tool | Version | Debian/Ubuntu package | Used by |
| --- | --- | --- | --- |
| Node.js, npm | 18.19.1, 9.2.0 | `nodejs`, `npm` | the `check.mjs` scripts |
| npm packages | jsqr 1.4.0, @zxing/library 0.21.3, pngjs 7.0.0, @xmldom/xmldom 0.8.15 | none: `npm install` in the quine's folder, pinned in `package-lock.json` | the `check.mjs` scripts |
| Python | 3.12.3 | `python3`, `python3-venv` | the Python quines, the `check.py`, `gen_*.py` and `render.py` scripts |
| tkinter (Tk) | 8.6.14 | `python3-tk` | PythonMorse (running it) |
| pip packages | see `requirements.txt` | none: pip, below | PythonModem, PythonSpectrogram, the `render.py` scripts |
| Ghostscript | 10.02.1 | `ghostscript` | the PostScript quines |
| gnuplot | 6.0 patchlevel 0 | `gnuplot-nox` (or `gnuplot-qt`, for a window) | GnuplotQrCode |
| pdfTeX (TeX Live 2023) | 1.40.25 | `texlive-latex-base` | LatexQrCode |
| poppler (`pdftoppm`) | 24.02.0 | `poppler-utils` | LatexQrCode |
| latexmk | 4.83 | `latexmk` | the paper |
| OpenSCAD | 2021.01 | `openscad` | ScadBraille |
| Icarus Verilog | 12.0 | `iverilog` | VerilogUart |
| sigrok-cli | 0.7.2 | `sigrok-cli` | VerilogUart (optional) |
| Yosys | 0.33 | `yosys` | VerilogUart (optional) |
| sox | 14.4.2 | `sox` | PythonSpectrogram (optional) |
| minimodem | not tested | `minimodem` | PythonModem (optional) |

**The pip packages** go into a virtual environment, `.venv` at the repository root (git-ignored).
`requirements.txt` pins their versions: miniaudio 1.71 (with cffi 2.1.1 and pycparser 3.12),
numpy 2.5.4, Pillow 13.0.0 and zxing-cpp 3.1.1.

```sh
python3 -m venv .venv
.venv/bin/pip install -r requirements.txt
```

The scripts that need these packages run with `.venv/bin/python`. The other Python scripts need
only the standard library, and run with either Python.

### Paper

With a TeX distribution that provides `latexmk` and `pdflatex`:

```sh
cd docs
latexmk -pdf quine-engine.tex
```
