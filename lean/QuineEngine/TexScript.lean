import QuineEngine.Barcode
import QuineEngine.GpScript

/-!
# pdfLaTeX files that typeset a barcode of their own source: the model

The LaTeX QR quine is a one-line `.tex` file of the fixed shape
```
PRE  x  |
```
`PRE` is fixed pdfLaTeX. It sets up the page and defines `\grab`, then sets every special character
to catcode 12 and starts `\grab`, which reads the bytes up to the delimiter `|` verbatim into `\v`.
`\grab`'s own body, tokenized when `PRE` defined it, restores the catcodes, runs `\v` with
`\scantokens` and ends the document.

The captured code `x` starts with `\iffalse PRE \fi`, a copy of the prefix that running the code
skips. Then come a fixed library `lib` (a QR encoder and a routine that typesets the matrix as a
field of mathematical symbols) and a short *template* (`epi`). The template rebuilds the whole file
from `\v`: the copy of `PRE` at offset 8, then `\v` itself, then `|`. It then typesets the file's
barcode.

The model is conservative, as for the gnuplot and PostScript quines:

* a file displays a barcode only when it has this shape and runs a code that the model knows;
* the known codes are two. The template, run on data `d`, outputs `slice d ++ d ++ "|"`, where
  `slice d` is the copy of `PRE` inside `d`. The *quotation* code outputs a fixed text that is
  encoded in it;
* every other file displays nothing.

The barcode is the abstract `Barcode.Codec`. The real `lib` is trusted to implement it, and
`check.mjs` tests it with pdfLaTeX, jsQR and ZXing.
-/

namespace QuineEngine.TexScript

open QuineEngine.Barcode
open QuineEngine.GpScript (octDigit octVal octVal_octDigit)

abbrev Text := List Char

/-- Printable ASCII. -/
def printable (c : Char) : Bool := 32 ≤ c.toNat && c.toNat < 127

/-- The quine-specific fixed byte strings: the prefix, the library, and the template. -/
structure Parts where
  pre : Text
  lib : Text
  epi : Text

variable (P : Parts)

/-! ## The template code -/

def ifFalse : Text := "\\iffalse".toList
def fiTok : Text := "\\fi".toList

/-- The captured code of the quine: a skipped copy of the prefix, the library, the template. -/
def tmplCode : Text := ifFalse ++ (P.pre ++ (fiTok ++ (P.lib ++ P.epi)))

/-- What the template reads back as the prefix: the bytes of `d` after `\iffalse`. -/
def slice (d : Text) : Text := (d.drop 8).take P.pre.length

theorem slice_tmplCode : slice P (tmplCode P) = P.pre := by
  unfold slice tmplCode
  rw [show ifFalse = "\\iffalse".toList from rfl]
  simp

/-! ## The quotation code: a text encoded in octal, marked by `Q`. -/

def quoteCode (t : Text) : Text := 'Q' :: GpScript.octs t

/-- Decode a run of `\ooo` octal escapes. -/
def unoct : Text → Option Text
  | [] => some []
  | '\\' :: a :: b :: d :: r =>
    match octVal a, octVal b, octVal d with
    | some x, some y, some z => (unoct r).map fun s => Char.ofNat (64 * x + 8 * y + z) :: s
    | _, _, _ => none
  | _ => none

def unquote : Text → Option Text
  | 'Q' :: r => unoct r
  | _ => none

theorem unoct_octs (t : Text) (ht : t.all printable = true) : unoct (GpScript.octs t) = some t := by
  induction t with
  | nil => rfl
  | cons c t ih =>
    simp only [List.all_cons, Bool.and_eq_true] at ht
    have hc := ht.1
    simp only [printable, Bool.and_eq_true, decide_eq_true_eq] at hc
    have h1 : c.toNat / 64 < 8 := by omega
    have h2 : c.toNat / 8 % 8 < 8 := Nat.mod_lt _ (by decide)
    have h3 : c.toNat % 8 < 8 := Nat.mod_lt _ (by decide)
    have hn : 64 * (c.toNat / 64) + 8 * (c.toNat / 8 % 8) + c.toNat % 8 = c.toNat := by omega
    simp only [GpScript.octs, unoct, octVal_octDigit _ h1, octVal_octDigit _ h2,
      octVal_octDigit _ h3, hn, ih ht.2, Option.map_some, Char.ofNat_toNat]

theorem unquote_quoteCode (t : Text) (ht : t.all printable = true) :
    unquote (quoteCode t) = some t := unoct_octs t ht

theorem quoteCode_ne_tmplCode (t : Text) : quoteCode t ≠ tmplCode P := by
  unfold quoteCode tmplCode
  rw [show ifFalse = "\\iffalse".toList from rfl]
  simp

/-! ## Files -/

open QuineEngine.PsScript (stripPrefix stripPrefix_append)
open QuineEngine.PyScript (readUntil readUntil_append)

/-- Parse a file into the captured data and the code that is run. -/
def parseFile (f : Text) : Option (Text × Text) :=
  match stripPrefix P.pre f with
  | some r =>
    match readUntil '|' r with
    | some (x, []) => some (x, x)
    | some (x, '@' :: rest) =>
      match readUntil '|' rest with
      | some (c, []) => some (x, c)
      | _ => none
    | _ => none
  | none => none

/-- Run a known code on the captured data. -/
def evalCode (code data : Text) : Option Text :=
  if code = tmplCode P then some (slice P data ++ (data ++ ['|'])) else unquote code

/-! ## The system -/

def Disp (Q : Codec) (f : Text) (p : Q.Grid ⊕ Text) : Prop :=
  ∃ data code out, parseFile P f = some (data, code) ∧ evalCode P code data = some out ∧
    out.length ≤ Q.C ∧ out.all printable = true ∧ p = render Q out

def system (Q : Codec) : System Text (Q.Grid ⊕ Text) where
  disp := Disp P Q
  scan := scan Q
  render := render Q
  scan_render := scan_render Q

/-! ## Substitution, quotation, template -/

/-- Data that can sit between the prefix and `|`: anything without the delimiter. -/
def safe (x : Text) : Bool := x.all (· ≠ '|')

/-- `sub c x` captures `x` and runs code `c`; if `c = x` it is the plain self-running file
`pre ++ x ++ "|"`. Otherwise `c` follows, as a second literal, which `\grab` never sees: it only
serves the model. -/
def sub (c x : Text) : Text :=
  P.pre ++ (x ++ ('|' :: (if c = x then [] else '@' :: (c ++ ['|']))))

/-- Facts about the fixed strings, discharged by the instance with `decide`. -/
structure Facts : Prop where
  tmpl_safe : safe (tmplCode P) = true
  pre_printable : P.pre.all printable = true

theorem parseFile_sub {c x : Text} (hx : safe x = true) (hc : safe c = true) :
    parseFile P (sub P c x) = some (x, c) := by
  have hxp : x.all (· ≠ '|') = true := hx
  unfold parseFile sub
  rw [stripPrefix_append]
  dsimp only
  rw [readUntil_append '|' _ x hxp]
  by_cases h : c = x
  · subst h
    simp
  · have hcp : c.all (· ≠ '|') = true := hc
    simp only [if_neg h, readUntil_append '|' _ c hcp]

/-- The template: `a`. -/
def tmpl : Text := tmplCode P

theorem evalCode_tmpl {data : Text} (h : slice P data = P.pre) :
    evalCode P (tmpl P) data = some (sub P data data) := by
  unfold evalCode tmpl sub
  rw [if_pos rfl, if_pos rfl, h]

/-- The quotation: a file that displays the text `t`. -/
def quoteWith (t : Text) : Text := sub P (quoteCode t) []

theorem evalCode_quote (t : Text) (ht : t.all printable = true) (data : Text) :
    evalCode P (quoteCode t) data = some t := by
  unfold evalCode
  rw [if_neg (quoteCode_ne_tmplCode P t), unquote_quoteCode t ht]

/-! ## The diagonal -/

/-- Admissible data for the template: no delimiter, printable, and its copy of the prefix. -/
def OkD (x : Text) : Prop := safe x = true ∧ x.all printable = true ∧ slice P x = P.pre

theorem printable_sub (F : Facts P) {x : Text} (hx : x.all printable = true) :
    (sub P x x).all printable = true := by
  unfold sub
  rw [if_pos rfl]
  simp only [List.all_append, List.all_cons, F.pre_printable, hx, List.all_nil,
    Bool.true_and, Bool.and_true]
  decide

theorem safe_octs {t : Text} (ht : t.all printable = true) :
    (GpScript.octs t).all (· ≠ '|') = true := by
  induction t with
  | nil => rfl
  | cons c t ih =>
    simp only [List.all_cons, Bool.and_eq_true] at ht
    have hc := ht.1
    simp only [printable, Bool.and_eq_true, decide_eq_true_eq] at hc
    have h1 : c.toNat / 64 < 8 := by omega
    have h2 : c.toNat / 8 % 8 < 8 := Nat.mod_lt _ (by decide)
    have h3 : c.toNat % 8 < 8 := Nat.mod_lt _ (by decide)
    have hpipe : GpScript.octVal '|' = none := by decide
    have hd : ∀ k, k < 8 → GpScript.octDigit k ≠ '|' := by
      intro k hk heq
      have hv := GpScript.octVal_octDigit k hk
      rw [heq, hpipe] at hv
      exact Option.noConfusion hv
    simp only [GpScript.octs, List.all_cons, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨by decide, hd _ h1, hd _ h2, hd _ h3, ih ht.2⟩

theorem safe_quoteCode {t : Text} (ht : t.all printable = true) : safe (quoteCode t) = true := by
  unfold safe quoteCode
  simp only [List.all_cons, safe_octs ht]
  decide

theorem parseFile_quoteWith {t : Text} (ht : t.all printable = true) :
    parseFile P (quoteWith P t) = some ([], quoteCode t) :=
  parseFile_sub P (by decide) (safe_quoteCode ht)

def quotation (Q : Codec) : Quotation (system P Q) where
  Dom t := t.all printable = true ∧ t.length ≤ Q.C
  q := quoteWith P
  disp_q t ht := ⟨render Q t, ⟨[], quoteCode t, t, parseFile_quoteWith P ht.1,
    evalCode_quote P t ht.1 [], ht.2, ht.1, rfl⟩, rfl⟩

def diagonal (F : Facts P) (Q : Codec) : Diagonal (system P Q) (quotation P Q) where
  sub := sub P
  a := tmpl P
  Ok := OkD P
  spec := by
    intro x hx s ⟨p, hd, hs⟩
    obtain ⟨d, c, out, hf, he, hlen, hpr, hp⟩ := hd
    change parseFile P (quoteWith P (sub P x x)) = _ at hf
    have hsubpr : (sub P x x).all printable = true := printable_sub P F hx.2.1
    rw [parseFile_quoteWith P hsubpr] at hf
    cases hf
    rw [evalCode_quote P (sub P x x) hsubpr] at he
    cases he
    subst hp
    change scan Q (render Q (sub P x x)) = _ at hs
    rw [scan_render] at hs
    cases hs
    exact ⟨render Q (sub P x x), ⟨x, tmpl P, sub P x x, parseFile_sub P hx.1 F.tmpl_safe,
      evalCode_tmpl P hx.2.2, hlen, hpr, rfl⟩, scan_render Q _⟩

/-- The engine's fixed point: the quine. -/
def quine : Text := sub P (tmpl P) (tmpl P)

theorem quine_correct (F : Facts P) (Q : Codec)
    (hpr : (quine P).all printable = true) (hlen : (quine P).length ≤ Q.C) :
    (system P Q).IsQuine (quine P) := by
  have htp : (tmpl P).all printable = true := by
    have hq := hpr
    rw [quine, sub, if_pos rfl] at hq
    simp only [List.all_append, Bool.and_eq_true] at hq
    exact hq.2.1
  exact (diagonal P F Q).isQuine ⟨F.tmpl_safe, htp, slice_tmplCode P⟩ ⟨hpr, hlen⟩

end QuineEngine.TexScript
