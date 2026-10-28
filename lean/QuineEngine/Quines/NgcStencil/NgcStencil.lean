import QuineEngine.NgcScript
import QuineEngine.Quines.SvgText.SvgText

/-!
# A G-code program that laser-cuts a stencil of itself

The program is RS274NGC (LinuxCNC G-code). Run on a laser cutter, it cuts its own source out of a
sheet as stencil lettering: each character is a 5 × 7 glyph of the SvgText font, cut as one bar
per run of pixels in a row, so the strips between rows hold every letter together.

G-code has no strings, so the file is a data block, which stores the code in parameters, followed
by the code (`QuineEngine.NgcScript`). The library `ENC` is `stencil.ngc.inc`. The text shown is
read glyph by glyph with the font, which `SvgText` proves faithful, so the theorem has no
hypotheses. The library is trusted to cut the glyphs of the text it shows; `check.py` tests this
with a G-code simulator.
-/

namespace QuineEngine.NgcStencil

open QuineEngine.NgcScript

/-! ## The alphabet and the font -/

/-- The characters of the program; the code of `A[i]` is `i + 1`. -/
def A : List Char := "\n0123456789#=[].-+*/ABCDEFGHILMNOQSTUWXY".toList

theorem alphabet : Alphabet A := ⟨by decide +kernel, by decide +kernel⟩

/-- A character as the stencil shows it: a glyph of the SvgText font, or a line break. -/
def cell (c : Char) : Option Nat := if c = '\n' then none else some (SvgText.glyph c)

def uncell : Option Nat → Char
  | none => '\n'
  | some g => SvgText.decodeGlyph g

theorem uncell_cell : ∀ c ∈ A, uncell (cell c) = c := by decide +kernel

/-! ## The representation system -/

/-- The stencil: the glyphs and line breaks of a text. Texts outside the alphabet get a formal
representation that no file displays as. -/
def render (t : Text) : List (Option Nat) ⊕ Text :=
  if t.all (inA A) then .inl (t.map cell) else .inr t

def scan : List (Option Nat) ⊕ Text → Option Text
  | .inl l => some (l.map uncell)
  | .inr t => some t

theorem map_uncell_cell : ∀ t : Text, t.all (inA A) = true → (t.map cell).map uncell = t
  | [], _ => rfl
  | c :: t, h => by
    simp only [List.all_cons, Bool.and_eq_true, inA, decide_eq_true_eq] at h
    simp only [List.map_cons, uncell_cell c h.1, map_uncell_cell t h.2]

theorem scan_render (t : Text) : scan (render t) = some t := by
  unfold render
  split
  · exact congrArg some (map_uncell_cell t ‹_›)
  · rfl

/-- The library: everything before the final call. -/
def ENC : Text := (include_str "stencil.ngc.inc").toList

/-- A file cuts the stencil of the text that its mode shows. -/
def Disp (f : Text) (p : List (Option Nat) ⊕ Text) : Prop :=
  ∃ x c m, parseFile A f = some (x, c) ∧ parseCode ENC c = some m ∧
    (shown A m x).all (inA A) = true ∧ p = render (shown A m x)

def system : System Text (List (Option Nat) ⊕ Text) where
  disp := Disp
  scan := scan
  render := render
  scan_render := scan_render

/-! ## The quine -/

def quotation : Quotation system where
  Dom t := t.all (inA A) = true ∧ t.length ≤ MAXLEN
  q := quoteWith A ENC
  disp_q t ht := ⟨render t, ⟨t, ENC ++ TAIL0, 0, parseFile_dataBlock A alphabet ht.1 ht.2 _,
    parseCode_tail0 ENC, ht.1, rfl⟩, rfl⟩

def diagonal : Diagonal system quotation where
  sub := sub A
  a := tmplWith ENC
  Ok x := (sub A x x).all (inA A) = true ∧ (sub A x x).length ≤ MAXLEN
  spec := by
    intro x hx s ⟨p, hd, hs⟩
    obtain ⟨x', c', m, hf, hc, hok, hp⟩ := hd
    change parseFile A (quoteWith A ENC (sub A x x)) = _ at hf
    rw [quoteWith, parseFile_dataBlock A alphabet hx.1 hx.2] at hf
    cases hf
    rw [parseCode_tail0] at hc
    cases hc
    subst hp
    change scan (render (sub A x x)) = _ at hs
    rw [scan_render] at hs
    cases hs
    have hxa : x.all (inA A) = true := by
      have := hx.1
      simp only [sub, List.all_append, Bool.and_eq_true] at this
      exact this.2
    have hxl : x.length ≤ MAXLEN := by
      have := hx.2
      simp only [sub, List.length_append] at this
      omega
    exact ⟨render (sub A x x), ⟨x, tmplWith ENC, 1, parseFile_dataBlock A alphabet hxa hxl _,
      parseCode_tail1 ENC, hx.1, rfl⟩, scan_render _⟩

/-- The engine's output: a G-code program that cuts a stencil of itself. -/
def quine : Text := diagonal.quine

theorem quine_ok : quine.all (inA A) = true ∧ quine.length ≤ MAXLEN := by decide +kernel

/-- **The stencil quine.** -/
theorem quine_correct : system.IsQuine quine := diagonal.isQuine quine_ok quine_ok

end QuineEngine.NgcStencil
