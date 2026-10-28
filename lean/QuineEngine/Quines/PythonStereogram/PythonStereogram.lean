import QuineEngine.PyScript
import QuineEngine.Quines.SvgText.SvgText

/-!
# A Python program that hides itself in autostereograms

The program writes `stereogram.pdf`: a title page, then pages of random-dot autostereograms. Hidden
in them, as raised 16-segment characters, 3 rows of 8 to a page, is the program's own source. A
line break is a filled cell, and a space an empty one. 16-segment characters have no case, so the
program is written without capital letters; it writes the capitals that PDF needs with a helper.

The file has the shape of `QuineEngine.PyScript`, and its library `ENC` is `stereogram.py.inc`,
which defines `draw`. The 16-segment table is concrete: `font16.txt` gives each character's
segments, `cell` maps a character to them and `uncell` reads them back, so the theorem has no
hypotheses. The library is trusted to draw the segments of its argument, in this layout, as
autostereograms. `check.py` verifies every link of every page against the segments that Lean
predicts, and reads the segments back from the dots.
-/

namespace QuineEngine.PythonStereogram

open QuineEngine.PyScript
open QuineEngine.PsScript (hexVal)

/-! ## The 16-segment table -/

/-- Each line of `font16.txt` is a character code and its segments, both in hex. Segment `i` is
bit `i` of: a1 a2 b c d1 d2 e f g1 g2 i l ul ur ll lr. -/
def fontSrc : String := include_str "font16.txt"

def hexNum (s : Text) : Option Nat :=
  s.foldl (fun n d => n.bind fun n => (hexVal d).map (16 * n + ·)) (some 0)

def TABLE : List (Char × Nat) :=
  (SvgText.splitOn '\n' fontSrc.toList).filterMap fun line =>
    match SvgText.splitOn ' ' line with
    | [a, b] =>
      match hexNum a, hexNum b with
      | some x, some y => some (Char.ofNat x, y)
      | _, _ => none
    | _ => none

/-- The characters with a pattern. -/
def KEYS : Text := TABLE.map (·.1)

def ok (c : Char) : Bool := decide (c ∈ KEYS)

/-- The segments of a character. -/
def cell (c : Char) : Nat := ((TABLE.find? (·.1 = c)).map (·.2)).getD 0

def uncell (n : Nat) : Option Char := (TABLE.find? (·.2 = n)).map (·.1)

theorem uncell_cell : ∀ c ∈ KEYS, uncell (cell c) = some c := by decide +kernel

theorem lt128 : ∀ c ∈ KEYS, c.toNat < 128 := by decide +kernel

/-! ## The representation system -/

/-- The pages: the segments of each character in turn. Texts outside the alphabet get a formal
representation that no file displays as. -/
def render (t : Text) : List Nat ⊕ Text := if t.all ok then .inl (t.map cell) else .inr t

def uncells : List Nat → Option Text
  | [] => some []
  | n :: ns => (uncell n).bind fun c => (uncells ns).map (c :: ·)

def scan : List Nat ⊕ Text → Option Text
  | .inl ns => uncells ns
  | .inr t => some t

theorem uncells_cells : ∀ t : Text, t.all ok = true → uncells (t.map cell) = some t
  | [], _ => rfl
  | c :: t, h => by
    simp only [List.all_cons, Bool.and_eq_true, ok, decide_eq_true_eq] at h
    simp only [List.map_cons, uncells, uncell_cell c h.1, Option.bind_some,
      uncells_cells t (by simpa only [ok, List.all_eq_true, decide_eq_true_eq] using h.2),
      Option.map_some]

theorem scan_render (t : Text) : scan (render t) = some t := by
  unfold render
  split
  · exact uncells_cells t ‹_›
  · rfl

/-- The library: everything before the call `draw(…)`. -/
def ENC : Text := (include_str "stereogram.py.inc").toList

def PRE : Text := ENC ++ "draw(".toList

/-- A file draws the segments of the string that `draw` receives. -/
def Disp (f : Text) (p : List Nat ⊕ Text) : Prop :=
  ∃ x c e, parseFile f = some (x, c) ∧ parseCodeWith PRE c = some e ∧
    (e.eval x).all ok = true ∧ p = render (e.eval x)

def system : System Text (List Nat ⊕ Text) where
  disp := Disp
  scan := scan
  render := render
  scan_render := scan_render

/-! ## The quine -/

set_option maxRecDepth 100000

theorem safe_show : safe (showWith PRE) = true := by decide +kernel
theorem parse_show : parseCodeWith PRE (showWith PRE) = some .var := by decide +kernel
theorem safe_tmpl : safe (tmplWith PRE) = true := by decide +kernel
theorem parse_tmpl : parseCodeWith PRE (tmplWith PRE) = some tmplExpr := by decide +kernel

def quotation : Quotation system where
  Dom t := t.all ok = true
  q := quoteWith PRE
  disp_q t ht := by
    have h128 : t.all (·.toNat < 128) = true := by
      simp only [List.all_eq_true, ok, decide_eq_true_eq] at ht ⊢
      exact fun c hc => lt128 c (ht c hc)
    exact ⟨render t, ⟨t, showWith PRE, .var, parseFile_quoteWith PRE safe_show t h128,
      parse_show, ht, rfl⟩, rfl⟩

def diagonal : Diagonal system quotation where
  sub := sub
  a := tmplWith PRE
  Ok x := safe x = true
  spec := by
    intro x hx s ⟨p, hd, hs⟩
    obtain ⟨x', c', e, hf, hc, hok, hp⟩ := hd
    change parseFile (quoteWith PRE (sub x x)) = _ at hf
    rw [parseFile_quoteWith PRE safe_show _ (all128_sub hx)] at hf
    cases hf
    rw [parse_show] at hc
    cases hc
    subst hp
    change scan (render (sub x x)) = _ at hs
    rw [scan_render] at hs
    cases hs
    refine ⟨render (sub x x), ⟨x, tmplWith PRE, tmplExpr, parseFile_sub safe_tmpl hx, parse_tmpl,
      ?_, ?_⟩, scan_render _⟩
    · rw [eval_tmpl]
      exact hok
    · rw [eval_tmpl]

/-- The engine's output: a Python program that hides itself in autostereograms. -/
def quine : Text := diagonal.quine

theorem quine_ok : quine.all ok = true := by decide +kernel

/-- **The stereogram quine.** -/
theorem quine_correct : system.IsQuine quine := diagonal.isQuine safe_tmpl quine_ok

end QuineEngine.PythonStereogram
