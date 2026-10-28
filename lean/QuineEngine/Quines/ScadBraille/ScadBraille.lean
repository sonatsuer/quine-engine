import QuineEngine.Braille
import QuineEngine.ScadScript

/-!
# An OpenSCAD model of itself in braille

The file is an OpenSCAD model: braille plates, in tactile dimensions, that emboss the file's own
source in 6-dot Braille ASCII. Braille ASCII has 64 cells and no case, so the file is written in
64 characters: space to `@`, `[ \ ] ^ _`, and the lower-case letters. Letters are read as lower
case. A line break in the text is read from a blank row on the plates.

The file has the shape of `QuineEngine.ScadScript`, and its library `ENC` is `braille.scad.inc`,
which defines the module `braille`. The braille code is concrete: `cell` maps a character to its
cell and `uncell` reads it back, so the theorem has no hypotheses. The library is trusted to build
plates that read as `render` of its argument; `check.py` tests this with OpenSCAD and a Braille ASCII table copied from liblouis.
-/

namespace QuineEngine.ScadBraille

open QuineEngine.ScadScript QuineEngine.Braille

/-! ## 6-dot Braille ASCII -/

/-- The characters with a cell: newline, space to `@`, `[ \ ] ^ _`, and `a`–`z`. -/
def ok (c : Char) : Bool :=
  c = '\n' || (32 ≤ c.toNat && c.toNat ≤ 64) || (91 ≤ c.toNat && c.toNat ≤ 95) ||
    (97 ≤ c.toNat && c.toNat ≤ 122)

/-- The cell of a character; a lower-case letter takes the cell of its capital. -/
def dots (n : Nat) : Nat := if n < 96 then ASCII.getD (n - 32) 0 else ASCII.getD (n - 64) 0

def cell (c : Char) : Char := if c = '\n' then c else Char.ofNat (0x2800 + dots c.toNat)

def ALPHABET : List Char := ((List.range 128).map Char.ofNat).filter ok

def uncell (b : Char) : Option Char := ALPHABET.find? fun c => cell c = b

theorem uncell_cell (c : Char) (h : ok c = true) : uncell (cell c) = some c := by
  have key : ∀ n : Fin 128, ok (Char.ofNat n) = true →
      uncell (cell (Char.ofNat n)) = some (Char.ofNat n) := by decide +kernel
  have hc : c.toNat < 128 := by
    simp only [ok, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ((h | h) | h) | h
    · subst h
      decide
    · exact Nat.lt_of_le_of_lt h.2 (by decide)
    · exact Nat.lt_of_le_of_lt h.2 (by decide)
    · exact Nat.lt_of_le_of_lt h.2 (by decide)
  have := key ⟨c.toNat, hc⟩
  simp only [Char.ofNat_toNat] at this
  exact this h

theorem escOK_of_ok (c : Char) (h : ok c = true) : escOK c = true := by
  have key : ∀ n : Fin 128, ok (Char.ofNat n) = true → escOK (Char.ofNat n) = true := by
    decide +kernel
  have hc : c.toNat < 128 := by
    simp only [ok, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ((h | h) | h) | h
    · subst h
      decide
    · exact Nat.lt_of_le_of_lt h.2 (by decide)
    · exact Nat.lt_of_le_of_lt h.2 (by decide)
    · exact Nat.lt_of_le_of_lt h.2 (by decide)
  have := key ⟨c.toNat, hc⟩
  simp only [Char.ofNat_toNat] at this
  exact this h

/-! ## The representation system -/

/-- The reading of the plates, row by row, with line breaks kept. Texts outside the alphabet get a
formal representation that no file displays as. -/
def render (t : Text) : Text ⊕ Text := if t.all ok then .inl (t.map cell) else .inr t

def uncells : Text → Option Text
  | [] => some []
  | b :: s => (uncell b).bind fun c => (uncells s).map (c :: ·)

def scan : Text ⊕ Text → Option Text
  | .inl s => uncells s
  | .inr t => some t

theorem uncells_cells : ∀ t : Text, t.all ok = true → uncells (t.map cell) = some t
  | [], _ => rfl
  | c :: t, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp [uncells, uncell_cell c h.1, uncells_cells t h.2]

theorem scan_render (t : Text) : scan (render t) = some t := by
  unfold render
  split
  · exact uncells_cells t ‹_›
  · rfl

/-- The library: everything before the call `braille(…)`. -/
def ENC : Text := (include_str "braille.scad.inc").toList

def PRE : Text := ENC ++ "braille(".toList

/-- A file builds the braille plates of the string that `braille` receives. -/
def Disp (f : Text) (p : Text ⊕ Text) : Prop :=
  ∃ x c e, parseFile f = some (x, c) ∧ parseCodeWith PRE c = some e ∧
    (e.eval x).all ok = true ∧ p = render (e.eval x)

def system : System Text (Text ⊕ Text) where
  disp := Disp
  scan := scan
  render := render
  scan_render := scan_render

/-! ## The quine -/

theorem parse_show : parseCodeWith PRE (showWith PRE) = some [.var] := by decide +kernel
theorem safe_tmpl : safe (tmplWith PRE) = true := by decide +kernel
theorem parse_tmpl : parseCodeWith PRE (tmplWith PRE) = some tmplExpr := by decide +kernel

def quotation : Quotation system where
  Dom t := t.all ok = true
  q := quoteWith PRE
  disp_q t ht := by
    have hesc : t.all escOK = true := by
      simp only [List.all_eq_true] at ht ⊢
      exact fun c hc => escOK_of_ok c (ht c hc)
    refine ⟨render t, ⟨t, showWith PRE, [.var], parseFile_quoteWith PRE t hesc, parse_show, ?_,
      ?_⟩, rfl⟩
    · simpa [Expr.eval, Atom.eval] using ht
    · simp [Expr.eval, Atom.eval]

def diagonal : Diagonal system quotation where
  sub := sub
  a := tmplWith PRE
  Ok x := safe x = true
  spec := by
    intro x hx s ⟨p, hd, hs⟩
    obtain ⟨x', c', e, hf, hc, hok, hp⟩ := hd
    change parseFile (quoteWith PRE (sub x x)) = _ at hf
    rw [parseFile_quoteWith PRE _ (escOK_sub hx)] at hf
    cases hf
    rw [parse_show] at hc
    cases hc
    subst hp
    simp only [Expr.eval, Atom.eval, List.map_cons, List.map_nil, List.flatten_cons,
      List.flatten_nil, List.append_nil] at hok hs
    change scan (render (sub x x)) = _ at hs
    rw [scan_render] at hs
    cases hs
    refine ⟨render (sub x x), ⟨x, tmplWith PRE, tmplExpr, parseFile_sub hx, parse_tmpl, ?_, ?_⟩,
      scan_render _⟩
    · rw [eval_tmpl]
      exact hok
    · rw [eval_tmpl]

/-- The engine's output: an OpenSCAD model of itself in braille. -/
def quine : Text := diagonal.quine

theorem quine_ok : quine.all ok = true := by decide +kernel

/-- **The braille model quine.** -/
theorem quine_correct : system.IsQuine quine := diagonal.isQuine safe_tmpl quine_ok

end QuineEngine.ScadBraille
