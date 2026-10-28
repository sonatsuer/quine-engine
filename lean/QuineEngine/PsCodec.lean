import QuineEngine.Barcode
import QuineEngine.PsScript

/-!
# PostScript quines for a barcode

The engine instance shared by the PostScript barcode quines. A quine supplies its library text
`enc` and the four concrete facts in `Facts enc`, checked by computation. A file displays the
barcode of the string that `Q` receives, as given by an abstract `Codec`.
-/

namespace QuineEngine.PsCodec

open QuineEngine.Barcode QuineEngine.PsScript

/-- A file prints the barcode of the string that `Q` receives, when it has the expected shape. -/
def Disp (enc : Text) (Q : Codec) (f : Text) (p : Q.Grid ⊕ Text) : Prop :=
  ∃ s c ops v st, parseFile f = some (s, c) ∧ parseCodeWith enc c = some ops ∧
    runOps ops [s] = some (v :: st) ∧ v.length ≤ Q.C ∧ v.all (·.toNat < 256) = true ∧
    p = render Q v

def system (enc : Text) (Q : Codec) : System Text (Q.Grid ⊕ Text) where
  disp := Disp enc Q
  scan := scan Q
  render := render Q
  scan_render := scan_render Q

/-- The engine's output for the library `enc`. -/
def quineWith (enc : Text) : Text := sub (tmplWith enc) (tmplWith enc)

/-- The facts about the concrete code that the instance needs. -/
structure Facts (enc : Text) : Prop where
  safe_show : safe (showWith enc) = true
  parse_show : parseCodeWith enc (showWith enc) = some []
  safe_tmpl : safe (tmplWith enc) = true
  parse_tmpl : parseCodeWith enc (tmplWith enc) = some tmplOps

def quotation {enc : Text} (h : Facts enc) (Q : Codec) : Quotation (system enc Q) where
  Dom t := t.all (·.toNat < 256) = true ∧ t.length ≤ Q.C
  q := quoteWith enc
  disp_q t ht := ⟨render Q t, ⟨t, showWith enc, [], t, [],
    parseFile_quoteWith enc h.safe_show t ht.1, h.parse_show, rfl, ht.2, ht.1, rfl⟩, rfl⟩

def diagonal {enc : Text} (h : Facts enc) (Q : Codec) :
    Diagonal (system enc Q) (quotation h Q) where
  sub := sub
  a := tmplWith enc
  Ok x := safe x = true
  spec := by
    intro x hx s ⟨p, hd, hs⟩
    obtain ⟨s', c', ops, v, st, hf, hc, hr, hlen, h256, hp⟩ := hd
    change parseFile (quoteWith enc (sub x x)) = _ at hf
    rw [parseFile_quoteWith enc h.safe_show _ (all256_sub hx)] at hf
    cases hf
    rw [h.parse_show] at hc
    cases hc
    simp only [runOps, Option.some.injEq, List.cons.injEq] at hr
    obtain ⟨rfl, -⟩ := hr
    subst hp
    change scan Q (render Q (sub x x)) = _ at hs
    rw [scan_render] at hs
    cases hs
    exact ⟨render Q (sub x x), ⟨x, tmplWith enc, _, sub x x, [], parseFile_sub h.safe_tmpl hx,
      h.parse_tmpl, runOps_tmpl x, hlen, h256, rfl⟩, scan_render Q _⟩

/-- The quine theorem, for any codec whose capacity is at least the quine's length. -/
theorem quine_correct {enc : Text} (h : Facts enc) {C₀ : Nat}
    (hlen : (quineWith enc).length ≤ C₀) (h256 : (quineWith enc).all (·.toNat < 256) = true)
    (Q : Codec) (hC : C₀ ≤ Q.C) : (system enc Q).IsQuine (quineWith enc) :=
  (diagonal h Q).isQuine h.safe_tmpl ⟨h256, Nat.le_trans hlen hC⟩

end QuineEngine.PsCodec
