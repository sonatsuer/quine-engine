import QuineEngine.Barcode
import QuineEngine.SvgScript

/-!
# SVG quines for a barcode

The engine instance shared by the SVG barcode quines. A quine supplies the prefix `pre` of its
evaluated code (its JavaScript library followed by `;drawX(`), and the four concrete facts in
`Facts pre`, checked by computation. A file displays the barcode of the value of `E`, as given by
an abstract `Codec`.
-/

namespace QuineEngine.SvgCodec

open QuineEngine.Barcode QuineEngine.SvgScript

/-- A file displays the barcode of the value of `E`, when it has the expected shape. -/
def Disp (pre : Text) (Q : Codec) (f : Text) (p : Q.Grid ⊕ Text) : Prop :=
  ∃ x c e, parseFile f = some (x, c) ∧ parseCodeWith pre c = some e ∧
    (e.eval x).length ≤ Q.C ∧ (e.eval x).all (·.toNat < 256) = true ∧ p = render Q (e.eval x)

def system (pre : Text) (Q : Codec) : System Text (Q.Grid ⊕ Text) where
  disp := Disp pre Q
  scan := scan Q
  render := render Q
  scan_render := scan_render Q

/-- The template `pre E)`, which draws the barcode of `sub v v`. -/
def tmplWith (pre : Text) : Text := codeWith pre tmplExpr

/-- The engine's output for the prefix `pre`. -/
def quineWith (pre : Text) : Text := sub (tmplWith pre) (tmplWith pre)

/-- The facts about the concrete code that the instance needs. -/
structure Facts (pre : Text) : Prop where
  safe_show : safe (showWith pre) = true
  parse_show : parseCodeWith pre (showWith pre) = some .var
  safe_tmpl : safe (tmplWith pre) = true
  parse_tmpl : parseCodeWith pre (tmplWith pre) = some tmplExpr

def quotation {pre : Text} (h : Facts pre) (Q : Codec) : Quotation (system pre Q) where
  Dom t := t.all (·.toNat < 256) = true ∧ t.length ≤ Q.C
  q := quoteWith pre
  disp_q t ht := ⟨render Q t, ⟨t, showWith pre, .var, parseFile_quoteWith pre h.safe_show t ht.1,
    h.parse_show, ht.2, ht.1, rfl⟩, rfl⟩

def diagonal {pre : Text} (h : Facts pre) (Q : Codec) :
    Diagonal (system pre Q) (quotation h Q) where
  sub := sub
  a := tmplWith pre
  Ok x := safe x = true
  spec := by
    intro x hx s ⟨p, hd, hs⟩
    obtain ⟨x', c', e', hf, hc, hlen, h256, hp⟩ := hd
    change parseFile (quoteWith pre (sub x x)) = _ at hf
    rw [parseFile_quoteWith pre h.safe_show _ (all256_sub hx)] at hf
    cases hf
    rw [h.parse_show] at hc
    cases hc
    simp only [Expr.eval] at hlen h256 hp
    subst hp
    change scan Q (render Q (sub x x)) = _ at hs
    rw [scan_render] at hs
    cases hs
    exact ⟨render Q (sub x x), ⟨x, tmplWith pre, tmplExpr, parseFile_sub h.safe_tmpl hx,
      h.parse_tmpl, by rw [eval_tmpl]; exact hlen, by rw [eval_tmpl]; exact h256,
      by rw [eval_tmpl]⟩, scan_render Q _⟩

/-- The quine theorem, for any codec whose capacity is at least the quine's length. -/
theorem quine_correct {pre : Text} (h : Facts pre) {C₀ : Nat} (hlen : (quineWith pre).length ≤ C₀)
    (h256 : (quineWith pre).all (·.toNat < 256) = true) (Q : Codec) (hC : C₀ ≤ Q.C) :
    (system pre Q).IsQuine (quineWith pre) :=
  (diagonal h Q).isQuine h.safe_tmpl ⟨h256, Nat.le_trans hlen hC⟩

end QuineEngine.SvgCodec
