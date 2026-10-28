/-!
# A quine engine

A fixed point theorem in the style of Kleene and Ershov, through a render/scan retract.

* `T` : texts (codes, files).
* `P` : representations (pictures, outputs, ...). No structure, nothing computable.
* `disp : T → P → Prop` : what a text displays as (a relation, so possibly partial or
  nondeterministic — it never has to be computed).
* `render : T → P`, `scan : P → Option T` with `scan ∘ render = some` : a retract.
  Scanning may identify many representations.

A *generalized quine* is a text `e` that displays as something which scans back to `e`.

The user supplies hypotheses as structures (each field is a definition or a lemma);
the engine *computes* the fixed point and *proves* it is a quine.
-/

namespace QuineEngine

/-! ## The abstract engine -/

structure System (T P : Type) where
  disp : T → P → Prop
  scan : P → Option T
  render : T → P
  scan_render : ∀ t, scan (render t) = some t

namespace System
variable {T P : Type} (S : System T P)

/-- `t` means `s`: it displays as something that scans to `s`. -/
def Means (t s : T) : Prop := ∃ p, S.disp t p ∧ S.scan p = some s

/-- `e` is a generalized quine. -/
def IsQuine (e : T) : Prop := S.Means e e
end System

variable {T P : Type} {S : System T P}

/-- Hypothesis (Q): rendering is internally definable on a domain `Dom`
(e.g. strings that fit a QR code, or well-formed literals). -/
structure Quotation (S : System T P) where
  Dom : T → Prop
  q : T → T
  disp_q : ∀ t, Dom t → ∃ p, S.disp (q t) p ∧ S.scan p = S.scan (S.render t)

theorem Quotation.means_q (Q : Quotation S) {t : T} (h : Q.Dom t) : S.Means (Q.q t) t := by
  obtain ⟨p, hp, hs⟩ := Q.disp_q t h
  exact ⟨p, hp, hs.trans (S.scan_render t)⟩

/-- Hypothesis (L): one template `a` whose instance at `x` behaves (at least) like the
quotation of the diagonal `sub x x`. -/
structure Diagonal (S : System T P) (Q : Quotation S) where
  sub : T → T → T
  a : T
  Ok : T → Prop
  spec : ∀ x, Ok x → ∀ s, S.Means (Q.q (sub x x)) s → S.Means (sub a x) s

/-- The fixed point. This is an ordinary computable value. -/
def Diagonal.quine {Q : Quotation S} (D : Diagonal S Q) : T := D.sub D.a D.a

/-- **Main theorem.** -/
theorem Diagonal.isQuine {Q : Quotation S} (D : Diagonal S Q)
    (hOk : D.Ok D.a) (hDom : Q.Dom D.quine) : S.IsQuine D.quine :=
  D.spec D.a hOk _ (Q.means_q hDom)

end QuineEngine
