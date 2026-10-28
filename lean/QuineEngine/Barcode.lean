/-!
# Barcodes, abstractly

The barcode quines (QR, color QR, Aztec) are proved relative to an abstract codec: a capacity
and a decoder that inverts the encoder on texts within the capacity. The real encoders (in
JavaScript and PostScript) are trusted to implement such a codec and are tested against real
decoders.
-/

namespace QuineEngine.Barcode

structure Codec where
  C : Nat
  Grid : Type
  encode : List Char → Grid
  decode : Grid → Option (List Char)
  decode_encode : ∀ t, t.length ≤ C → decode (encode t) = some t

/-- Oversized texts get a formal representation that no file displays as. -/
def render (Q : Codec) (t : List Char) : Q.Grid ⊕ List Char :=
  if t.length ≤ Q.C then .inl (Q.encode t) else .inr t

def scan (Q : Codec) : Q.Grid ⊕ List Char → Option (List Char)
  | .inl g => Q.decode g
  | .inr t => some t

theorem scan_render (Q : Codec) (t : List Char) : scan Q (render Q t) = some t := by
  unfold render
  split
  · exact Q.decode_encode t ‹_›
  · rfl

end QuineEngine.Barcode
