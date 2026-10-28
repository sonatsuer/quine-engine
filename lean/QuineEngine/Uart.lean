/-!
# UART frames

The modem and Verilog quines send their text as asynchronous serial frames, 8N1: a start bit 0,
eight data bits least significant first, and a stop bit 1. A frame is a list of ten bits, and the
representation of a text is the frame of each character in turn. `uncell` reads a frame back, so
the retract is concrete and its proof is computed over the 128 ASCII characters.
-/

namespace QuineEngine.Uart

abbrev Text := List Char

/-- The characters that a frame carries: ASCII. -/
def ok (c : Char) : Bool := c.toNat < 128

/-- The 8N1 frame of a character: start bit, eight data bits least significant first, stop bit. -/
def cell (c : Char) : List Bool :=
  false :: ((List.range 8).map fun i => c.toNat / 2 ^ i % 2 = 1) ++ [true]

/-- Read a frame back: check its length and its start and stop bits, then sum the data bits. -/
def uncell (w : List Bool) : Option Char :=
  match w with
  | false :: rest =>
    if rest.length = 9 ∧ rest.getLast? = some true then
      some (Char.ofNat (((rest.take 8).zipIdx).foldl
        (fun n (b, i) => if b then n + 2 ^ i else n) 0))
    else none
  | _ => none

theorem uncell_cell (c : Char) (h : ok c = true) : uncell (cell c) = some c := by
  have key : ∀ k : Fin 128, uncell (cell (Char.ofNat k)) = some (Char.ofNat k) := by
    decide +kernel
  have hc : c.toNat < 128 := by simpa [ok] using h
  have := key ⟨c.toNat, hc⟩
  simpa [Char.ofNat_toNat] using this

/-- The frames of a text. Texts outside ASCII get a formal representation that no file displays
as. -/
def render (t : Text) : List (List Bool) ⊕ Text := if t.all ok then .inl (t.map cell) else .inr t

def uncells : List (List Bool) → Option Text
  | [] => some []
  | w :: ws => (uncell w).bind fun c => (uncells ws).map (c :: ·)

def scan : List (List Bool) ⊕ Text → Option Text
  | .inl ws => uncells ws
  | .inr t => some t

theorem uncells_cells : ∀ t : Text, t.all ok = true → uncells (t.map cell) = some t
  | [], _ => rfl
  | c :: t, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [List.map_cons, uncells, uncell_cell c h.1, Option.bind_some,
      uncells_cells t h.2, Option.map_some]

theorem scan_render (t : Text) : scan (render t) = some t := by
  unfold render
  split
  · exact uncells_cells t ‹_›
  · rfl

end QuineEngine.Uart
