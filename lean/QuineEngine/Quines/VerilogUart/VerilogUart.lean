import QuineEngine.VlogScript

/-!
# A Verilog circuit that sends its own description on a serial pin

The file has the shape of `QuineEngine.VlogScript`: a `` `define s "…" `` line holding the code
as a string, then the code. The code is a synthesizable circuit `quine` and a simulation top.
- **The circuit.** It drives its `tx` pin with 9600-baud 8N1 serial. With `full = 1` it sends
  the whole file, rebuilt from `s`: the `define` line with `s` escaped, then `s` itself.
- **The simulation top.** It clocks the circuit at 9600 Hz (one bit a cycle), dumps `tx` to
  `quine.vcd`, and stops when the circuit is done.

The representation is the UART frames of `QuineEngine.Uart`, so the theorem has no hypotheses.
The circuit is trusted to send the frames of its text. `check.py` simulates it with Icarus
Verilog and decodes the pin.
-/

namespace QuineEngine.VerilogUart

open QuineEngine.VlogScript

/-- The code, around its parameter `full`. -/
def P : Parts where
  pre := (include_str "code-a.v.inc").toList
  post := (include_str "code-b.v.inc").toList

abbrev system := VlogScript.system P

/-- The engine's output: a Verilog file that sends itself on a serial pin. -/
def quine : Text := VlogScript.quine P

theorem quine_ok : quine.all ok = true := by decide +kernel

/-- **The Verilog quine.** -/
theorem quine_correct : system.IsQuine quine := VlogScript.quine_correct P quine_ok

end QuineEngine.VerilogUart
