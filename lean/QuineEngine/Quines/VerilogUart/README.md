# A Verilog circuit that sends its own description on a serial pin

A Verilog file that describes a circuit. When simulated, the circuit drives its `tx` pin with
serial data, and the data is the file itself, in ASCII.

| File | Contents |
| --- | --- |
| `VerilogUart.lean` | the instance of the engine and the proof |
| `code-a.v.inc`, `code-b.v.inc` | the code, before and after its parameter `full` |
| `check.py` | simulates files with Icarus Verilog and decodes the pin |
| `quine.v` | the quine, written by `lake exe quine` |
| `quine.txt` | the frames that the Lean model predicts, written by `lake exe quine` |

## The format

**The serial line** is 9600 baud, 8N1, the framing of a PC serial port: a start bit 0, the eight
data bits least significant first, and a stop bit 1. The line is idle (1) for 20 bit times before
the first frame and after the last one.

## The file

`quine.v` is 3,521 bytes. It is a data + code file, like the OpenSCAD and G-code quines:

```
`define s "`timescale 1ns / 1ps\n\nmodule quine(input clk, output reg tx = 1, ...
`timescale 1ns / 1ps

module quine(input clk, output reg tx = 1, output reg done = 0);
  localparam s = `s, n = $bits(s) / 8, full = 1, lead = 20;
  ...
```

- **The data.** The first line defines the macro `s` as a string literal holding the code. The
  literal writes a line break as `\n`, and a quote and a backslash as `\"` and `\\`, so the code
  can be ordinary multi-line Verilog.
- **The circuit.** `quine` is a synthesizable module: one clock in, the pin `tx` out.
  - It reads the bytes of `s` from the parameter, and feeds them, one frame at a time, to a
    shift register on `tx`.
  - With `full = 1` it sends the whole file. First comes the `define` line: its header, then `s`
    escaped, with the escape bytes chosen by the circuit, then the closing quote and the line
    break. Then come the bytes of `s`, as they are.
  - It writes the backtick and the quote as numbers (`8'd96`, `8'd34`).
- **The simulation top** clocks the circuit at 9600 Hz, one bit a cycle. It dumps `tx` to
  `quine.vcd` and stops when the circuit raises `done`. It is fenced with `` `ifndef SYNTHESIS ``,
  so synthesis sees only the circuit.
- **No comments.** Icarus Verilog's preprocessor removes comments inside a `` `define ``, even
  inside a string literal: a `//` there cuts the literal short. So the code has no comments, and
  this README explains it instead.

**Running it.** With Icarus Verilog:

```sh
iverilog -g2012 quine.v && vvp a.out
```

This writes `quine.vcd`: about 4 s of simulated time, in about a second. To see the pin, open
the VCD in GTKWave, or decode it with sigrok (`check.py` shows how). On an FPGA, give the
circuit a 9600 Hz clock (or add a clock divider) and connect `tx` to a USB-serial adapter. A
terminal at 9600 baud then prints the file.

## The development

- **The file model** is `lean/QuineEngine/VlogScript.lean`.
  - **Files** have the shape `` `define s "x" ``, then a line break, then the code.
  - **Literals** escape the line break, the quote and the backslash, so any printable ASCII
    text, with line breaks, can be the data.
  - **The two recognised codes** differ only in `full`. The template (`full = 1`) sends
    `sub s s`, the whole file rebuilt from the data. The show code (`full = 0`) sends the data
    alone, and serves as the quotation.
- **The representation** is the sequence of UART frames, from `lean/QuineEngine/Uart.lean`,
  which it shares with the Python modem quine. The proof that the frames read back is computed
  over the 128 ASCII characters.
- **Result.** `quine_correct : system.IsQuine quine`. It has no hypotheses and depends only on
  `propext` and `Quot.sound`.

**What is trusted:**
1. Verilog simulators run files of the modelled shape as modelled;
2. the circuit sends the frames that `render` gives, with the timing above.

## Testing

Tested with Python 3.12.3, Icarus Verilog 12.0, and optionally sigrok-cli 0.7.2 and Yosys 0.33. From this folder:

```sh
python3 check.py
```

The script simulates each file and reads the `tx` pin from the VCD. It decodes the pin as
asynchronous serial: from each falling edge, it samples the ten bits at their centres.
- **The library.** Files with the show code send their data, for texts that include every
  printable character, the line break, the quote and the backslash.
- **The quine.** The frames of `quine.v` are those in `quine.txt`, as Lean predicts, and they
  decode to the source.
- **An independent decoder.** sigrok's UART decoder also decodes every pin, and its result must
  be the text. libsigrok's VCD reader stops at Icarus's `$comment` and `$dumpall` blocks, which
  carry no signal data, so the script removes them from a copy first.
- **Hardware.** Yosys synthesizes the circuit (`synth -top quine`). This is the slow step,
  about four minutes: the circuit reads `s` by a variable index, which becomes a 3,500-way
  multiplexer.
