`timescale 1ns / 1ps

module quine(input clk, output reg tx = 1, output reg done = 0);
  localparam s = `s, n = $bits(s) / 8, full = 