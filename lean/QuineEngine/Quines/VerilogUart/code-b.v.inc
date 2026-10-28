, lead = 20;
  localparam [87:0] head = {8'd96, "define s ", 8'd34};
  reg [1:0] part = full ? 0 : 3;
  reg second = 0, last = 0;
  reg [7:0] c, b;
  reg [9:0] frame;
  integer i = 0, bits = 0, idle = lead;
  always @(posedge clk)
    if (bits > 0) begin
      tx <= frame[0];
      frame <= frame >> 1;
      bits <= bits - 1;
    end else if (idle > 0 || last) begin
      tx <= 1;
      if (idle > 0) idle <= idle - 1;
      else if (last) done <= 1;
      if (last && idle == 0) idle <= lead;
    end else begin
      case (part)
        0: begin
          b = head[8 * (10 - i) +: 8];
          i = i + 1;
          if (i == 11) begin part = 1; i = 0; end
        end
        1: begin
          c = s[8 * (n - 1 - i) +: 8];
          if (!second && (c == 10 || c == 34 || c == 92)) begin b = 92; second = 1; end
          else begin
            b = second && c == 10 ? 110 : c;
            second = 0;
            i = i + 1;
            if (i == n) begin part = 2; i = 0; end
          end
        end
        2: begin
          b = i == 0 ? 34 : 10;
          i = i + 1;
          if (i == 2) begin part = 3; i = 0; end
        end
        3: begin
          b = s[8 * (n - 1 - i) +: 8];
          i = i + 1;
          if (i == n) last = 1;
        end
      endcase
      frame <= {1'b1, b, 1'b0};
      bits <= 10;
    end
endmodule

`ifndef SYNTHESIS
module top;
  reg clk = 0;
  wire tx, done;
  quine q(clk, tx, done);
  always #52083.333 clk = !clk;
  initial begin
    $dumpfile("quine.vcd");
    $dumpvars(0, tx);
  end
  always @(posedge done) $finish;
endmodule
`endif
