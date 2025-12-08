`timescale 1ns / 1ps

module Duplicate #(
    parameter type data_t, 
    parameter NUM_ELEMENTS,
    parameter MAX_IN_TRANSIT,
    parameter ENABLE_SKID_BUFFER = 1
) (
    input logic clk,
    input logic rst_n,

    valid_i.s mask,  // #(logic[NUM_ELEMENTS + NUM_ELEMENTS * $clog2(NUM_VALUES) - 1:0])

    ndata_i.s in,    // #(data_t, NUM_ELEMENTS)
    ndata_i.m out    // #(data_t, NUM_ELEMENTS)
);

typedef struct packed {
    logic duplicate;
    logic [$clog2(NUM_ELEMENTS)-1:0] origin;
} duplicate_t;

ready_valid_i #(duplicate_t[NUM_ELEMENTS - 1:0]) curr_mask();

ndata_i #(data_t, NUM_ELEMENTS) d (), q ();

FIFO #(
  .DEPTH(MAX_IN_TRANSIT),
  .WIDTH($bits(duplicate_t) * NUM_ELEMENTS)
) inst_mask_fifo (
  .i_clk(clk),
  .i_rst_n(rst_n),

  .i_data(mask.data),
  .i_valid(mask.valid),
  .i_ready(),

  .o_data(curr_mask.data),
  .o_valid(curr_mask.valid),
  .o_ready(curr_mask.ready),

  .o_filling_level()
);

assign curr_mask.ready = in.valid && q.ready;

assign in.ready = q.ready;

always_comb begin
  d.data  = q.data;
  d.valid = q.valid;
  d.keep = q.keep;
  d.last = q.last;

  if (in.valid && q.ready) begin
    d.data  = in.data;
    d.keep  = in.keep;
    d.valid = 1;
    d.last  = in.last;

    for (int unsigned i = 0; i < NUM_ELEMENTS; i++) begin
      if (curr_mask.data[i].duplicate) begin
        d.data[i] = in.data[curr_mask.data[i].origin];
        d.keep[i] = 1;
      end
    end
  end else if (q.ready) begin
    //Drain registers
    d.valid = 0;
    d.data  = 'x;
    d.keep  = 'x;
    d.last  = 0;
  end
end

always_ff @(posedge clk) begin
  if (~rst_n) begin
    q.data  <= 'x;
    q.keep <= 'x;
    q.valid <= 0;
    q.last <= 0;
  end else begin
    q.data  <= d.data;
    q.keep <= d.keep;
    q.valid <= d.valid;
    q.last <= d.last;
  end
end

generate if (ENABLE_SKID_BUFFER) begin
    NDataSkidBuffer #(data_t, NUM_ELEMENTS) inst_skid_buffer (.clk(clk), .rst_n(rst_n), .in(q), .out(out));
end else begin
    `DATA_ASSIGN(q, out)
end endgenerate

endmodule
