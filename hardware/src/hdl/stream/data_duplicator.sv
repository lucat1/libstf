`timescale 1ns / 1ps

/**
 * The NDataDuplicator creates NUM_OUTPUTS output streams based on one input stream. The ready 
 * signal of the input is driven when all output ready signals are high.
 */
module NDataDuplicator #(
    parameter integer NUM_OUTPUTS
) (
    input logic clk,
    input logic rst_n,

    ndata_i.s in,              // #(data_t, NUM_ELEMENTS)
    ndata_i.m out[NUM_OUTPUTS] // #(data_t, NUM_ELEMENTS)
);

logic[NUM_OUTPUTS - 1:0] out_ready;
logic[NUM_OUTPUTS - 1:0] seen, n_seen;

assign in.ready = &(seen | out_ready);

always_ff @(posedge clk) begin
    if(!rst_n) begin
        seen <= '0;     
    end else begin
        seen <= n_seen;
    end
end

always_comb begin
    n_seen = seen;

    if (in.ready) begin
        n_seen = '0;
    end else if (in.valid) begin
        n_seen = seen | out_ready;
    end
end

for (genvar I = 0; I < NUM_OUTPUTS; I++) begin
    assign out_ready[I] = out[I].ready;

    assign out[I].data  = in.data;
    assign out[I].keep  = in.keep;
    assign out[I].last  = in.last;
    assign out[I].valid = in.valid && !seen[I];
end

endmodule
