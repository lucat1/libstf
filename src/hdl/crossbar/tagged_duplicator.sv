`timescale 1ns / 1ps

/**
 * The Duplicator creates NUM_STREAMS output streams based on one input stream. The ready signal of 
 * the input is driven when all output ready signals are high. The valid signals of the output 
 * streams are masked with their previous ready signal. The mask is reset when every output stream 
 * has acknowledged the element with a ready.
 */
module TaggedDuplicator #(
    parameter integer NUM_STREAMS
) (
    input logic clk,
    input logic rst_n,

    tagged_i.s in,              // #(data_t, TAG_WIDTH)
    tagged_i.m out[NUM_STREAMS] // #(data_t, TAG_WIDTH)
);

logic[NUM_STREAMS - 1:0] out_ready;
logic[NUM_STREAMS - 1:0] seen, n_seen;

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

for (genvar I = 0; I < NUM_STREAMS; I++) begin
    assign out_ready[I] = out[I].ready;

    assign out[I].data  = in.data;
    assign out[I].tag   = in.tag;
    assign out[I].keep  = in.keep;
    assign out[I].last  = in.last;
    assign out[I].valid = in.valid && !seen[I];
end

endmodule