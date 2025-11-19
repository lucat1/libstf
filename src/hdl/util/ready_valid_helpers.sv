`timescale 1ns / 1ps

/**
 * The ReadyValidDuplicator creates NUM_INTERFACES outputs based on one input. The ready signal of 
 * the input is driven when all output ready signals are high.
 */
module ReadyValidDuplicator #(
    parameter integer NUM_INTERFACES
) (
    input logic clk,
    input logic rst_n,

    ready_valid_i.s in,                 // #(data_t)
    ready_valid_i.m out[NUM_INTERFACES] // #(data_t)
);

logic[NUM_INTERFACES - 1:0] out_ready;
logic[NUM_INTERFACES - 1:0] seen, n_seen;

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
    end else begin
        n_seen = seen | out_ready;
    end
end

for (genvar I = 0; I < NUM_INTERFACES; I++) begin
    assign out_ready[I] = out[I].ready;

    assign out[I].data  = in.data;
    assign out[I].valid = in.valid && !seen[I];
end

endmodule

/**
 * The ReadyValidCombiner combines the data of two inputs into one output.
 */
module ReadyValidCombiner (
    ready_valid_i.s left,  // #(left_t)
    ready_valid_i.s right, // #(right_t)
    ready_valid_i.m out    // #({left_t, right_t})
);

assign left.ready  = right.valid && out.ready;
assign right.ready = left.valid  && out.ready;

assign out.data  = {left.data, right.data};
assign out.valid = left.valid && right.valid;

endmodule
