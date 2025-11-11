`timescale 1ns / 1ps

/**
 * ReadyValidCyclicDriver drives a ready valid signal forever with a constant
 * list of data values. Values are outputted in the provided order, from first
 * to last. When the last element is transmitted the driver resets and
 * restarts sending from the first element.
 */
module ReadyValidCyclicDriver #(
    parameter type data_t,
    parameter NUM_ELEMENTS
) (
    input logic clk,
    input logic rst_n,

    input data_t data[NUM_ELEMENTS - 1:0],

    ready_valid_i.m out_data // #(data_t)
);

reg [$clog2(NUM_ELEMENTS)-1:0] i;

// We always have data to put out, as we're cycling through the input values
assign out_data.valid = rst_n;
assign out_data.data = data[i];

always_ff @(posedge clk) begin
    if (rst_n == 1'b0) begin
        i <= 0;
    end else if (out_data.ready) begin
        i <= (i + 1) % NUM_ELEMENTS;
    end
end

endmodule

module NDataCyclicDriver #(
    parameter type data_t,
    parameter NUM_ELEMENTS,
    parameter NUM_DATABEATS
) (
    input logic clk,
    input logic rst_n,

    input data_t[NUM_ELEMENTS - 1:0] data[NUM_DATABEATS - 1:0],
    input logic[NUM_ELEMENTS - 1:0]  keep[NUM_DATABEATS - 1:0],

    ndata_i.m out_data // (data_t, NUM_ELEMENTS)
);

typedef struct packed {
    data_t[NUM_ELEMENTS - 1:0] data;
    logic[NUM_ELEMENTS - 1:0]  keep;
    logic last;
} input_t;

input_t in[NUM_DATABEATS - 1:0];

generate
for (genvar I = 0; I < NUM_DATABEATS; I++) begin
    assign in[I].data = data[I];
    assign in[I].keep = keep[I];
    assign in[I].last = I == NUM_DATABEATS - 1;
end
endgenerate

ready_valid_i #(input_t) inner ();

ReadyValidCyclicDriver #(input_t, NUM_DATABEATS) ready_valid_cyclic_driver_inst (
    .clk(clk),
    .rst_n(rst_n),

    .data(in),
    .out_data(inner)
);

assign inner.ready = out_data.ready;
assign out_data.valid = inner.valid;
assign out_data.data = inner.data.data;
assign out_data.keep = inner.data.keep;
assign out_data.last = inner.data.last;

endmodule
