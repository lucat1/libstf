`timescale 1ns / 1ps

`include "libstf_macros.svh"

module DataEnumerator #(
    parameter type data_t,
    parameter NUM_ELEMENTS,
    parameter SERIAL_WIDTH
) (
    input logic clk,
    input logic rst_n,

    ndata_i.s   in, // #(data_t, NUM_ELEMENTS)
    ntagged_i.m out // #(data_t, NUM_ELEMENTS, SERIAL_WIDTH)
);

`RESET_RESYNC // Reset pipelining

localparam ELEMENT_BITS = $clog2(NUM_ELEMENTS);

typedef logic[SERIAL_WIDTH - 1:0] serial_t;

serial_t serial_count;

assign in.ready = out.ready;

always_ff @(posedge clk) begin
    if(!reset_synced) begin
        serial_count <= '0;     
    end else begin
        if (in.valid && in.ready) begin
            if (!in.last) begin
                serial_count <= serial_count + 1;
            end else begin
                serial_count <= '0;
            end
        end else begin
            serial_count <= serial_count;
        end
    end
end

for (genvar I = 0; I < NUM_ELEMENTS; I++) begin
    assign out.tag[I] = (serial_count << ELEMENT_BITS) + I;
end

assign out.data  = in.data;
assign out.keep  = in.keep;
assign out.last  = in.last;
assign out.valid = in.valid;

endmodule