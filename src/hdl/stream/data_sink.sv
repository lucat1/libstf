`timescale 1ns / 1ps

`include "libstf_macros.svh"

/**
 * Can be configured to discard the input stream or forward it to the output. The ID parameter can 
 * be used to select the correct enable signal in case the enable configuration carries the signal 
 * for multiple DataSinks.
 */
module DataSink #(
    parameter integer ID,
    parameter integer ENABLE_SKID_BUFFER = 1
) (
    input logic clk,
    input logic rst_n,

    ready_valid_i.s enable, // #(logic[NUM_STREAMS - 1:0])

    ndata_i.s in, // #(data_t, NUM_ELEMENTS)
    ndata_i.m out // #(data_t, NUM_ELEMENTS)
);

localparam type    data_t       = in.data_t;
localparam integer NUM_ELEMENTS = in.NUM_ELEMENTS;

// If we don't pull this into an internal register we have to assign valid to ready which is bad
logic enable_reg; 
logic enable_reg_valid;

logic was_last_data_beat;

ndata_i #(data_t, NUM_ELEMENTS) internal();

always_ff @(posedge clk) begin
    if (rst_n == 1'b0) begin
        enable_reg_valid <= 1'b0;
    end else begin
        if (enable.valid) begin
            if (enable.ready) begin
                enable_reg       <= enable.data[ID];
                enable_reg_valid <= 1'b1;
            end
        end else begin
            enable_reg <= enable_reg;

            if (was_last_data_beat) begin
                enable_reg_valid <= '0;
            end else begin
                enable_reg_valid <= enable_reg_valid;
            end
        end
    end
end

assign was_last_data_beat = in.valid && in.last && in.ready;
assign enable.ready       = !enable_reg_valid || was_last_data_beat;

assign in.ready = enable_reg_valid && (internal.ready || enable_reg);

assign internal.data  = in.data;
assign internal.keep  = in.keep;
assign internal.last  = in.last;
assign internal.valid = in.valid && enable_reg_valid && !enable_reg;

generate if (ENABLE_SKID_BUFFER) begin
    NDataSkidBuffer #(data_t, NUM_ELEMENTS) inst_skid_buffer (.clk(clk), .rst_n(rst_n), .in(internal), .out(out));
end else begin
    `DATA_ASSIGN(internal, out)
end endgenerate

endmodule
