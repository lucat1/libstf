`timescale 1ns / 1ps

import libstf::*;
import lynxTypes::*;

`include "axi_macros.svh"
`include "libstf_macros.svh"

/*
 * NOTE: out must be wired to axis_card_send[AXI_STRM_ID].
 */
module StreamCacheWriter #(
    parameter AXI_STRM_ID = 0,
    parameter TRANSFER_SIZE = TRANSFER_SIZE_BYTES,
    // TODO: figure out a good size for this
    parameter BUFFER_SIZE = MAXIMUM_HOST_ALLOCATION_SIZE_BYTES,
) (
    input logic clk,
    input logic rst_n,

    metaIntf.m sq_wr,
    metaIntf.s cq_wr,

    AXI4S.s          in,

    stream_cache_link.m link,
    AXI4S.m          out,
);

`RESET_RESYNC // Reset pipelining

// This stream is used on the host to allocate more data for the StreamWriter.
// On card memory, there's no need for allocations, new mem_config_i regions
// are provided when requested from the code below. Thus, we can just tie off
// this signal.
metaIntf #(.STYPE(irq_not_t)) notify (.aclk(clk), .aresetn(reset_synced));
always_comb notify.tie_off_m();

buffer_t next_buffer;
assign next_buffer.len = BUFFER_SIZE;

mem_config_i mem_config (.clk(clk), .rst_n(rst_n));
assign mem_config.flush_buffers = 1'b0;
assign mem_config.buffer_data   = next_buffer;
assign mem_config.buffer_valid  = 1'b1;

always_ff @(posedge clk) begin
    if (reset_synced == 1'b0) begin
        next_buffer.vaddr <= '0;
    end else begin
        if (mem_config.ready) begin
            next_buffer.vaddr <= next_buffer.vaddr + BUFFER_SIZE;
        end
    end
end

StreamWriter #(
    .STRM(STRM_CARD),
    .AXI_STRM_ID(AXI_STRM_ID),
    .TRANSFER_LENGTH_BYTES(TRANSFER_SIZE)
) inst_stream_writer (
    .clk(clk),
    .rst_n(reset_synced),

    .sq_wr(sq_wr),
    .cq_wr(cq_wr),
    .notify(notify),

    .mem_config(mem_config),

    .input_data(in),
    .output_data(out)
);

ready_valid_i #(data32_t) n_next_link (), next_link (), out_link ();

SkidBuffer #(data32_t) inst_skid_buffer (
    .clk(clk),
    .rst_n(reset_synced),

    .in(next_link),
    .out(out_link),
);

assign link.len_data  = out_link.data;
assign link.len_valid = out_link.valid;
assign out_link.ready = link.len_ready;

always_ff @(posedge clk) begin
    if (reset_synced == 1'b0) begin
      next_link.valid <= 0;
    end else begin
      next_link.data <= n_next_link.data;
      next_link.valid <= n_next_link.valid;
    end
end

logic is_completion;
// Lifted from the StreamWriter implementation. Should be kept in sync.
assign is_completion = cq_wr.valid && cq_wr.data.strm == STRM_CARD && cq_wr.data.dest == AXI_STRM_ID;

always_comb begin
    // If we received a completion on the cq_wr interface, TRANSFER_SIZE bytes
    // have been successfully written to the card. Thus, we can place a token
    // on the link to notify the reader.
    if (is_completion) begin
        // To avoid having to keep a potentially very big queue of equally
        // sized tokens, we instead update the next token and increase its
        // size incrementally. This way we only need to store at most two
        // tokens. The one currently served on the AXI stream (which cannot be
        // modified since it's valid) and the next one (which we can modify).
        if (next_link.ready) begin
            n_next_link.data = cq_wr.data.len;
        end else begin
            n_next_link.data = next_link.data + cq_wr.data.len;
        end
        n_next_link.valid = 1;
    end
end

endmodule
