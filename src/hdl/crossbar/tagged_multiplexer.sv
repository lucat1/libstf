`timescale 1ns / 1ps

/**
 * At the end of the stream, it waits to see all last signals before any elements of a new stream 
 * are accepted.
 */
module TaggedMultiplexer #(
    parameter type data_t,
    parameter ID,
    parameter NUM_INPUTS,
    parameter TAG_WIDTH,
    parameter LAST_HANDLING = 1, // 0: Wait until we see an element with a last signal for every input stream and produce a dummy last element; 1: Directly forward the incoming elements as they are
    parameter FILTER_KEEP = 1    // 0: Forward all elements even if the keep signal is 0, 1: Do not forward elements where keep is 0
) (
    input logic clk,
    input logic rst_n,

    tagged_i.s in[NUM_INPUTS], // #(data_t, TAG_WIDTH)
    data_i.m   out             // #(data_t)
);

`RESET_RESYNC // Reset pipelining

// Note: WAIT_ALL breaks the stream semantics because it may produce dummy last elements in the output
localparam WAIT_ALL = 0;
localparam FORWARD = 1;

// -- 1. stage: Extract matches to simplify multiplexing logic -------------------------------------
logic[NUM_INPUTS - 1:0] in_last, in_valid, in_ready;
logic[NUM_INPUTS - 1:0] last_seen_1, n_last_seen_1;
logic[NUM_INPUTS - 1:0] tag_matches;
tagged_i #(data_t, 1) filtered[NUM_INPUTS](), internal_1[NUM_INPUTS]();

always_ff @(posedge clk) begin
    if (!reset_synced) begin
        last_seen_1 <= '0;
    end else begin
        last_seen_1 <= n_last_seen_1;
    end
end

always_comb begin
    n_last_seen_1 = last_seen_1;

    if (LAST_HANDLING == WAIT_ALL) begin
        for (int i = 0; i < NUM_INPUTS; i++) begin
            if (in_valid[i] && in_last[i] && (!tag_matches[i] || in_ready[i])) begin
                n_last_seen_1[i] = 1'b1;
            end
        end
        // Note: We need the one hot expression here too because otherwise the first and second 
        // phase get out of sync
        if (&last_seen_1 || ($onehot(in_valid & tag_matches) && |(in_valid & tag_matches & in_ready) && 
                &(last_seen_1 | (in_valid & in_last)))) begin
            n_last_seen_1 = '0;
        end
    end
end

for (genvar I = 0; I < NUM_INPUTS; I++) begin
    assign in_last[I]  = in[I].last;
    assign in_valid[I] = in[I].valid;
    assign in_ready[I] = in[I].ready;

    assign tag_matches[I] = in[I].tag == ID;

    always_comb begin
        in[I].ready = 1'b1;

        filtered[I].data  = in[I].data;
        filtered[I].tag   = tag_matches[I];
        filtered[I].keep  = in[I].keep;
        filtered[I].last  = in[I].last;
        filtered[I].valid = last_seen_1[I] ? 1'b0 : in[I].valid;

        // If we wait for all last signals, the inputs where we have seen the last belong to the next 
        // stream and cannot yet be consumed
        if ((LAST_HANDLING == WAIT_ALL && last_seen_1[I]) || (tag_matches[I] && !filtered[I].ready)) begin
            in[I].ready = 1'b0;
        end
    end

    TaggedSkidBuffer #(data_t, 1) inst_internal_buffer (.clk(clk), .rst_n(reset_synced), .in(filtered[I]), .out(internal_1[I]));
end

// -- 2. stage: Multiplex round robin --------------------------------------------------------------
logic[NUM_INPUTS - 1:0] tags, is_selected;
data_i #(data_t) selected();

data_t internal_1_data[NUM_INPUTS];
logic[NUM_INPUTS - 1:0] internal_1_keep, internal_1_last, internal_1_valid, internal_1_ready;

logic[NUM_INPUTS - 1:0] last_seen_2, n_last_seen_2;

data_i #(data_t) internal_2(), n_internal_2();

for(genvar I = 0; I < NUM_INPUTS; I++) begin
    assign internal_1[I].ready = internal_1_ready[I]; // We need to reassign these values to local arrays because SystemVerilog thinks the iterator in a process is not constant for arrays of interfaces

    assign internal_1_data[I]  = internal_1[I].data;
    assign internal_1_keep[I]  = internal_1[I].keep;
    assign internal_1_last[I]  = internal_1[I].last;
    assign internal_1_valid[I] = internal_1[I].valid;

    assign tags[I] = internal_1[I].valid && (!FILTER_KEEP || internal_1[I].keep) && internal_1[I].tag;
end

// -- Selection logic ------------------------------------------------------------------------------
// High: Masked selection for the elements before the wrap around
logic[NUM_INPUTS - 1:0] high_mask, shifted_mask, masked_tags, prefix_sum_high, is_selected_high;

always_ff @(posedge clk) begin
    if (!reset_synced) begin
        high_mask <= '1;
    end else begin
        if (|shifted_mask) begin
            high_mask <= shifted_mask;
        end else begin
            high_mask <= '1;
        end
    end
end

assign shifted_mask = high_mask << 1;
assign masked_tags  = high_mask & tags;

assign prefix_sum_high[0]  = masked_tags[0];
assign is_selected_high[0] = masked_tags[0];

for (genvar I = 1; I < NUM_INPUTS; I++) begin
    assign prefix_sum_high[I]  = masked_tags[I] ? 1'b1 : prefix_sum_high[I - 1];
    assign is_selected_high[I] = masked_tags[I] && !prefix_sum_high[I - 1];
end

// Low: Non-masked selection for the elements after the wrap around
logic[NUM_INPUTS - 1:0] prefix_sum_low, is_selected_low;

assign prefix_sum_low[0]  = tags[0];
assign is_selected_low[0] = tags[0];

for (genvar I = 1; I < NUM_INPUTS; I++) begin
    assign prefix_sum_low[I]  = tags[I] ? 1'b1 : prefix_sum_low[I - 1];
    assign is_selected_low[I] = tags[I] && !prefix_sum_low[I - 1];
end

assign is_selected = |is_selected_high ? is_selected_high : is_selected_low;

// -- One-hot OR reduce multiplexer ----------------------------------------------------------------
always_comb begin
    selected.data  = '0;
    selected.keep  = 1'b0;
    selected.last  = 1'b0;
    selected.valid = |is_selected; 

    for (int i = 0; i < NUM_INPUTS; i++) begin
        selected.data |= is_selected[i] ? internal_1_data[i]  : '0;
        selected.keep |= is_selected[i] ? internal_1_keep[i]  : 1'b0;
        selected.last |= LAST_HANDLING == FORWARD && is_selected[i] ? internal_1_last[i] : 1'b0;
    end
end

// -- Output logic ---------------------------------------------------------------------------------
always_ff @(posedge clk) begin
    if (!reset_synced) begin
        last_seen_2      <= '0;
        internal_2.valid <= '0;
    end else begin
        last_seen_2 <= n_last_seen_2;

        internal_2.data  <= n_internal_2.data;
        internal_2.keep  <= n_internal_2.keep;
        internal_2.last  <= n_internal_2.last;
        internal_2.valid <= n_internal_2.valid;
    end
end

always_comb begin
    internal_1_ready = '1;

    n_last_seen_2 = last_seen_2;

    n_internal_2.data  = internal_2.data;
    n_internal_2.keep  = 1'b0;
    n_internal_2.last  = 1'b0;
    n_internal_2.valid = 1'b0; 

    if (internal_2.ready) begin
        n_internal_2.data  = selected.data;
        n_internal_2.keep  = selected.keep;
        n_internal_2.last  = selected.last;
        n_internal_2.valid = selected.valid; 

        for (int i = 0; i < NUM_INPUTS; i++) begin
            if (tags[i] && !is_selected[i]) begin
                internal_1_ready[i] = 1'b0; // Stall element
            end
            if (LAST_HANDLING == WAIT_ALL && internal_1_last[i] && (is_selected[i] || (internal_1_valid[i] && !tags[i]))) begin
                n_last_seen_2[i] = 1'b1; // Mark last seen
            end
        end

        // We have seen all last signals or the last element is processed in this clock cycle
        if (LAST_HANDLING == WAIT_ALL && (&last_seen_2 || ($onehot(tags) && &(last_seen_2 | internal_1_last)))) begin 
            n_last_seen_2      = '0;
            n_internal_2.last  = 1'b1;
            n_internal_2.valid = 1'b1;
        end
    end else begin // Not ready => Hold signals
        for (int i = 0; i < NUM_INPUTS; i++) begin
            if (tags[i]) begin
                internal_1_ready[i] = 1'b0;
            end else begin
                if (LAST_HANDLING == WAIT_ALL && internal_1_valid[i] && internal_1_last[i]) begin
                    n_last_seen_2[i] = 1'b1;
                end
            end
        end

        n_internal_2.keep  = internal_2.keep;
        n_internal_2.last  = internal_2.last;
        n_internal_2.valid = internal_2.valid;
    end 
end

DataSkidBuffer #(data_t) inst_output_buffer (.clk(clk), .rst_n(reset_synced), .in(internal_2), .out(out));

endmodule
