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

// Note: WAIT_ALL breaks the stream semantics because it may produce dummy last elements in the output
localparam WAIT_ALL = 0;
localparam FORWARD = 1;

logic [$clog2(NUM_INPUTS) - 1:0] rr_priority; // TODO: Implement shift based on this

logic[NUM_INPUTS - 1:0] is_valid, tag_matches, prefix_sum, is_selected;
data_i #(data_t) selected();

data_t in_data[NUM_INPUTS];
logic[NUM_INPUTS - 1:0] in_keep, in_last, in_valid, in_ready;

logic[NUM_INPUTS - 1:0] last_seen, n_last_seen;

data_i #(data_t) skid(), n_skid();

// -- State ----------------------------------------------------------------------------------------
always_ff @(posedge clk) begin
    if (!rst_n) begin
        last_seen   <= '0;
        skid.valid  <= '0;
        rr_priority <= ID;
    end else begin
        last_seen <= n_last_seen;

        skid.data  <= n_skid.data;
        skid.keep  <= n_skid.keep;
        skid.last  <= n_skid.last;
        skid.valid <= n_skid.valid;

        rr_priority <= rr_priority + 1;
    end
end

// -- Selection signals ----------------------------------------------------------------------------
for(genvar I = 0; I < NUM_INPUTS; I++) begin
    assign in[I].ready = in_ready[I]; // We need to reassign these values to local arrays because SystemVerilog thinks the iterator in a process is not constant for arrays of interfaces

    assign in_data[I]  = in[I].data;
    assign in_keep[I]  = in[I].keep;
    assign in_last[I]  = in[I].last;
    assign in_valid[I] = in[I].valid;

    assign is_valid[I]    = in[I].valid && (!FILTER_KEEP || in[I].keep) && !last_seen[I];
    assign tag_matches[I] = is_valid[I] && in[I].tag == ID;
end

assign prefix_sum[0]  = tag_matches[0];
assign is_selected[0] = tag_matches[0];

for (genvar I = 1; I < NUM_INPUTS; I++) begin
    assign prefix_sum[I]  = tag_matches[I] ? 1'b1 : prefix_sum[I - 1];
    assign is_selected[I] = tag_matches[I] && !prefix_sum[I - 1];
end

// -- One-hot OR reduce multiplexer ----------------------------------------------------------------
always_comb begin
    selected.data = '0;
    selected.keep  = 1'b0;
    selected.last  = 1'b0;
    selected.valid = |is_selected; 

    for (int i = 0; i < NUM_INPUTS; i++) begin
        selected.data |= is_selected[i] ? in_data[i]  : '0;
        selected.keep |= is_selected[i] ? in_keep[i]  : 1'b0;
        selected.last |= LAST_HANDLING == FORWARD && is_selected[i] ? in_last[i] : 1'b0;
    end
end

// -- Comb logic -----------------------------------------------------------------------------------
always_comb begin
    // If we wait for all last signals, the inputs where we have seen the last belong to the next 
    // stream and cannot yet be consumed
    if (LAST_HANDLING == WAIT_ALL) begin
        in_ready = ~last_seen;
    end else begin
        in_ready = '1;
    end

    n_last_seen = last_seen;

    n_skid.data  = skid.data;
    n_skid.keep  = 1'b0;
    n_skid.last  = 1'b0;
    n_skid.valid = 1'b0; 

    if (skid.ready) begin
        n_skid.data  = selected.data;
        n_skid.keep  = selected.keep;
        n_skid.last  = selected.last;
        n_skid.valid = selected.valid; 

        for (int i = 0; i < NUM_INPUTS; i++) begin
            if (tag_matches[i] && !is_selected[i]) begin
                in_ready[i] = 1'b0; // Stall element
            end
            if (LAST_HANDLING == WAIT_ALL && in_last[i] && (is_selected[i] || (in_valid[i] && !tag_matches[i]))) begin
                n_last_seen[i] = 1'b1; // Mark last seen
            end
        end

        // We have seen all last signals or the last element is processed in this clock cycle
        if (LAST_HANDLING == WAIT_ALL && (&last_seen || ($onehot(tag_matches) && &(last_seen | in_last)))) begin 
            n_last_seen  = '0;
            n_skid.last   = 1'b1;
            n_skid.valid  = 1'b1;
        end
    end else begin // Not ready => Hold signals
        for (int i = 0; i < NUM_INPUTS; i++) begin
            if (tag_matches[i]) begin
                in_ready[i] = 1'b0;
            end else begin
                if (LAST_HANDLING == WAIT_ALL && in_valid[i] && in_last[i]) begin
                    n_last_seen[i] = 1'b1;
                end
            end
        end

        n_skid.keep  = skid.keep;
        n_skid.last  = skid.last;
        n_skid.valid = skid.valid;
    end 
end

DataSkidBuffer #(data_t) inst_skid_buffer (.clk(clk), .rst_n(rst_n), .in(skid), .out(out));

endmodule
