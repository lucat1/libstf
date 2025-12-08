`timescale 1ns / 1ps

///This module fills parts of the duplicate bitmask and the duplicate origin vector, as specified
///with the START_IDX_INCL and END_IDX_EXCL parameters. All other indices remain untouched; remaining
///input port signals are just passed along.

///This module auto-resets itself after in.last, when eventually in.valid = 0 and out.ready = 1.
module DeduplicateStage  #(
    parameter int unsigned ID,
    parameter type data_t, 
    parameter NUM_ELEMENTS,
    parameter int unsigned START_IDX_INCL,
    parameter int unsigned END_IDX_EXCL
) (
    input logic clk,
    input logic rst_n,

    ntagged_i in,    // #(data_t, $bits(duplicate_t), NUM_ELEMENTS)
    ntagged_i out    // #(data_t, $bits(duplicate_t), NUM_ELEMENTS)
);

assign in.ready = out.ready;

typedef struct packed {
    logic duplicate;
    logic [$clog2(NUM_ELEMENTS)-1:0] origin;
} duplicate_t;

ndata_i #(data_t, NUM_ELEMENTS) d (), q ();
duplicate_t[NUM_ELEMENTS - 1:0] d_tag, q_tag;

assign out.data = q.data;
assign out.keep = q.keep;
assign out.valid = q.valid;
assign out.last = q.last;
assign out.tag = q_tag;

always_comb begin
    d.data = q.data;
    d.keep = q.keep;
    d.last = q.last;
    d.valid = q.valid;
    d_tag = q_tag;

    if (in.valid && out.ready) begin
        d.valid = 1;
        d.keep = in.keep;
        d.last = in.last;
        d.data = in.data;
        d_tag = in.tag;  // start with a clean duplicate bitmask

        for (int unsigned i = START_IDX_INCL; i < END_IDX_EXCL; i++) begin
            for (int unsigned j = 0; j < i; j++) begin
                // j is always less than i
                if (d.data[i] == d.data[j]) begin
                    d_tag[i].duplicate = d.keep[i];
                    d_tag[i].origin = j;
                    d.keep[i] = 0;

                    // Break inner loop, otherwise d_tag[i].origin might point to a
                    // location which is itself a duplicate
                    break;
                end
            end
        end
    end else if (out.ready) begin
        //Drain registers
        d.data = 'x;
        d.keep = 'x;
        d.valid = 0;
        d.last = 0;
        for (int unsigned i = 0; i < NUM_ELEMENTS; i++) begin
            d_tag[i] = '{duplicate: 0, origin: 'x};
        end
    end
end

always_ff @(posedge clk) begin
    if (~rst_n) begin
        q.data <= 'x;
        q.keep <= 'x;
        q.valid <= 0;
        q.last <= 0;
        q_tag <= '{NUM_ELEMENTS{'{duplicate: 0, origin: 'x}}};
    end else begin
        q.data <= d.data;
        q.keep <= d.keep;
        q.valid <= d.valid;
        q.last <= d.last;
        q_tag <= d_tag;
    end
end

assert property (@(posedge clk) disable iff (!rst_n) in.valid && !in.ready |=> $stable(in.valid))
else $fatal(1, "DeduplicationStage[%0d]: in.valid changed while in.ready is low", ID);

assert property (@(posedge clk) disable iff (!rst_n) in.valid && !in.ready |=> $stable(
    in.data
))
else $fatal(1, "DeduplicationStage[%0d]: in.data changed while in.ready is low", ID);

assert property (@(posedge clk) disable iff (!rst_n) in.valid && !in.ready |=> $stable(in.last))
else $fatal(1, "DeduplicationStage[%0d]: in.last changed while in.ready is low", ID);

initial begin
  assert (START_IDX_INCL < END_IDX_EXCL)
  else
    $fatal(
        1,
        "DeduplicationStage[%0d]: START_IDX %0d must be strictly less than END_IDX %0d",
        ID,
        START_IDX_INCL,
        END_IDX_EXCL
    );
end

endmodule
