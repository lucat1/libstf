`timescale 1ns / 1ps

module Deduplicate #(
    parameter type data_t, 
    parameter NUM_ELEMENTS
) (
    input logic clk,
    input logic rst_n,

    ndata_i.s in,    // #(data_t, NUM_ELEMENTS)

    valid_i.m mask,  // #(logic[NUM_ELEMENTS + NUM_ELEMENTS * $clog2(NUM_VALUES) - 1:0])
    ndata_i.m out    // #(data_t, NUM_ELEMENTS)
);

localparam int unsigned N_STAGES = 4;

//These boundaries were chosen to so that each deduplication stage performs roughly the same number of comparisons.
//In total, there are 16 choose 2 = 120 comparisons, so optimally, each stage would perform 120/N_STAGES comparisons.
//With these boundaries, the first stage performs:
//1 + 2 + 3 + 4 + 5 + 6 + 7 = 28 comparisons. Similarly for the remaining stages.
localparam int IDX_BOUNDARIES[N_STAGES+1] = '{1, 8, 11, 14, 16};

typedef struct packed {
    logic duplicate;
    logic [$clog2(NUM_ELEMENTS)-1:0] origin;
} duplicate_t;

ntagged_i #(data_t, $bits(duplicate_t), NUM_ELEMENTS) tmp[N_STAGES:0] ();

assign tmp[0].data = in.data;
assign tmp[0].valid = in.valid;
assign in.ready = tmp[0].ready;
assign tmp[0].keep = in.keep;
assign tmp[0].last = in.last;

duplicate_t[NUM_ELEMENTS - 1:0] first_stage_tag;
assign first_stage_tag = '{NUM_ELEMENTS{'{duplicate: 0, origin: 'x}}};
assign tmp[0].tag = first_stage_tag;

assign out.data = tmp[N_STAGES].data;
assign out.keep = tmp[N_STAGES].keep;
assign out.valid = tmp[N_STAGES].valid;
assign tmp[N_STAGES].ready = out.ready;
assign out.last = tmp[N_STAGES].last;

assign mask.data = tmp[N_STAGES].tag;
assign mask.valid = out.valid && out.ready;

generate
    for (genvar i = 1; i <= N_STAGES; i++) begin : gen_dedup_stages
        DeduplicateStage #(
            .ID(i - 1),
            .data_t(data_t),
            .NUM_ELEMENTS(NUM_ELEMENTS),
            .START_IDX_INCL(IDX_BOUNDARIES[i-1]),
            .END_IDX_EXCL(IDX_BOUNDARIES[i])
        ) inst_dedup_stage (
            .clk(clk),
            .rst_n(rst_n),
            .in(tmp[i-1]),
            .out(tmp[i])
        );
    end
endgenerate

endmodule
