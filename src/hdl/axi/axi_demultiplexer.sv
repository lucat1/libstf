`timescale 1ns / 1ps

module AXIDemultiplexer #(
    parameter NUM_STREAMS
) (
    input logic clk,
    input logic rst_n,

    ready_valid_i.s select, // #(logic[$clog2(NUM_STREAMS) - 1:0])

    AXI4S.s in,
    AXI4S.m out[NUM_STREAMS]
);

typedef logic[$clog2(NUM_STREAMS) - 1:0] select_t;

// If we don't pull this into an internal register we have to assign valid to ready which is bad
select_t select_reg; 
logic    select_reg_valid;

logic selected_stream_ready;
logic[NUM_STREAMS - 1:0] is_selected, stream_ready;
logic was_last_data_beat;

always_ff @(posedge clk) begin
    if (rst_n == 1'b0) begin
        select_reg_valid <= 1'b0;
    end else begin
        if (select.valid) begin
            if (select.ready) begin
                select_reg       <= select.data;
                select_reg_valid <= 1'b1;
            end
        end else begin
            select_reg <= select_reg;

            if (was_last_data_beat) begin
                select_reg_valid <= '0;
            end else begin
                select_reg_valid <= select_reg_valid;
            end
        end
    end
end

assign selected_stream_ready = select_reg_valid && |(is_selected & stream_ready);
assign was_last_data_beat    = in.tvalid && in.tlast && selected_stream_ready;
assign select.ready = !select_reg_valid || was_last_data_beat;

assign in.tready = selected_stream_ready;

for (genvar I = 0; I < NUM_STREAMS; I++) begin
    assign is_selected[I]  = I == select_reg;
    assign stream_ready[I] = out[I].tready;

    assign out[I].tdata  = in.tdata;
    assign out[I].tkeep  = in.tkeep;
    assign out[I].tlast  = in.tlast;
    assign out[I].tvalid = in.tvalid && select_reg_valid && is_selected[I];
end

endmodule
