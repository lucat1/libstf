`timescale 1ns / 1ps

import libstf::data32_t;

/* -- Tie-off unused interfaces and signals ----------------------------- */
always_comb axi_ctrl.tie_off_s();
always_comb notify.tie_off_m();

/* -- INPUT ------------------------------------------------------------- */

AXI4S #(.AXI4S_DATA_BITS(512)) host_in (.aclk(aclk));
assign axis_host_recv[0].tready = host_in.tready;
assign host_in.tdata = axis_host_recv[0].tdata;
assign host_in.tkeep = axis_host_recv[0].tkeep;
assign host_in.tlast = axis_host_recv[0].tlast;
assign host_in.tvalid = axis_host_recv[0].tvalid;

ndata_i #(data32_t, 32) inner_in_values (), in_values ();
AXIToNData #(data32_t, 32) axi_to_ndata_inst (
    .clk(aclk),
    .rst_n(aresetn),

    .in(host_in),
    .out(inner_in_values)
);

typedef enum logic [1:0] {
  SEND_VALUES,
  SEND_IDS,
  WAIT_OUT
} state_t;
state_t state;

assign in_values.data = inner_in_values.data;
assign in_values.keep = inner_in_values.keep;
assign in_values.last = inner_in_values.last;
assign in_values.valid = inner_in_values.valid && state == SEND_VALUES;
assign inner_in_values.ready = in_values.ready && state == SEND_VALUES;

data32_t[15:0] test_ids_data[7:0];
assign test_ids_data = '{
    '{127,126,125,124,123,122,121,120,119,118,117,116,115,114,113,112},
    '{111,110,109,108,107,106,105,104,103,102,101,100,99,98,97,96},
    '{95,94,93,92,91,90,89,88,87,86,85,84,83,82,81,80},
    '{79,78,77,76,75,74,73,72,71,70,69,68,67,66,65,64},
    '{63,62,61,60,59,58,57,56,55,54,53,52,51,50,49,48},
    '{47,46,45,44,43,42,41,40,39,38,37,36,35,34,33,32},
    '{31,30,29,28,27,26,25,24,23,22,21,20,19,18,17,16},
    '{15,14,13,12,11,10,9,8,7,6,5,4,3,2,1,0}
};
logic[15:0] test_ids_keep[7:0];
assign test_ids_keep = '{
    16'hFFF0, 16'hFFFF, 16'hFFFF, 16'hFFFF, 
    16'hFFFF, 16'hFFFF, 16'hFFFF, 16'hFFFF
};
ndata_i #(data32_t, 16) inner_in_ids (), in_ids ();
NDataCyclicDriver #(data32_t, 16, 8) ndata_cyclic_driver_inst (
    .clk(aclk),
    .rst_n(aresetn),

    .data(test_ids_data),
    .keep(test_ids_keep),

    .out_data(inner_in_ids)
);

assign in_ids.data            = inner_in_ids.data;
assign in_ids.keep            = inner_in_ids.keep;
assign in_ids.last            = inner_in_ids.last;
assign in_ids.valid           = inner_in_ids.valid && state == SEND_IDS;
assign inner_in_ids.ready     = in_ids.ready && state == SEND_IDS;

/* -- OUTPUT ------------------------------------------------------------ */

integer output_databeat;
AXI4S #(.AXI4S_DATA_BITS(512)) host_out (.aclk(aclk));
assign host_out.tready = axis_host_send[0].tready;
assign axis_host_send[0].tdata = host_out.tdata;
assign axis_host_send[0].tkeep = host_out.tkeep;
assign axis_host_send[0].tlast = host_out.tlast;
assign axis_host_send[0].tvalid = host_out.tvalid;
assign axis_host_send[0].tid = output_databeat;

ndata_i #(data32_t, 16) out ();
NDataToAXI #(data32_t, 16) ndata_to_axi_inst (
    .clk(aclk),
    .rst_n(aresetn),

    .in(out),
    .out(host_out)
);

/* -- DESIGN WIRING ----------------------------------------------------- */

// Alternate between values and ids
always_ff @(posedge aclk) begin
    if(aresetn == 1'b0) begin 
        state <= SEND_VALUES;
    end else begin
        case (state)
            SEND_VALUES: begin
                if (in_values.ready && in_values.valid && in_values.last) begin
                    state <= SEND_IDS;
                end
            end

            SEND_IDS: begin
                if (in_ids.ready && in_ids.valid && in_ids.last) begin
                    state <= WAIT_OUT;
                end
            end

            WAIT_OUT: begin
                if (out.ready && out.valid && out.last) begin
                    state <= SEND_VALUES;
                end
            end
        endcase
    end
end


always_ff @(posedge aclk) begin
    if(aresetn == 1'b0) begin 
        output_databeat  <= 0;
    end else begin
        if (in_values.valid && in_values.ready) begin
            $display("< in valid: %x, ready: %x, last: %x", in_values.valid, in_values.ready, in_values.last);
        end

        if (in_ids.valid && in_ids.ready) begin
            $display("<<< in_ids valid: %x, ready: %x, last: %x", in_ids.valid, in_ids.ready, in_ids.last);
        end

        if (host_out.tvalid && host_out.tready) begin
            $display("> out valid: %x, ready: %x, last: %x", host_out.tvalid, host_out.tready, host_out.tlast);
            output_databeat <= output_databeat + 1;

            if (host_out.tlast) begin
              $display(">>! got tlast after %d databeats", output_databeat+1);
              output_databeat <= 0;
            end
        end
    end
end

Dictionary #(data32_t, data32_t, 16) dictionary_inst (
    .clk(aclk),
    .rst_n(aresetn),

    .in_values(in_values),
    .in_ids(in_ids),

    .out(out)
);
