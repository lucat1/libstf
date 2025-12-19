`timescale 1ns / 1ps

`include "libstf_macros.svh"
`include "config_macros.svh"

module StreamConfig #(
    parameter NUM_SELECT,
    parameter NUM_STREAMS
) (
    input logic clk,
    input logic rst_n,

    write_config_i.s write_config,
    read_config_i.s  read_config,

    stream_config_i.m out[NUM_STREAMS] // #(SELECT_WIDTH)
);

localparam SELECT_WIDTH = $clog2(NUM_SELECT);
localparam NUM_REGISTERS = 2;
localparam MAX_OUTSTANDING_STREAMS = 64;

typedef logic[SELECT_WIDTH - 1:0] select_t;

ConfigReadRegister #(0, data8_t) inst_id_reg (clk, rst_n, read_config, data8_t'(STREAM_CONFIG_ID));

for (genvar I = 0; I < NUM_STREAMS; I++) begin
    ready_valid_i #(select_t) select();
    ready_valid_i #(type_t)   data_type();
    stream_config_i #(SELECT_WIDTH) result();

    `CONFIG_WRITE_FIFO(I * NUM_REGISTERS + 0, MAX_OUTSTANDING_STREAMS, select_t, select)
    `CONFIG_WRITE_FIFO(I * NUM_REGISTERS + 1, MAX_OUTSTANDING_STREAMS, type_t, data_type)

    `CONFIG_INTF_TO_SIGNALS(select,    out[I].select)
    `CONFIG_INTF_TO_SIGNALS(data_type, out[I].data_type)
end

endmodule
