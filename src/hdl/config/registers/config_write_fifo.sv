`timescale 1ns / 1ps

module ConfigWriteFIFO #(
    parameter integer ADDR,
    parameter integer DEPTH,
    parameter type    data_t
) (
    input logic clk,
    input logic rst_n,

    config_i.s      conf,
    ready_valid_i.m data // #(data_t)
);

FIFO #(DEPTH, $bits(data_t)) inst_fifo (
    .i_clk(clk),
    .i_rst_n(rst_n),

    .i_data(data_t'(conf.data)),
    .i_valid(conf.valid),
    .i_ready(),

    .o_data(data.data),
    .o_valid(data.valid),
    .o_ready(data.ready),

    .o_filling_level()
);

endmodule
