`timescale 1ns / 1ps

import libstf::*;

`include "config_macros.svh"

module MemConfig #(
    parameter NUM_STREAMS
) (
    input logic clk,
    input logic rst_n,

    write_config_i.s write_config,
    read_config_i.s  read_config,

    mem_config_i.m out[NUM_STREAMS]
);

localparam NUM_WRITE_REGISTERS = 2;
localparam MAX_NUM_ENQUEUED_BUFFERS = 64;

ConfigReadRegister #(0, data8_t) inst_id_reg (clk, rst_n, read_config, data8_t'(MEM_CONFIG_ID));

for (genvar I = 0; I < NUM_STREAMS; I++) begin
    ready_valid_i #(vaddress_t)   vaddr();
    ready_valid_i #(alloc_size_t) size();
    ready_valid_i #(buffer_t)     buffer();

    ConfigWriteFIFO #(I * NUM_WRITE_REGISTERS + 0, MAX_NUM_ENQUEUED_BUFFERS, vaddress_t)   inst_vaddr_fifo (clk, rst_n, write_config, vaddr);
    ConfigWriteFIFO #(I * NUM_WRITE_REGISTERS + 1, MAX_NUM_ENQUEUED_BUFFERS, alloc_size_t) inst_size_fifo  (clk, rst_n, write_config, size);

    ReadyValidCombiner inst_combine (vaddr, size, buffer);

    `CONFIG_INTF_TO_SIGNALS(buffer, out[I].buffer)
end

endmodule
