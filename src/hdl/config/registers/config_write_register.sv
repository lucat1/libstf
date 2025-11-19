`timescale 1ns / 1ps

module ConfigWriteRegister #(
    parameter integer ADDR,
    parameter type    data_t
) (
    input logic clk,

    config_i.s    conf,
    output data_t data
);

always_ff @(posedge clk) begin
    if (conf.valid && conf.addr == ADDR) begin
        data <= data_t'(conf.data);
    end
end

endmodule
