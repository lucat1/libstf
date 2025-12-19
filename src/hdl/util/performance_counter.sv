`timescale 1ns / 1ps

module PerformanceCounter (
    input logic clk,
    input logic rst_n,

    input logic is_handshake,
    input logic is_last,

    output data64_t counter
);

typedef enum logic {
    IDLE,    // Waiting for first handshake
    COUNTING // Counting cycles between first and last handshake
} state_t;

state_t  state,       n_state;
data64_t counter_reg, n_counter_reg;

always_ff @(posedge clk) begin
    if (!rst_n) begin
        state       <= IDLE;
        counter_reg <= '0;
    end else begin
        state       <= n_state;
        counter_reg <= n_counter_reg;
    end
end

always_comb begin
    n_state       = state;
    n_counter_reg = counter_reg;

    case (state)
        IDLE: begin
            if (is_handshake) begin
                n_counter_reg = 1;

                if (!is_last) begin
                    n_state = COUNTING;
                end
            end
        end
        COUNTING: begin
            n_counter_reg = counter_reg + 1;
            
            if (is_handshake && is_last) begin
                n_state = IDLE;
            end
        end
    endcase
end

assign counter = counter_reg;

endmodule