`timescale 1ns / 1ps

/**
 * A stream profiler that starts counting when it sees the first valid data beat and only stops upon 
 * the stop signal. It counts the number of handshakes, starved cycles, stalled cycles, and idle 
 * pauses after a stream finishes with a last before the next stream arrives. After it received the 
 * stop signal, it holds its signals until the next valid data beat. The stop signal has to be 
 * asserted on the same clock cycle as the last handshake
 */
module StreamProfiler (
    input logic clk,
    input logic rst_n,

    input logic last,
    input logic valid,
    input logic ready,

    input logic stop,

    output data64_t handshakes_cycles,
    output data64_t starved_cycles,
    output data64_t stalled_cycles,
    output data64_t idle_cycles
);

typedef enum logic[1:0] {
    WAIT,   // Waiting for first handshake
    STREAM, // Counting cycles in a stream
    IDLE    // Counting cycles between streams
} state_t;

state_t  state,          n_state;
data64_t handshakes_reg, n_handshakes_reg;
data64_t starved_reg,    n_starved_reg;
data64_t stalled_reg,    n_stalled_reg;
data64_t idle_reg,       n_idle_reg;

always_ff @(posedge clk) begin
    if (!rst_n) begin
        state <= WAIT;

        handshakes_reg <= '0;
        starved_reg    <= '0;
        stalled_reg    <= '0;
        idle_reg       <= '0;
    end else begin
        state <= n_state;

        handshakes_reg <= n_handshakes_reg;
        starved_reg    <= n_starved_reg;
        stalled_reg    <= n_stalled_reg;
        idle_reg       <= n_idle_reg;
    end
end

always_comb begin
    n_state = state;

    n_handshakes_reg = handshakes_reg;
    n_starved_reg    = starved_reg;
    n_stalled_reg    = stalled_reg;
    n_idle_reg       = idle_reg;

    case (state)
        WAIT: begin
            if (valid) begin
                n_state       = STREAM;
                n_starved_reg = '0;

                if (ready) begin
                    n_handshakes_reg = 1;
                    n_stalled_reg    = '0;

                    if (last) begin
                        if (stop) begin
                            n_state = WAIT;
                        end else begin
                            n_state = STREAM;
                        end
                    end
                end else begin
                    n_handshakes_reg = '0;
                    n_stalled_reg    = 1;
                end
            end
        end
        STREAM: begin
            if (valid) begin
                if (ready) begin
                    n_handshakes_reg = handshakes_reg + 1;

                    if (last) begin
                        if (stop) begin
                            n_state = WAIT;
                        end else begin
                            n_state = IDLE;
                        end
                    end
                end else begin
                    n_stalled_reg = stalled_reg + 1;
                end
            end else begin
                n_starved_reg = starved_reg + 1;
            end
        end
        IDLE: begin
            if (valid) begin
                n_state = STREAM;

                if (ready) begin
                    n_handshakes_reg = handshakes_reg + 1;

                    if (last) begin
                        if (stop) begin
                            n_state = WAIT;
                        end else begin
                            n_state = IDLE;
                        end
                    end
                end else begin
                    n_stalled_reg = stalled_reg + 1;
                end
            end else begin
                n_idle_reg = idle_reg + 1;
            end
        end
    endcase
end

assign handshakes_cycles = handshakes_reg;
assign starved_cycles    = starved_reg;
assign stalled_cycles    = stalled_reg;
assign idle_cycles       = idle_reg;

endmodule
