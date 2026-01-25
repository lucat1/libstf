`timescale 1ns / 1ps

/*
 * This interface links the StreamCacheWriter and StreamCacheWriter, acting as
 * a stream where tokens are shared. Each tokens represents the amount of
 * bytes written by the latest card write. This is used to pause reads until
 * data for a region has been fully written, so that partial data is never
 * read.
 */
interface stream_cache_link_i (
    input logic clk,
    input logic rst_n
);
    `READY_VALID_SIGNALS(buffer_size_t, len)

    task tie_off_m();
        len_valid  = 1'b0;
    endtask

    task tie_off_s();
        len_ready = 1'b1;
    endtask

    modport m (
        import tie_off_m,
        output len_data, len_valid,
        input len_ready
    );

    modport s (
        import tie_off_s,
        output len_ready,
        input len_data, len_valid
    );

`ifndef SYNTHESIS
    `STF_ASSERT_STABLE(len_data, len_valid, len_ready);
    `STF_ASSERT_NOT_UNDEFINED(len_valid);
    `STF_ASSERT_NOT_UNDEFINED(len_ready);
`endif
endinterface
