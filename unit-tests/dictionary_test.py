from coyote_test import fpga_test_case, fpga_stream
from random import randint

_n = 128

class DictionaryB32TestCase(fpga_test_case.FPGATestCase):
    alternative_vfpga_top_file = "dictionary_test.sv"
    debug_mode = True
    # verbose_logging = True

    def test_one_b32(self):
        data = [randint(-_n, _n) for _ in range(_n-4)]
        self.set_stream_input(0, fpga_stream.Stream(fpga_stream.StreamType.SIGNED_INT_32, data))
        self.set_stream_input(0, fpga_stream.Stream(fpga_stream.StreamType.SIGNED_INT_32, data))
        self.set_expected_output(0, fpga_stream.Stream(fpga_stream.StreamType.SIGNED_INT_32, data))
        self.set_expected_output(0, fpga_stream.Stream(fpga_stream.StreamType.SIGNED_INT_32, data))

        # Act
        self.simulate_fpga()

        # Assert
        self.assert_simulation_output()
