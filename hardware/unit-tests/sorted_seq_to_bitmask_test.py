from typing import List
import math

from coyote_test import fpga_test_case

from unit_test.fpga_stream import Stream, StreamType

class SortedSeqToBitmaskTest(fpga_test_case.FPGATestCase):
    alternative_vfpga_top_file = "vfpga_tops/sorted_seq_to_bitmask_test.sv"
    debug_mode = True
    verbose_logging = True

    def setUp(self):
        super().setUp()
        self.ids : List[int] = None

    def compute_expected_bitmask(self) -> List[bool]:
        # Get the number of bits the bitmask should have.
        # -> Next multiple of 8 that is >= max_id
        n_bits = math.ceil((self.ids[-1] + 1) / 8) * 8
        bitmask = [True if id in self.ids else False for id in range(0, n_bits)]
        return bitmask

    def simulate_fpga(self):
        assert self.ids is not None, "ids cannot be None"

        self.set_stream_input(0, Stream(StreamType.UNSIGNED_INT_32, self.ids))

        # Set the expected output
        self.set_expected_output(0, Stream(StreamType.ARROW_BOOL, self.compute_expected_bitmask()))

        return super().simulate_fpga()
    
    def test_with_continuous_ids(self):
        """
        Test behavior with continuous tuple ids, without gaps.
        Every 8 ids, one mask with all 1 should be created.
        """
        # Arrange
        self.ids = list(range(0, 400))
    
        # Act
        self.simulate_fpga()

        # Assert
        self.assert_simulation_output()

    def test_with_gaps_that_fit_into_one_mask(self):
        """
        Test behavior that tests indices that still fit into
        one mask (8-bit) but are irregular
        """
        # Arrange
        self.ids = [0, 2, 4, 7, 10, 11, 13, 15]
    
        # Act
        self.simulate_fpga()

        # Assert
        self.assert_simulation_output()

    def test_large_gaps_that_need_to_be_filled(self):
        """
        Tests tuple ids that have large gaps in between them.
        Those gaps need to be filled with masks that are all zero.
        """
        self.ids = list(range(0, 192, 24))
    
        # Act
        self.simulate_fpga()

        # Assert
        self.assert_simulation_output()

    def test_mask_with_non_full_data_beat(self):
        """
        Tests the behavior with masks that do not have 4 masks per data beat
        """
        self.ids = list(range(0, 37))
    
        # Act
        self.simulate_fpga()

        # Assert
        self.assert_simulation_output()
    
    def test_mixed_mask(self):
        """
        Test produces a mask that exhibits most of the properties
        discussed above. The first few data beats produce full
        masks. Then we have some larger gaps. Finally, the 
        input ends with a non-full data beat.
        """
        continuous = list(range(0, 33))
        gaps = list(range(33, 90, 17))
        end = [92, 97]
        self.ids = continuous + gaps + end
    
        # Act
        self.simulate_fpga()

        # Assert
        self.assert_simulation_output()
    

