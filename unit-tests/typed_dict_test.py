from enum import Enum
import random
from typing import List
from coyote_test import fpga_test_case, fpga_register
from unit_test.fpga_stream import get_bytes_for_stream_type, Stream, StreamType

class TypedDictExpression:
    def __init__(
        self,
        data_type: StreamType,
        values: List[list[object]],
        ids: List[List[int]],
    ):
        assert len(values) == len(ids)
        for v, i in zip(values, ids):
            assert len(i) > 0
            assert max(i) < len(v)

        self.data_type = data_type
        self.values = [Stream(data_type, vs) for vs in values]
        self.ids = ids
    
    def apply(self) -> List[Stream]:
        """
        Returns the result column
        """
        result = []
        for v, i in zip(self.values, self.ids):
            data = [v.stream_data()[id] for id in i]
            result.append(Stream(v.stream_type(), data))
        return result

    def get_type(self):
        return self.type
    
    def get_ids(self):
        result = []
        for i in self.ids:
            result.append(Stream(StreamType.UNSIGNED_INT_32, i))
        return result


class DictTest(fpga_test_case.FPGATestCase):
    """
    These tests test the typed dictionary.
    """

    debug_mode = True
    verbose_logging = True
    alternative_vfpga_top_file = "vfpga_tops/typed_dict_test.sv"

    # Method that gets executed once per test case
    def setUp(self):
        super().setUp()
        self.expression: TypedDictExpression = None

    def simulate_fpga(self):
        assert self.expression is not None, (
            "Cannot have dictionary test with empty dictionary expression!"
        )

        data_type = self.expression.data_type
        if data_type == StreamType.UNSIGNED_INT_8 or data_type == StreamType.SIGNED_INT_8:
            type_reg = 0
        elif data_type == StreamType.SIGNED_INT_32 or data_type == StreamType.UNSIGNED_INT_32:
            type_reg = 1
        elif data_type == StreamType.SIGNED_INT_64 or data_type == StreamType.UNSIGNED_INT_64:
            type_reg = 2
        elif data_type == StreamType.FLOAT_32:
            type_reg = 3
        elif data_type == StreamType.FLOAT_64:
            type_reg = 4
        else:
            raise TypeError(f"The provided StreamType cannot be cast to libstf's type_t: {repr(data_type)}")

        # Configuration
        self.write_register(fpga_register.vFPGARegister(1, bytearray([type_reg])))

        # Set the input data
        for values in self.expression.values:
            self.set_stream_input(0, values)
        for ids in self.expression.get_ids():
            self.set_stream_input(1, ids)

        # Set the expected output data
        for results in self.expression.apply():
            self.set_expected_output(0, results)

        return super().simulate_fpga()

    def test_sequential_32bit(self):
        values = list(range(0, 500))
        ids = [i for i in range(0, 500)]
        self.expression = TypedDictExpression(
            StreamType.UNSIGNED_INT_32,
            [values],
            [ids]
        )

        # Act
        self.simulate_fpga()

        # Assert
        self.assert_simulation_output()

    def test_random_32bit(self):
        values = list(range(0, 500))
        ids = [random.randint(0, 499) for _ in range(0, 1001)]
        self.expression = TypedDictExpression(
            StreamType.UNSIGNED_INT_32,
            [values],
            [ids]
        )

        # Act
        self.simulate_fpga()

        # Assert
        self.assert_simulation_output()

    def test_sequential_64bit(self):
        values = list(range(0, 500))
        ids = [i for i in range(0, 500)]
        self.expression = TypedDictExpression(
            StreamType.UNSIGNED_INT_64,
            [values],
            [ids]
        )

        # Act
        self.simulate_fpga()

        # Assert
        self.assert_simulation_output()

    def test_random_64bit(self):
        values = list(range(0, 500))
        ids = [random.randint(0, 499) for _ in range(0, 1001)]
        self.expression = TypedDictExpression(
            StreamType.UNSIGNED_INT_64,
            [values],
            [ids]
        )

        # Act
        self.simulate_fpga()

        # Assert
        self.assert_simulation_output()
    
    def test_sequential_32bit_twice(self):
        values_0 = list(range(0, 500))
        values_1 = list(range(1, 501))
        ids = [i for i in range(0, 500)]
        self.expression = TypedDictExpression(
            StreamType.UNSIGNED_INT_32,
            [values_0, values_1],
            [ids, ids]
        )

        # Act
        self.simulate_fpga()

        # Assert
        self.assert_simulation_output()
