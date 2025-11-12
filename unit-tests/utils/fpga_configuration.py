from coyote_test import constants, fpga_register
from typing import List
from unit_test.fpga_stream import StreamType
from utils.common import INTERRUPT_TRANSFER_SIZE_BITS


# Most general configuration class
# Configures which stream is valid and the stream types
# -> Is extended by configurations for specific operators like filter or projection
class StreamConfig:
    def __init__(self, offset: int, stream_id: int, select: int, type: StreamType):
        """
        Creates a new configuration, which tells the FPGA to use the memory region starting from 
        vaddr and over size bytes to send the output of stream with id stream_id. Offset is the 
        start of the memory configuration registers. 
        """
        self.offset = offset
        self.stream_id = stream_id
        self.select = select
        self.type = type

    def to_register_configuration(self) -> List[fpga_register.vFPGARegister]:
        # Determine the id of the register
        select_reg_id = self.offset + 2 * self.stream_id
        type_reg_id  = self.offset + 2 * self.stream_id + 1

        return [
            fpga_register.vFPGARegister(
                select_reg_id,
                bytearray(self.select.to_bytes(4, constants.BYTE_ORDER)),
            ),
            fpga_register.vFPGARegister(
                type_reg_id,
                bytearray(self.type.value.to_bytes(4, constants.BYTE_ORDER)),
            ),
        ]


class MemConfig:
    def __init__(self, offset: int, stream_id: int, vaddr: int, size: int):
        """
        Creates a new configuration, which tells the FPGA to use the memory region starting from 
        vaddr and over size bytes to send the output of stream with id stream_id. Offset is the 
        start of the memory configuration registers. 
        """
        self.offset = offset
        self.stream_id = stream_id
        self.vaddr = vaddr
        self.size = size

    def _to_bytearray(self, size: int, value: int) -> bytearray:
        """
        Ensures the value fits into size bits.
        Then, the id is prepended. Finally, the whole value
        will be converted to a bytearray with 8 bytes.
        """
        assert value <= pow(2, size) - 1, (
            f"Value {value} was out of range for the target of {size} bits"
        )
        return bytearray(value.to_bytes(8, constants.BYTE_ORDER))

    def to_register_configuration(self) -> List[fpga_register.vFPGARegister]:
        # Determine the id of the register
        vaddr_reg_id = self.offset + 2 * self.stream_id
        size_reg_id  = self.offset + 2 * self.stream_id + 1

        return [
            fpga_register.vFPGARegister(
                vaddr_reg_id,
                self._to_bytearray(constants.VADDR_BITS, self.vaddr),
            ),
            fpga_register.vFPGARegister(
                size_reg_id,
                self._to_bytearray(INTERRUPT_TRANSFER_SIZE_BITS, self.size),
            ),
        ]
