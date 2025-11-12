<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="img/libstf_dark.png">
    <img src="img/libstf_light.png" width=400>
  </picture>
</p>

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

# a library of STandard components for FPGA hardware design (libSTF)

This library is a collection of common modules used to develop hardware designs. Some modules are 
specific to developing vFPGAs for Coyote. The main functionality it offers are:

1. Interfaces that transport a specific number of elements, adapters to AXI4S interfaces, and other helpers (src/data_interfaces.sv and src/hdl/stream)
2. Utilities for configuration registers accessed through an AXI4L interface (src/hdl/config)
3. Crossbar (src/hdl/crossbar)
4. Dictionary (src/hdl/dict)
5. Stream normalization (src/hdl/normalization)
6. vFPGA-specific stream output writer that generates memory requests and communicates with a memory manager on the CPU side (src/hdl/output)

 This library is *work in progress*. For now, we have a couple of code style rules:

1. Camel case for class names and snake case for file names and everything else in the code
2. _i postfix for interfaces
3. _t postfix for types
4. n_ prefix for next signals in state logic
5. inst_ prefix for module instantiations
6. *Width* always refers to width in bits and *size* to width in bytes

## TODOs
1. Documentation
2. Stream configuration that can take as many config values at once as we have outstanding requests (and tests for it)
3. Figure out a way to test 0-length streams
