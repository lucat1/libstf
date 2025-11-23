<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="img/libstf_dark.png">
    <img src="img/libstf_light.png" width=250>
  </picture>
</p>

[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)

# A Standard Library for Hardware Design

This library is a collection of common modules used to develop hardware designs. Some modules are 
specific to developing vFPGAs for Coyote. The main functionality libstf offers is:

- Interfaces that transport a specific number of elements, adapters to AXI4S interfaces, and other helpers (src/data_interfaces.sv and src/hdl/stream)
- Utilities for configuration registers accessed through an AXI4L interface (src/hdl/config)
- Crossbar (src/hdl/crossbar)
- Dictionary (src/hdl/dict)
- Stream normalization (src/hdl/normalization)
- vFPGA-specific stream output writer that generates memory requests and communicates with a memory manager on the CPU side (src/hdl/output)

This library is *work in progress*.

## Getting Started
Clone the repo and download the Coyote submodule:
```bash
git clone --recurse-submodules https://github.com/fpgasystems/libstf
```

The recommended way to get started with libstf is to start exploring the Python unit tests in the 
`unit-tests` folder. To execute the unit tests, you have to set up the Coyote simulation project 
with:

```bash
./sim_setup.sh
```

This creates the `build_hw` folder. Anytime you create or rename files in `src/hdl`, you have to 
execute this command again. Afterwards, the unit tests should show up in VSCode.

## Code Style
For now, we have a couple of code style rules:

- Camel case for class names and snake case for file names and everything else in the code
- _i postfix for interfaces
- _t postfix for types
- n_ prefix for next signals in state logic
- inst_ prefix for module instantiations
- *Width* always refers to width in bits and *size* to width in bytes

## TODOs
1. Get types and NUM_ELEMENTS from interface instead of parameters
2. Add interface assertions

## License
The libstf code is licensed under the terms in [LICENSE.md](https://github.com/fpgasystems/libstf/blob/master/LICENSE.md), which corresponds to the MIT Licence.
Any contributions to libstf will be accepted under the same terms of license.
