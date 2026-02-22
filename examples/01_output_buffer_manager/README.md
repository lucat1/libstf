# LibSTF Example 1: Output Buffer Manager
Example how to use the OutputBufferManager of the library software library that manages output memory buffers together with an OutputWriter on the hardware side.

## Hardware synthesis
You need to copy the content of `hardware/unit-tests/vfpga_tops/output_writer_test.sv` to `hardware/src/vfpga_top.svh`. Then, you can build the hardware as follows (the last step takes several hours so we run it in the background and pipe the output to `bitgen.log`):

``` bash
mkdir build_hw && cd build_hw
cmake ../hardware
make project
nohup make bitgen &> bitgen.log &
```

## Software build
The software side can be built with:

``` bash
mkdir build_sw && cd build_sw
cmake -DCMAKE_PREFIX_PATH=$HOME/opt ../examples/01_output_buffer_manager
make -j 8
```

## Running the example
After flashing the design to the hardware, you can run the example as follows with default values:

``` bash
./build_sw/output_buffer_manager
```

For simulations (you also need to change to the Coyote sim library), it is recommended to set the parameters like for systems that do not have huge pages and keep the memory footprint reasonable:

``` bash
COYOTE_SIM_DIR=/<path-to-this-repo>/libstf/hardware/build_hw ./build_sw/output_buffer_manager -p -b 65536 -s 1024
```
