[![Vyges IP Template](https://img.shields.io/badge/template-vyges--ip--template-blue)](https://github.com/vyges/vyges-ip-template)
[![Use this template](https://img.shields.io/badge/Use%20this%20template-vyges--ip--template-brightgreen?style=for-the-badge)](https://github.com/vyges/vyges-ip-template/generate)
![License: Apache-2.0](https://img.shields.io/badge/License-Apache--2.0-blue.svg)
![Build](https://github.com/vyges/vyges-ip-template/actions/workflows/test.yml/badge.svg)

# PWM Controller IP - Quickstart

## Overview
This repository contains a configurable, multi-channel PWM controller IP core, ready for SoC, FPGA, and chiplet integration. It supports APB4, precise frequency/duty/phase control, and advanced safety features.

## Directory Structure
- `rtl/` - SystemVerilog RTL source
- `tb/` - Testbenches (SystemVerilog and cocotb)
- `integration/` - Wrappers and example top-levels for SoC, FPGA, chiplet
- `flow/openlane/` - OpenLane ASIC flow config
- `flow/vivado/` - Vivado FPGA flow scripts
- `docs/` - Design spec and documentation

## Simulation (Verilator/SystemVerilog)
```sh
# Example: Run SystemVerilog testbench
cd tb/
make -f Makefile sv_tb
# Or run with Verilator
make -f Makefile verilator
```

## Simulation (Python/cocotb)
```sh
cd tb/cocotb/
make
```

## ASIC Synthesis (OpenLane)
```sh
cd flow/openlane/
# Edit config.json as needed
make
```

## FPGA Synthesis (Vivado)
```sh
cd flow/vivado/
vivado -mode batch -source create_project.tcl
```

## Example Integration
- **SoC/Simulation:** See `integration/example_soc_top.v` for APB master + PWM
- **FPGA:** See `integration/example_fpga_top.v` for board-level instantiation
- **Chiplet:** See `integration/example_chiplet_top.v` for die-to-die integration

## APB Register Map
See `docs/PWM-Controller_design_spec.md` for full register and interface details.

## Support
For questions, open an issue or contact the Vyges IP team.
