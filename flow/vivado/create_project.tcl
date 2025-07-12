# Vivado project creation script for PWM Controller
create_project pwm_controller ./pwm_controller_vivado -part xc7a35ticsg324-1L
set_property board_part digilentinc:arty-a7-35:part0:1.0 [current_project]

# Add RTL files
add_files ../../rtl/pwm_controller.sv
add_files ../../rtl/pwm_apb_slave.sv
add_files ../../rtl/pwm_pll_controller.sv
add_files ../../rtl/pwm_channel_array.sv
add_files ../../rtl/pwm_channel.sv
add_files ../../rtl/pwm_sync_controller.sv
add_files ../../rtl/pwm_fault_protection.sv
add_files ../../rtl/pwm_irq_controller.sv
set_property file_type SystemVerilog [get_files *.sv]

# Add constraints
add_files ../../constraints/pwm_controller.xdc
set_property file_type XDC [get_files *.xdc]

# Create IP cores
create_ip -name clk_wiz -vendor xilinx.com -library ip -version 6.0 -module_name clk_wiz_0 