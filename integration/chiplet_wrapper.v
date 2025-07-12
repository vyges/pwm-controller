//=============================================================================
// Module Name: chiplet_wrapper
//=============================================================================
// Description: Chiplet integration wrapper for PWM controller for die-to-die/interposer use.
// Author: Vyges IP Development Team
// License: Apache-2.0
//=============================================================================

module chiplet_wrapper (
    input  wire        pclk_i,
    input  wire        preset_n_i,
    input  wire        psel_i,
    input  wire        penable_i,
    input  wire        pwrite_i,
    input  wire [11:0] paddr_i,
    input  wire [31:0] pwdata_i,
    output wire [31:0] prdata_o,
    output wire        pready_o,
    output wire        pslverr_o,
    output wire [7:0]  pwm_o,
    output wire [7:0]  pwm_n_o,
    input  wire        sync_i,
    output wire        sync_o,
    input  wire        fault_i,
    output wire        fault_o,
    output wire        irq_o,
    output wire        busy_o
);

    pwm_controller dut (
        .pclk_i(pclk_i),
        .preset_n_i(preset_n_i),
        .psel_i(psel_i),
        .penable_i(penable_i),
        .pwrite_i(pwrite_i),
        .paddr_i(paddr_i),
        .pwdata_i(pwdata_i),
        .prdata_o(prdata_o),
        .pready_o(pready_o),
        .pslverr_o(pslverr_o),
        .pwm_o(pwm_o),
        .pwm_n_o(pwm_n_o),
        .sync_i(sync_i),
        .sync_o(sync_o),
        .fault_i(fault_i),
        .fault_o(fault_o),
        .irq_o(irq_o),
        .busy_o(busy_o)
    );

endmodule 