//=============================================================================
// Module Name: pwm_wrapper
//=============================================================================
// Description: RTL wrapper for PWM controller for simulation and integration.
// Author: Vyges IP Development Team
// License: Apache-2.0
//=============================================================================

module pwm_wrapper (
    input  logic        pclk_i,
    input  logic        preset_n_i,
    input  logic        psel_i,
    input  logic        penable_i,
    input  logic        pwrite_i,
    input  logic [11:0] paddr_i,
    input  logic [31:0] pwdata_i,
    output logic [31:0] prdata_o,
    output logic        pready_o,
    output logic        pslverr_o,
    output logic [7:0]  pwm_o,
    output logic [7:0]  pwm_n_o,
    input  logic        sync_i,
    output logic        sync_o,
    input  logic        fault_i,
    output logic        fault_o,
    output logic        irq_o,
    output logic        busy_o
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