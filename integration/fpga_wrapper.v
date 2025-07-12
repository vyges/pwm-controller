//=============================================================================
// Module Name: fpga_wrapper
//=============================================================================
// Description: FPGA integration wrapper for PWM controller for Vivado/board use.
// Author: Vyges IP Development Team
// License: Apache-2.0
//=============================================================================

module fpga_wrapper (
    input  wire        clk,
    input  wire        rst_n,
    // APB interface
    input  wire        psel,
    input  wire        penable,
    input  wire        pwrite,
    input  wire [11:0] paddr,
    input  wire [31:0] pwdata,
    output wire [31:0] prdata,
    output wire        pready,
    output wire        pslverr,
    // PWM outputs
    output wire [7:0]  pwm,
    output wire [7:0]  pwm_n,
    // Control/status
    input  wire        sync_in,
    output wire        sync_out,
    input  wire        fault_in,
    output wire        fault_out,
    output wire        irq,
    output wire        busy
);

    pwm_controller dut (
        .pclk_i(clk),
        .preset_n_i(rst_n),
        .psel_i(psel),
        .penable_i(penable),
        .pwrite_i(pwrite),
        .paddr_i(paddr),
        .pwdata_i(pwdata),
        .prdata_o(prdata),
        .pready_o(pready),
        .pslverr_o(pslverr),
        .pwm_o(pwm),
        .pwm_n_o(pwm_n),
        .sync_i(sync_in),
        .sync_o(sync_out),
        .fault_i(fault_in),
        .fault_o(fault_out),
        .irq_o(irq),
        .busy_o(busy)
    );

endmodule 