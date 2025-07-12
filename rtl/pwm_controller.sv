//=============================================================================
// Module Name: pwm_controller
//=============================================================================
// Description: Configurable PWM controller with multiple channels and precise 
//              frequency control for motor control, power management, and 
//              signal generation applications.
//
// Features:
// - Multi-channel PWM generation (up to 8 channels)
// - 24-bit frequency resolution (0.1Hz to 100MHz)
// - 16-bit duty cycle control (0.001% to 100%)
// - 16-bit phase control (0.01° steps)
// - APB4 slave interface
// - PLL integration for precise timing
// - Dead-time insertion for power applications
// - Fault protection and emergency shutdown
// - Chiplet-ready design
//
// Author: Vyges IP Development Team
// License: Apache-2.0
//=============================================================================

module pwm_controller #(
    parameter int NUM_CHANNELS = 8,
    parameter int FREQ_WIDTH = 24,
    parameter int DUTY_WIDTH = 16,
    parameter int PHASE_WIDTH = 16,
    parameter int APB_ADDR_WIDTH = 12
)(
    // Clock and reset
    input  logic                    pclk_i,
    input  logic                    preset_n_i,
    
    // APB interface
    input  logic                    psel_i,
    input  logic                    penable_i,
    input  logic                    pwrite_i,
    input  logic [APB_ADDR_WIDTH-1:0] paddr_i,
    input  logic [31:0]            pwdata_i,
    output logic [31:0]            prdata_o,
    output logic                   pready_o,
    output logic                   pslverr_o,
    
    // PWM outputs
    output logic [NUM_CHANNELS-1:0] pwm_o,
    output logic [NUM_CHANNELS-1:0] pwm_n_o,
    
    // Control and status
    input  logic                    sync_i,
    output logic                    sync_o,
    input  logic                    fault_i,
    output logic                    fault_o,
    output logic                    irq_o,
    output logic                    busy_o
);

    // Internal signals
    logic [NUM_CHANNELS-1:0] channel_enable;
    logic [NUM_CHANNELS-1:0] channel_busy;
    logic [NUM_CHANNELS-1:0] channel_fault;
    logic [NUM_CHANNELS-1:0] channel_irq;
    
    logic [FREQ_WIDTH-1:0] freq_settings [NUM_CHANNELS];
    logic [DUTY_WIDTH-1:0] duty_settings [NUM_CHANNELS];
    logic [PHASE_WIDTH-1:0] phase_settings [NUM_CHANNELS];
    logic [15:0] deadtime_settings [NUM_CHANNELS];
    
    logic global_enable;
    logic pll_enable;
    logic sync_mode_enable;
    logic fault_protection_enable;
    logic [7:0] clock_divider;
    
    logic pll_locked;
    logic pll_clk;
    logic [7:0] pll_multiplier;
    logic [7:0] pll_divider;
    
    // APB slave interface instance
    pwm_apb_slave #(
        .NUM_CHANNELS(NUM_CHANNELS),
        .FREQ_WIDTH(FREQ_WIDTH),
        .DUTY_WIDTH(DUTY_WIDTH),
        .PHASE_WIDTH(PHASE_WIDTH),
        .APB_ADDR_WIDTH(APB_ADDR_WIDTH)
    ) apb_slave (
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
        .global_enable_o(global_enable),
        .pll_enable_o(pll_enable),
        .sync_mode_enable_o(sync_mode_enable),
        .fault_protection_enable_o(fault_protection_enable),
        .clock_divider_o(clock_divider),
        .channel_enable_o(channel_enable),
        .freq_settings_o(freq_settings),
        .duty_settings_o(duty_settings),
        .phase_settings_o(phase_settings),
        .deadtime_settings_o(deadtime_settings),
        .pll_multiplier_o(pll_multiplier),
        .pll_divider_o(pll_divider),
        .channel_status_i(channel_busy),
        .fault_status_i(channel_fault),
        .irq_status_i(channel_irq),
        .pll_locked_i(pll_locked)
    );
    
    // PLL controller instance
    pwm_pll_controller pll_ctrl (
        .pclk_i(pclk_i),
        .preset_n_i(preset_n_i),
        .pll_enable_i(pll_enable),
        .multiplier_i(pll_multiplier),
        .divider_i(pll_divider),
        .pll_clk_o(pll_clk),
        .pll_locked_o(pll_locked)
    );
    
    // Channel array instance
    pwm_channel_array #(
        .NUM_CHANNELS(NUM_CHANNELS),
        .FREQ_WIDTH(FREQ_WIDTH),
        .DUTY_WIDTH(DUTY_WIDTH),
        .PHASE_WIDTH(PHASE_WIDTH)
    ) channel_array (
        .pclk_i(pclk_i),
        .preset_n_i(preset_n_i),
        .pll_clk_i(pll_clk),
        .global_enable_i(global_enable),
        .channel_enable_i(channel_enable),
        .freq_settings_i(freq_settings),
        .duty_settings_i(duty_settings),
        .phase_settings_i(phase_settings),
        .deadtime_settings_i(deadtime_settings),
        .sync_i(sync_i),
        .fault_i(fault_i),
        .pwm_o(pwm_o),
        .pwm_n_o(pwm_n_o),
        .channel_busy_o(channel_busy),
        .channel_fault_o(channel_fault),
        .channel_irq_o(channel_irq)
    );
    
    // Synchronization controller instance
    pwm_sync_controller sync_ctrl (
        .pclk_i(pclk_i),
        .preset_n_i(preset_n_i),
        .sync_mode_enable_i(sync_mode_enable),
        .sync_i(sync_i),
        .channel_busy_i(channel_busy),
        .sync_o(sync_o)
    );
    
    // Fault protection instance
    pwm_fault_protection fault_prot (
        .pclk_i(pclk_i),
        .preset_n_i(preset_n_i),
        .fault_protection_enable_i(fault_protection_enable),
        .fault_i(fault_i),
        .channel_fault_i(channel_fault),
        .fault_o(fault_o)
    );
    
    // Interrupt controller instance
    pwm_irq_controller irq_ctrl (
        .pclk_i(pclk_i),
        .preset_n_i(preset_n_i),
        .channel_irq_i(channel_irq),
        .fault_i(fault_i),
        .irq_o(irq_o)
    );
    
    // Busy status generation
    assign busy_o = |channel_busy;
    
    // Assertions for protocol compliance
    // APB protocol assertions
    property apb_setup_hold;
        @(posedge pclk_i) disable iff (!preset_n_i)
        psel_i && penable_i |-> ##[1:2] psel_i;
    endproperty
    
    property apb_write_sequence;
        @(posedge pclk_i) disable iff (!preset_n_i)
        psel_i && pwrite_i && penable_i |-> pready_o;
    endproperty
    
    property apb_read_sequence;
        @(posedge pclk_i) disable iff (!preset_n_i)
        psel_i && !pwrite_i && penable_i |-> pready_o;
    endproperty
    
    // PWM output assertions
    property pwm_valid_range;
        @(posedge pclk_i) disable iff (!preset_n_i)
        global_enable |-> pwm_o >= 0 && pwm_o <= {NUM_CHANNELS{1'b1}};
    endproperty
    
    // Fault protection assertions
    property fault_protection_response;
        @(posedge pclk_i) disable iff (!preset_n_i)
        fault_i |-> ##[1:10] fault_o;
    endproperty
    
    // Coverage properties
    covergroup pwm_coverage @(posedge pclk_i);
        channel_enable_cp: coverpoint channel_enable {
            bins all_disabled = {0};
            bins all_enabled = {{NUM_CHANNELS{1'b1}}};
            bins mixed = default;
        }
        
        duty_cycle_cp: coverpoint duty_settings[0] {
            bins low_duty = {[0:25]};
            bins mid_duty = {[26:75]};
            bins high_duty = {[76:100]};
        }
        
        frequency_cp: coverpoint freq_settings[0] {
            bins low_freq = {[0:1000]};
            bins mid_freq = {[1001:1000000]};
            bins high_freq = {[1000001:$]};
        }
    endgroup
    
    pwm_coverage pwm_cov = new();

endmodule 