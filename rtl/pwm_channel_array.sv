//=============================================================================
// Module Name: pwm_channel_array
//=============================================================================
// Description: Multi-channel PWM generation array with precise frequency, 
//              duty cycle, and phase control for motor control and power 
//              management applications.
//
// Features:
// - Multi-channel PWM generation (configurable number of channels)
// - 24-bit frequency resolution (0.1Hz to 100MHz)
// - 16-bit duty cycle control (0.001% to 100%)
// - 16-bit phase control (0.01° steps)
// - Dead-time insertion for power applications
// - Fault protection and emergency shutdown
// - Synchronization support
//
// Author: Vyges IP Development Team
// License: Apache-2.0
//=============================================================================

module pwm_channel_array #(
    parameter int NUM_CHANNELS = 8,
    parameter int FREQ_WIDTH = 24,
    parameter int DUTY_WIDTH = 16,
    parameter int PHASE_WIDTH = 16
)(
    // Clock and reset
    input  logic                    pclk_i,
    input  logic                    preset_n_i,
    input  logic                    pll_clk_i,
    
    // Global control
    input  logic                    global_enable_i,
    input  logic [NUM_CHANNELS-1:0] channel_enable_i,
    
    // Channel settings
    input  logic [FREQ_WIDTH-1:0] freq_settings_i [NUM_CHANNELS],
    input  logic [DUTY_WIDTH-1:0] duty_settings_i [NUM_CHANNELS],
    input  logic [PHASE_WIDTH-1:0] phase_settings_i [NUM_CHANNELS],
    input  logic [15:0]           deadtime_settings_i [NUM_CHANNELS],
    
    // External control
    input  logic                    sync_i,
    input  logic                    fault_i,
    
    // PWM outputs
    output logic [NUM_CHANNELS-1:0] pwm_o,
    output logic [NUM_CHANNELS-1:0] pwm_n_o,
    
    // Status outputs
    output logic [NUM_CHANNELS-1:0] channel_busy_o,
    output logic [NUM_CHANNELS-1:0] channel_fault_o,
    output logic [NUM_CHANNELS-1:0] channel_irq_o
);

    // Internal signals for each channel
    logic [NUM_CHANNELS-1:0] pwm_raw;
    logic [NUM_CHANNELS-1:0] pwm_complementary;
    logic [NUM_CHANNELS-1:0] channel_active;
    logic [NUM_CHANNELS-1:0] channel_error;
    
    // Generate individual PWM channels
    genvar i;
    generate
        for (i = 0; i < NUM_CHANNELS; i++) begin : pwm_channels
            pwm_channel #(
                .FREQ_WIDTH(FREQ_WIDTH),
                .DUTY_WIDTH(DUTY_WIDTH),
                .PHASE_WIDTH(PHASE_WIDTH)
            ) pwm_ch (
                .pclk_i(pclk_i),
                .preset_n_i(preset_n_i),
                .pll_clk_i(pll_clk_i),
                .global_enable_i(global_enable_i),
                .channel_enable_i(channel_enable_i[i]),
                .freq_setting_i(freq_settings_i[i]),
                .duty_setting_i(duty_settings_i[i]),
                .phase_setting_i(phase_settings_i[i]),
                .deadtime_setting_i(deadtime_settings_i[i]),
                .sync_i(sync_i),
                .fault_i(fault_i),
                .pwm_o(pwm_raw[i]),
                .pwm_n_o(pwm_complementary[i]),
                .channel_busy_o(channel_busy_o[i]),
                .channel_fault_o(channel_fault_o[i]),
                .channel_irq_o(channel_irq_o[i])
            );
        end
    endgenerate
    
    // Output assignments with fault protection
    always_comb begin
        for (int j = 0; j < NUM_CHANNELS; j++) begin
            if (fault_i || channel_fault_o[j]) begin
                // Fault condition - disable outputs
                pwm_o[j] = 1'b0;
                pwm_n_o[j] = 1'b0;
            end else begin
                // Normal operation
                pwm_o[j] = pwm_raw[j];
                pwm_n_o[j] = pwm_complementary[j];
            end
        end
    end
    
    // Assertions for channel array behavior
    property channel_enable_consistency;
        @(posedge pclk_i) disable iff (!preset_n_i)
        global_enable_i && channel_enable_i[0] |-> ##[1:100] channel_busy_o[0];
    endproperty
    
    property fault_protection;
        @(posedge pclk_i) disable iff (!preset_n_i)
        fault_i |-> ##[1:5] (pwm_o == 0) && (pwm_n_o == 0);
    endproperty
    
    property channel_independence;
        @(posedge pclk_i) disable iff (!preset_n_i)
        channel_enable_i[0] && !channel_enable_i[1] |-> 
        channel_busy_o[0] && !channel_busy_o[1];
    endproperty
    
    // Coverage for channel array
    covergroup channel_array_coverage @(posedge pclk_i);
        active_channels_cp: coverpoint channel_enable_i {
            bins none_active = {0};
            bins all_active = {{NUM_CHANNELS{1'b1}}};
            bins mixed_active = default;
        }
        
        fault_conditions_cp: coverpoint fault_i {
            bins no_fault = {0};
            bins fault_active = {1};
        }
        
        sync_conditions_cp: coverpoint sync_i {
            bins no_sync = {0};
            bins sync_active = {1};
        }
        
        cross active_channels_cp, fault_conditions_cp, sync_conditions_cp;
    endgroup
    
    channel_array_coverage ch_array_cov = new();

endmodule 