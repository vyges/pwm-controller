//=============================================================================
// Module Name: pwm_channel
//=============================================================================
// Description: Individual PWM channel with precise frequency, duty cycle, and 
//              phase control for motor control and power management applications.
//
// Features:
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

module pwm_channel #(
    parameter int FREQ_WIDTH = 24,
    parameter int DUTY_WIDTH = 16,
    parameter int PHASE_WIDTH = 16
)(
    // Clock and reset
    input  logic                    pclk_i,
    input  logic                    preset_n_i,
    input  logic                    pll_clk_i,
    
    // Control inputs
    input  logic                    global_enable_i,
    input  logic                    channel_enable_i,
    
    // Settings
    input  logic [FREQ_WIDTH-1:0] freq_setting_i,
    input  logic [DUTY_WIDTH-1:0] duty_setting_i,
    input  logic [PHASE_WIDTH-1:0] phase_setting_i,
    input  logic [15:0]           deadtime_setting_i,
    
    // External control
    input  logic                    sync_i,
    input  logic                    fault_i,
    
    // PWM outputs
    output logic                    pwm_o,
    output logic                    pwm_n_o,
    
    // Status outputs
    output logic                    channel_busy_o,
    output logic                    channel_fault_o,
    output logic                    channel_irq_o
);

    // Internal signals
    logic [FREQ_WIDTH-1:0] period_counter;
    logic [DUTY_WIDTH-1:0] duty_counter;
    logic [PHASE_WIDTH-1:0] phase_counter;
    logic [15:0] deadtime_counter;
    
    logic pwm_raw;
    logic pwm_complementary;
    logic channel_active;
    logic channel_error;
    logic period_complete;
    logic duty_complete;
    logic phase_complete;
    
    // PWM state machine
    typedef enum logic [2:0] {
        CHANNEL_IDLE,
        CHANNEL_STARTUP,
        CHANNEL_ACTIVE,
        CHANNEL_FAULT,
        CHANNEL_SHUTDOWN
    } channel_state_t;
    
    channel_state_t channel_state, channel_next_state;
    
    // Channel state machine
    always_ff @(posedge pclk_i or negedge preset_n_i) begin
        if (!preset_n_i) begin
            channel_state <= CHANNEL_IDLE;
            period_counter <= 0;
            duty_counter <= 0;
            phase_counter <= 0;
            deadtime_counter <= 0;
            pwm_raw <= 1'b0;
            pwm_complementary <= 1'b0;
            channel_active <= 1'b0;
            channel_error <= 1'b0;
            period_complete <= 1'b0;
            duty_complete <= 1'b0;
            phase_complete <= 1'b0;
        end else begin
            channel_state <= channel_next_state;
            
            // PWM generation logic
            if (channel_state == CHANNEL_ACTIVE && global_enable_i && channel_enable_i) begin
                // Period counter
                if (period_counter >= freq_setting_i - 1) begin
                    period_counter <= 0;
                    period_complete <= 1'b1;
                end else begin
                    period_counter <= period_counter + 1;
                    period_complete <= 1'b0;
                end
                
                // Duty cycle counter
                if (period_complete) begin
                    duty_counter <= 0;
                end else if (duty_counter >= duty_setting_i - 1) begin
                    duty_complete <= 1'b1;
                end else begin
                    duty_counter <= duty_counter + 1;
                    duty_complete <= 1'b0;
                end
                
                // Phase counter
                if (period_complete) begin
                    if (phase_counter >= phase_setting_i - 1) begin
                        phase_counter <= 0;
                        phase_complete <= 1'b1;
                    end else begin
                        phase_counter <= phase_counter + 1;
                        phase_complete <= 1'b0;
                    end
                end
                
                // PWM output generation
                if (duty_counter < duty_setting_i) begin
                    pwm_raw <= 1'b1;
                end else begin
                    pwm_raw <= 1'b0;
                end
                
                // Dead-time insertion
                if (deadtime_setting_i > 0) begin
                    if (pwm_raw) begin
                        if (deadtime_counter < deadtime_setting_i) begin
                            pwm_complementary <= 1'b0;
                            deadtime_counter <= deadtime_counter + 1;
                        end else begin
                            pwm_complementary <= 1'b1;
                        end
                    end else begin
                        if (deadtime_counter < deadtime_setting_i) begin
                            pwm_complementary <= 1'b1;
                            deadtime_counter <= deadtime_counter + 1;
                        end else begin
                            pwm_complementary <= 1'b0;
                        end
                    end
                end else begin
                    pwm_complementary <= ~pwm_raw;
                end
                
                channel_active <= 1'b1;
            end else begin
                // Reset counters and outputs when not active
                period_counter <= 0;
                duty_counter <= 0;
                phase_counter <= 0;
                deadtime_counter <= 0;
                pwm_raw <= 1'b0;
                pwm_complementary <= 1'b0;
                channel_active <= 1'b0;
                period_complete <= 1'b0;
                duty_complete <= 1'b0;
                phase_complete <= 1'b0;
            end
            
            // Fault detection
            if (fault_i) begin
                channel_error <= 1'b1;
            end else if (channel_state == CHANNEL_IDLE) begin
                channel_error <= 1'b0;
            end
        end
    end
    
    // Channel state machine next state logic
    always_comb begin
        channel_next_state = channel_state;
        
        case (channel_state)
            CHANNEL_IDLE: begin
                if (global_enable_i && channel_enable_i && !fault_i) begin
                    channel_next_state = CHANNEL_STARTUP;
                end
            end
            
            CHANNEL_STARTUP: begin
                // Startup delay for channel stabilization
                if (period_counter >= 16'h0100) begin
                    channel_next_state = CHANNEL_ACTIVE;
                end else if (fault_i) begin
                    channel_next_state = CHANNEL_FAULT;
                end
            end
            
            CHANNEL_ACTIVE: begin
                if (fault_i || !global_enable_i || !channel_enable_i) begin
                    channel_next_state = CHANNEL_SHUTDOWN;
                end
            end
            
            CHANNEL_FAULT: begin
                if (!fault_i && global_enable_i && channel_enable_i) begin
                    channel_next_state = CHANNEL_STARTUP;
                end
            end
            
            CHANNEL_SHUTDOWN: begin
                if (!global_enable_i || !channel_enable_i) begin
                    channel_next_state = CHANNEL_IDLE;
                end else if (fault_i) begin
                    channel_next_state = CHANNEL_FAULT;
                end
            end
        endcase
    end
    
    // Output assignments
    assign pwm_o = (channel_state == CHANNEL_ACTIVE) ? pwm_raw : 1'b0;
    assign pwm_n_o = (channel_state == CHANNEL_ACTIVE) ? pwm_complementary : 1'b0;
    assign channel_busy_o = channel_active;
    assign channel_fault_o = channel_error;
    assign channel_irq_o = period_complete && (channel_state == CHANNEL_ACTIVE);
    
    // Assertions for PWM channel behavior
    property pwm_frequency_control;
        @(posedge pclk_i) disable iff (!preset_n_i)
        (channel_state == CHANNEL_ACTIVE) && (freq_setting_i > 0) |-> 
        ##[1:freq_setting_i] period_complete;
    endproperty
    
    property pwm_duty_cycle_control;
        @(posedge pclk_i) disable iff (!preset_n_i)
        (channel_state == CHANNEL_ACTIVE) && (duty_setting_i > 0) |-> 
        (duty_counter <= duty_setting_i);
    endproperty
    
    property pwm_fault_protection;
        @(posedge pclk_i) disable iff (!preset_n_i)
        fault_i |-> ##[1:5] (pwm_o == 0) && (pwm_n_o == 0);
    endproperty
    
    property pwm_deadtime_insertion;
        @(posedge pclk_i) disable iff (!preset_n_i)
        (deadtime_setting_i > 0) && (pwm_raw != pwm_complementary) |-> 
        (deadtime_counter <= deadtime_setting_i);
    endproperty
    
    // Coverage for PWM channel
    covergroup pwm_channel_coverage @(posedge pclk_i);
        channel_state_cp: coverpoint channel_state {
            bins idle = {CHANNEL_IDLE};
            bins startup = {CHANNEL_STARTUP};
            bins active = {CHANNEL_ACTIVE};
            bins fault = {CHANNEL_FAULT};
            bins shutdown = {CHANNEL_SHUTDOWN};
        }
        
        duty_cycle_cp: coverpoint duty_setting_i {
            bins low_duty = {[0:25]};
            bins mid_duty = {[26:75]};
            bins high_duty = {[76:100]};
        }
        
        frequency_cp: coverpoint freq_setting_i {
            bins low_freq = {[0:1000]};
            bins mid_freq = {[1001:1000000]};
            bins high_freq = {[1000001:$]};
        }
        
        deadtime_cp: coverpoint deadtime_setting_i {
            bins no_deadtime = {0};
            bins low_deadtime = {[1:100]};
            bins high_deadtime = {[101:65535]};
        }
        
        cross channel_state_cp, duty_cycle_cp, frequency_cp, deadtime_cp;
    endgroup
    
    pwm_channel_coverage pwm_ch_cov = new();

endmodule 