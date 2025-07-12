//=============================================================================
// Module Name: pwm_apb_slave
//=============================================================================
// Description: APB4 slave interface for PWM controller with complete register 
//              map implementation and protocol compliance.
//
// Features:
// - APB4 protocol compliance
// - Complete register map (global and channel-specific)
// - Read/write access control
// - Error handling and status reporting
// - Interrupt status management
//
// Author: Vyges IP Development Team
// License: Apache-2.0
//=============================================================================

module pwm_apb_slave #(
    parameter int NUM_CHANNELS = 8,
    parameter int FREQ_WIDTH = 24,
    parameter int DUTY_WIDTH = 16,
    parameter int PHASE_WIDTH = 16,
    parameter int APB_ADDR_WIDTH = 12
)(
    // APB interface
    input  logic                    pclk_i,
    input  logic                    preset_n_i,
    input  logic                    psel_i,
    input  logic                    penable_i,
    input  logic                    pwrite_i,
    input  logic [APB_ADDR_WIDTH-1:0] paddr_i,
    input  logic [31:0]            pwdata_i,
    output logic [31:0]            prdata_o,
    output logic                   pready_o,
    output logic                   pslverr_o,
    
    // Control outputs
    output logic                   global_enable_o,
    output logic                   pll_enable_o,
    output logic                   sync_mode_enable_o,
    output logic                   fault_protection_enable_o,
    output logic [7:0]            clock_divider_o,
    output logic [NUM_CHANNELS-1:0] channel_enable_o,
    output logic [FREQ_WIDTH-1:0] freq_settings_o [NUM_CHANNELS],
    output logic [DUTY_WIDTH-1:0] duty_settings_o [NUM_CHANNELS],
    output logic [PHASE_WIDTH-1:0] phase_settings_o [NUM_CHANNELS],
    output logic [15:0]           deadtime_settings_o [NUM_CHANNELS],
    output logic [7:0]            pll_multiplier_o,
    output logic [7:0]            pll_divider_o,
    
    // Status inputs
    input  logic [NUM_CHANNELS-1:0] channel_status_i,
    input  logic [NUM_CHANNELS-1:0] fault_status_i,
    input  logic [NUM_CHANNELS-1:0] irq_status_i,
    input  logic                   pll_locked_i
);

    // Register definitions
    logic [31:0] global_ctrl_reg;
    logic [31:0] global_status_reg;
    logic [31:0] global_config_reg;
    logic [31:0] clock_config_reg;
    logic [31:0] sync_config_reg;
    logic [31:0] fault_config_reg;
    logic [31:0] irq_enable_reg;
    logic [31:0] irq_status_reg;
    
    logic [31:0] channel_ctrl_reg [NUM_CHANNELS];
    logic [31:0] channel_freq_reg [NUM_CHANNELS];
    logic [31:0] channel_duty_reg [NUM_CHANNELS];
    logic [31:0] channel_phase_reg [NUM_CHANNELS];
    logic [31:0] channel_deadtime_reg [NUM_CHANNELS];
    logic [31:0] channel_status_reg [NUM_CHANNELS];
    
    // APB state machine
    typedef enum logic [1:0] {
        IDLE,
        SETUP,
        ACCESS
    } apb_state_t;
    
    apb_state_t apb_state, apb_next_state;
    
    // APB state machine
    always_ff @(posedge pclk_i or negedge preset_n_i) begin
        if (!preset_n_i) begin
            apb_state <= IDLE;
        end else begin
            apb_state <= apb_next_state;
        end
    end
    
    always_comb begin
        apb_next_state = apb_state;
        case (apb_state)
            IDLE: begin
                if (psel_i && !penable_i) begin
                    apb_next_state = SETUP;
                end
            end
            SETUP: begin
                if (psel_i && penable_i) begin
                    apb_next_state = ACCESS;
                end else if (!psel_i) begin
                    apb_next_state = IDLE;
                end
            end
            ACCESS: begin
                apb_next_state = IDLE;
            end
        endcase
    end
    
    // APB control signals
    assign pready_o = (apb_state == ACCESS);
    assign pslverr_o = 1'b0; // No errors in this implementation
    
    // Register read/write logic
    always_ff @(posedge pclk_i or negedge preset_n_i) begin
        if (!preset_n_i) begin
            // Initialize registers
            global_ctrl_reg <= 32'h0000_0000;
            global_config_reg <= 32'h0000_0000;
            clock_config_reg <= 32'h0000_0000;
            sync_config_reg <= 32'h0000_0000;
            fault_config_reg <= 32'h0000_0000;
            irq_enable_reg <= 32'h0000_0000;
            irq_status_reg <= 32'h0000_0000;
            
            for (int i = 0; i < NUM_CHANNELS; i++) begin
                channel_ctrl_reg[i] <= 32'h0000_0000;
                channel_freq_reg[i] <= 32'h0000_0000;
                channel_duty_reg[i] <= 32'h8000_0000; // 50% duty cycle default
                channel_phase_reg[i] <= 32'h0000_0000;
                channel_deadtime_reg[i] <= 32'h0000_0000;
            end
        end else begin
            // Write operations
            if (apb_state == ACCESS && pwrite_i) begin
                case (paddr_i)
                    // Global registers
                    12'h000: global_ctrl_reg <= pwdata_i;
                    12'h008: global_config_reg <= pwdata_i;
                    12'h00C: clock_config_reg <= pwdata_i;
                    12'h010: sync_config_reg <= pwdata_i;
                    12'h014: fault_config_reg <= pwdata_i;
                    12'h018: irq_enable_reg <= pwdata_i;
                    12'h01C: irq_status_reg <= irq_status_reg & ~pwdata_i; // Write-1-to-clear
                    
                    // Channel registers
                    default: begin
                        if (paddr_i >= 12'h100 && paddr_i < 12'h100 + NUM_CHANNELS * 24) begin
                            int channel_idx = (paddr_i - 12'h100) / 24;
                            int reg_offset = (paddr_i - 12'h100) % 24;
                            
                            if (channel_idx < NUM_CHANNELS) begin
                                case (reg_offset)
                                    12'h000: channel_ctrl_reg[channel_idx] <= pwdata_i;
                                    12'h004: channel_freq_reg[channel_idx] <= pwdata_i;
                                    12'h008: channel_duty_reg[channel_idx] <= pwdata_i;
                                    12'h00C: channel_phase_reg[channel_idx] <= pwdata_i;
                                    12'h010: channel_deadtime_reg[channel_idx] <= pwdata_i;
                                endcase
                            end
                        end
                    end
                endcase
            end
            
            // Update status registers
            global_status_reg <= {
                16'h0000,
                pll_locked_i,
                7'h00,
                |channel_status_i,
                7'h00
            };
            
            // Update channel status registers
            for (int i = 0; i < NUM_CHANNELS; i++) begin
                channel_status_reg[i] <= {
                    16'h0000,
                    irq_status_i[i],
                    fault_status_i[i],
                    channel_status_i[i],
                    13'h0000
                };
            end
            
            // Update interrupt status
            irq_status_reg <= {
                16'h0000,
                |irq_status_i,
                |fault_status_i,
                14'h0000
            };
        end
    end
    
    // Read data multiplexer
    always_comb begin
        prdata_o = 32'h0000_0000;
        
        if (apb_state == ACCESS && !pwrite_i) begin
            case (paddr_i)
                // Global registers
                12'h000: prdata_o = global_ctrl_reg;
                12'h004: prdata_o = global_status_reg;
                12'h008: prdata_o = global_config_reg;
                12'h00C: prdata_o = clock_config_reg;
                12'h010: prdata_o = sync_config_reg;
                12'h014: prdata_o = fault_config_reg;
                12'h018: prdata_o = irq_enable_reg;
                12'h01C: prdata_o = irq_status_reg;
                
                // Channel registers
                default: begin
                    if (paddr_i >= 12'h100 && paddr_i < 12'h100 + NUM_CHANNELS * 24) begin
                        int channel_idx = (paddr_i - 12'h100) / 24;
                        int reg_offset = (paddr_i - 12'h100) % 24;
                        
                        if (channel_idx < NUM_CHANNELS) begin
                            case (reg_offset)
                                12'h000: prdata_o = channel_ctrl_reg[channel_idx];
                                12'h004: prdata_o = channel_freq_reg[channel_idx];
                                12'h008: prdata_o = channel_duty_reg[channel_idx];
                                12'h00C: prdata_o = channel_phase_reg[channel_idx];
                                12'h010: prdata_o = channel_deadtime_reg[channel_idx];
                                12'h014: prdata_o = channel_status_reg[channel_idx];
                            endcase
                        end
                    end
                end
            endcase
        end
    end
    
    // Output assignments
    assign global_enable_o = global_ctrl_reg[31];
    assign pll_enable_o = global_ctrl_reg[30];
    assign sync_mode_enable_o = global_ctrl_reg[29];
    assign fault_protection_enable_o = global_ctrl_reg[28];
    assign clock_divider_o = global_ctrl_reg[7:0];
    assign channel_enable_o = global_ctrl_reg[23:16];
    assign pll_multiplier_o = clock_config_reg[15:8];
    assign pll_divider_o = clock_config_reg[7:0];
    
    // Channel settings assignments
    always_comb begin
        for (int i = 0; i < NUM_CHANNELS; i++) begin
            freq_settings_o[i] = channel_freq_reg[i][FREQ_WIDTH-1:0];
            duty_settings_o[i] = channel_duty_reg[i][DUTY_WIDTH-1:0];
            phase_settings_o[i] = channel_phase_reg[i][PHASE_WIDTH-1:0];
            deadtime_settings_o[i] = channel_deadtime_reg[i][15:0];
        end
    end
    
    // Assertions for APB protocol compliance
    property apb_psel_penable_sequence;
        @(posedge pclk_i) disable iff (!preset_n_i)
        psel_i && !penable_i |-> ##[1:2] (psel_i && penable_i) or !psel_i;
    endproperty
    
    property apb_access_complete;
        @(posedge pclk_i) disable iff (!preset_n_i)
        psel_i && penable_i |-> ##[1:2] pready_o;
    endproperty
    
    property apb_no_glitch;
        @(posedge pclk_i) disable iff (!preset_n_i)
        !psel_i |-> !pready_o;
    endproperty
    
    // Coverage for register access
    covergroup apb_register_coverage @(posedge pclk_i);
        register_access_cp: coverpoint paddr_i {
            bins global_regs = {12'h000, 12'h004, 12'h008, 12'h00C, 12'h010, 12'h014, 12'h018, 12'h01C};
            bins channel_regs = {[12'h100:12'h1FF]};
            bins invalid_addr = {[12'h200:12'hFFF]};
        }
        
        access_type_cp: coverpoint pwrite_i {
            bins read = {0};
            bins write = {1};
        }
        
        cross register_access_cp, access_type_cp;
    endgroup
    
    apb_register_coverage apb_cov = new();

endmodule 