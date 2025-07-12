//=============================================================================
// Module Name: pwm_sync_controller
//=============================================================================
// Description: Synchronization controller for PWM channels with external sync 
//              input and cross-channel coordination.
//
// Features:
// - External synchronization input handling
// - Cross-channel synchronization
// - Phase alignment control
// - Synchronization status reporting
//
// Author: Vyges IP Development Team
// License: Apache-2.0
//=============================================================================

module pwm_sync_controller (
    // Clock and reset
    input  logic       pclk_i,
    input  logic       preset_n_i,
    
    // Control inputs
    input  logic       sync_mode_enable_i,
    input  logic       sync_i,
    input  logic [7:0] channel_busy_i,
    
    // Outputs
    output logic       sync_o
);

    // Internal signals
    logic sync_enabled;
    logic sync_detected;
    logic sync_output;
    logic [7:0] sync_counter;
    logic [7:0] channel_busy_reg;
    
    // Synchronization state machine
    typedef enum logic [1:0] {
        SYNC_IDLE,
        SYNC_WAIT,
        SYNC_ACTIVE,
        SYNC_COMPLETE
    } sync_state_t;
    
    sync_state_t sync_state, sync_next_state;
    
    // Synchronization state machine
    always_ff @(posedge pclk_i or negedge preset_n_i) begin
        if (!preset_n_i) begin
            sync_state <= SYNC_IDLE;
            sync_enabled <= 1'b0;
            sync_detected <= 1'b0;
            sync_output <= 1'b0;
            sync_counter <= 8'h00;
            channel_busy_reg <= 8'h00;
        end else begin
            sync_state <= sync_next_state;
            
            // Update registers
            sync_enabled <= sync_mode_enable_i;
            channel_busy_reg <= channel_busy_i;
            
            // Sync detection and generation
            if (sync_state == SYNC_WAIT && sync_i) begin
                sync_detected <= 1'b1;
                sync_counter <= 8'h00;
            end else if (sync_state == SYNC_ACTIVE) begin
                if (sync_counter >= 8'hFF) begin
                    sync_output <= 1'b0;
                end else begin
                    sync_counter <= sync_counter + 1;
                    sync_output <= 1'b1;
                end
            end else begin
                sync_detected <= 1'b0;
                sync_output <= 1'b0;
                sync_counter <= 8'h00;
            end
        end
    end
    
    // Synchronization state machine next state logic
    always_comb begin
        sync_next_state = sync_state;
        
        case (sync_state)
            SYNC_IDLE: begin
                if (sync_enabled && |channel_busy_i) begin
                    sync_next_state = SYNC_WAIT;
                end
            end
            
            SYNC_WAIT: begin
                if (sync_i) begin
                    sync_next_state = SYNC_ACTIVE;
                end else if (!sync_enabled || !(|channel_busy_i)) begin
                    sync_next_state = SYNC_IDLE;
                end
            end
            
            SYNC_ACTIVE: begin
                if (sync_counter >= 8'hFF) begin
                    sync_next_state = SYNC_COMPLETE;
                end else if (!sync_enabled) begin
                    sync_next_state = SYNC_IDLE;
                end
            end
            
            SYNC_COMPLETE: begin
                if (!sync_enabled || !(|channel_busy_i)) begin
                    sync_next_state = SYNC_IDLE;
                end else begin
                    sync_next_state = SYNC_WAIT;
                end
            end
        endcase
    end
    
    // Output assignment
    assign sync_o = sync_output;
    
    // Assertions for synchronization behavior
    property sync_enable_sequence;
        @(posedge pclk_i) disable iff (!preset_n_i)
        sync_mode_enable_i && |channel_busy_i |-> ##[1:10] sync_state != SYNC_IDLE;
    endproperty
    
    property sync_input_response;
        @(posedge pclk_i) disable iff (!preset_n_i)
        sync_i && (sync_state == SYNC_WAIT) |-> ##[1:5] sync_state == SYNC_ACTIVE;
    endproperty
    
    property sync_output_generation;
        @(posedge pclk_i) disable iff (!preset_n_i)
        (sync_state == SYNC_ACTIVE) |-> sync_o;
    endproperty
    
    // Coverage for synchronization
    covergroup sync_coverage @(posedge pclk_i);
        sync_state_cp: coverpoint sync_state {
            bins idle = {SYNC_IDLE};
            bins wait = {SYNC_WAIT};
            bins active = {SYNC_ACTIVE};
            bins complete = {SYNC_COMPLETE};
        }
        
        sync_enable_cp: coverpoint sync_mode_enable_i {
            bins disabled = {0};
            bins enabled = {1};
        }
        
        sync_input_cp: coverpoint sync_i {
            bins no_sync = {0};
            bins sync_pulse = {1};
        }
        
        channel_busy_cp: coverpoint |channel_busy_i {
            bins no_channels = {0};
            bins channels_active = {1};
        }
        
        cross sync_state_cp, sync_enable_cp, sync_input_cp, channel_busy_cp;
    endgroup
    
    sync_coverage sync_cov = new();

endmodule 