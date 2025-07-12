//=============================================================================
// Module Name: pwm_fault_protection
//=============================================================================
// Description: Fault protection system for PWM controller with emergency 
//              shutdown and fault status reporting.
//
// Features:
// - External fault input handling
// - Channel fault detection
// - Emergency shutdown response
// - Fault status reporting
// - Fault recovery mechanisms
//
// Author: Vyges IP Development Team
// License: Apache-2.0
//=============================================================================

module pwm_fault_protection (
    // Clock and reset
    input  logic       pclk_i,
    input  logic       preset_n_i,
    
    // Control inputs
    input  logic       fault_protection_enable_i,
    input  logic       fault_i,
    input  logic [7:0] channel_fault_i,
    
    // Outputs
    output logic       fault_o
);

    // Internal signals
    logic fault_enabled;
    logic external_fault;
    logic internal_fault;
    logic fault_output;
    logic [7:0] fault_counter;
    logic [7:0] channel_fault_reg;
    
    // Fault state machine
    typedef enum logic [2:0] {
        FAULT_NORMAL,
        FAULT_DETECTED,
        FAULT_ACTIVE,
        FAULT_RECOVERY,
        FAULT_LATCHED
    } fault_state_t;
    
    fault_state_t fault_state, fault_next_state;
    
    // Fault state machine
    always_ff @(posedge pclk_i or negedge preset_n_i) begin
        if (!preset_n_i) begin
            fault_state <= FAULT_NORMAL;
            fault_enabled <= 1'b0;
            external_fault <= 1'b0;
            internal_fault <= 1'b0;
            fault_output <= 1'b0;
            fault_counter <= 8'h00;
            channel_fault_reg <= 8'h00;
        end else begin
            fault_state <= fault_next_state;
            
            // Update registers
            fault_enabled <= fault_protection_enable_i;
            external_fault <= fault_i;
            channel_fault_reg <= channel_fault_i;
            
            // Fault detection logic
            internal_fault <= |channel_fault_i;
            
            // Fault counter for recovery timing
            if (fault_state == FAULT_ACTIVE) begin
                if (fault_counter >= 8'hFF) begin
                    fault_counter <= 8'hFF;
                end else begin
                    fault_counter <= fault_counter + 1;
                end
            end else if (fault_state == FAULT_RECOVERY) begin
                if (fault_counter > 0) begin
                    fault_counter <= fault_counter - 1;
                end
            end else begin
                fault_counter <= 8'h00;
            end
            
            // Fault output generation
            if (fault_state == FAULT_ACTIVE || fault_state == FAULT_LATCHED) begin
                fault_output <= 1'b1;
            end else begin
                fault_output <= 1'b0;
            end
        end
    end
    
    // Fault state machine next state logic
    always_comb begin
        fault_next_state = fault_state;
        
        case (fault_state)
            FAULT_NORMAL: begin
                if (fault_enabled && (external_fault || internal_fault)) begin
                    fault_next_state = FAULT_DETECTED;
                end
            end
            
            FAULT_DETECTED: begin
                // Immediate transition to active for fast response
                fault_next_state = FAULT_ACTIVE;
            end
            
            FAULT_ACTIVE: begin
                if (!fault_enabled) begin
                    fault_next_state = FAULT_NORMAL;
                end else if (!external_fault && !internal_fault) begin
                    fault_next_state = FAULT_RECOVERY;
                end else if (fault_counter >= 8'hFF) begin
                    fault_next_state = FAULT_LATCHED;
                end
            end
            
            FAULT_RECOVERY: begin
                if (!fault_enabled) begin
                    fault_next_state = FAULT_NORMAL;
                end else if (external_fault || internal_fault) begin
                    fault_next_state = FAULT_ACTIVE;
                end else if (fault_counter == 0) begin
                    fault_next_state = FAULT_NORMAL;
                end
            end
            
            FAULT_LATCHED: begin
                if (!fault_enabled) begin
                    fault_next_state = FAULT_NORMAL;
                end else if (!external_fault && !internal_fault) begin
                    fault_next_state = FAULT_RECOVERY;
                end
            end
        endcase
    end
    
    // Output assignment
    assign fault_o = fault_output;
    
    // Assertions for fault protection behavior
    property fault_detection_response;
        @(posedge pclk_i) disable iff (!preset_n_i)
        fault_enabled && (external_fault || internal_fault) |-> ##[1:5] fault_o;
    endproperty
    
    property fault_recovery_sequence;
        @(posedge pclk_i) disable iff (!preset_n_i)
        fault_state == FAULT_ACTIVE && !external_fault && !internal_fault |-> 
        ##[1:10] fault_state == FAULT_RECOVERY;
    endproperty
    
    property fault_latch_behavior;
        @(posedge pclk_i) disable iff (!preset_n_i)
        fault_state == FAULT_LATCHED |-> fault_o;
    endproperty
    
    // Coverage for fault protection
    covergroup fault_coverage @(posedge pclk_i);
        fault_state_cp: coverpoint fault_state {
            bins normal = {FAULT_NORMAL};
            bins detected = {FAULT_DETECTED};
            bins active = {FAULT_ACTIVE};
            bins recovery = {FAULT_RECOVERY};
            bins latched = {FAULT_LATCHED};
        }
        
        fault_enable_cp: coverpoint fault_protection_enable_i {
            bins disabled = {0};
            bins enabled = {1};
        }
        
        external_fault_cp: coverpoint external_fault {
            bins no_fault = {0};
            bins fault_active = {1};
        }
        
        internal_fault_cp: coverpoint internal_fault {
            bins no_fault = {0};
            bins fault_active = {1};
        }
        
        fault_output_cp: coverpoint fault_o {
            bins no_fault = {0};
            bins fault_active = {1};
        }
        
        cross fault_state_cp, fault_enable_cp, external_fault_cp, internal_fault_cp, fault_output_cp;
    endgroup
    
    fault_coverage fault_cov = new();

endmodule 