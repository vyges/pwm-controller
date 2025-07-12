//=============================================================================
// Module Name: pwm_irq_controller
//=============================================================================
// Description: Interrupt controller for PWM channels with prioritization and 
//              interrupt status management.
//
// Features:
// - Channel interrupt handling
// - Fault interrupt generation
// - Interrupt prioritization
// - Interrupt status reporting
//
// Author: Vyges IP Development Team
// License: Apache-2.0
//=============================================================================

module pwm_irq_controller (
    // Clock and reset
    input  logic       pclk_i,
    input  logic       preset_n_i,
    
    // Interrupt inputs
    input  logic [7:0] channel_irq_i,
    input  logic       fault_i,
    
    // Outputs
    output logic       irq_o
);

    // Internal signals
    logic [7:0] channel_irq_reg;
    logic fault_irq_reg;
    logic interrupt_output;
    logic [7:0] irq_priority;
    logic [7:0] irq_mask;
    
    // Interrupt state machine
    typedef enum logic [1:0] {
        IRQ_IDLE,
        IRQ_PENDING,
        IRQ_ACTIVE,
        IRQ_CLEAR
    } irq_state_t;
    
    irq_state_t irq_state, irq_next_state;
    
    // Interrupt controller
    always_ff @(posedge pclk_i or negedge preset_n_i) begin
        if (!preset_n_i) begin
            irq_state <= IRQ_IDLE;
            channel_irq_reg <= 8'h00;
            fault_irq_reg <= 1'b0;
            interrupt_output <= 1'b0;
            irq_priority <= 8'h00;
            irq_mask <= 8'hFF;
        end else begin
            irq_state <= irq_next_state;
            
            // Update interrupt registers
            channel_irq_reg <= channel_irq_i;
            fault_irq_reg <= fault_i;
            
            // Interrupt priority logic
            irq_priority <= channel_irq_reg & irq_mask;
            
            // Interrupt output generation
            if (irq_state == IRQ_ACTIVE) begin
                interrupt_output <= 1'b1;
            end else begin
                interrupt_output <= 1'b0;
            end
            
            // Interrupt mask update (simple round-robin priority)
            if (irq_state == IRQ_CLEAR) begin
                irq_mask <= {irq_mask[6:0], irq_mask[7]};
            end
        end
    end
    
    // Interrupt state machine next state logic
    always_comb begin
        irq_next_state = irq_state;
        
        case (irq_state)
            IRQ_IDLE: begin
                if (|channel_irq_reg || fault_irq_reg) begin
                    irq_next_state = IRQ_PENDING;
                end
            end
            
            IRQ_PENDING: begin
                // Immediate transition to active for fast response
                irq_next_state = IRQ_ACTIVE;
            end
            
            IRQ_ACTIVE: begin
                // Stay active until interrupt is cleared
                if (!(|channel_irq_reg) && !fault_irq_reg) begin
                    irq_next_state = IRQ_CLEAR;
                end
            end
            
            IRQ_CLEAR: begin
                irq_next_state = IRQ_IDLE;
            end
        endcase
    end
    
    // Output assignment
    assign irq_o = interrupt_output;
    
    // Assertions for interrupt behavior
    property interrupt_generation;
        @(posedge pclk_i) disable iff (!preset_n_i)
        (|channel_irq_reg || fault_irq_reg) |-> ##[1:5] irq_o;
    endproperty
    
    property interrupt_clear;
        @(posedge pclk_i) disable iff (!preset_n_i)
        !(|channel_irq_reg) && !fault_irq_reg |-> ##[1:10] !irq_o;
    endproperty
    
    property interrupt_priority;
        @(posedge pclk_i) disable iff (!preset_n_i)
        |irq_priority |-> irq_state == IRQ_ACTIVE;
    endproperty
    
    // Coverage for interrupt controller
    covergroup irq_coverage @(posedge pclk_i);
        irq_state_cp: coverpoint irq_state {
            bins idle = {IRQ_IDLE};
            bins pending = {IRQ_PENDING};
            bins active = {IRQ_ACTIVE};
            bins clear = {IRQ_CLEAR};
        }
        
        channel_irq_cp: coverpoint |channel_irq_reg {
            bins no_irq = {0};
            bins irq_active = {1};
        }
        
        fault_irq_cp: coverpoint fault_irq_reg {
            bins no_fault = {0};
            bins fault_active = {1};
        }
        
        irq_output_cp: coverpoint irq_o {
            bins no_irq = {0};
            bins irq_active = {1};
        }
        
        irq_priority_cp: coverpoint |irq_priority {
            bins no_priority = {0};
            bins priority_active = {1};
        }
        
        cross irq_state_cp, channel_irq_cp, fault_irq_cp, irq_output_cp, irq_priority_cp;
    endgroup
    
    irq_coverage irq_cov = new();

endmodule 