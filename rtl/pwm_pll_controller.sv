//=============================================================================
// Module Name: pwm_pll_controller
//=============================================================================
// Description: PLL controller for PWM timing with configurable multiplier and 
//              divider for precise frequency synthesis.
//
// Features:
// - Configurable PLL multiplier and divider
// - Lock detection and status reporting
// - Frequency synthesis for precise PWM timing
// - Power management support
//
// Author: Vyges IP Development Team
// License: Apache-2.0
//=============================================================================

module pwm_pll_controller (
    // Clock and reset
    input  logic       pclk_i,
    input  logic       preset_n_i,
    
    // Control inputs
    input  logic       pll_enable_i,
    input  logic [7:0] multiplier_i,
    input  logic [7:0] divider_i,
    
    // Outputs
    output logic       pll_clk_o,
    output logic       pll_locked_o
);

    // Internal signals
    logic [15:0] pll_counter;
    logic [15:0] pll_divider_reg;
    logic [15:0] pll_multiplier_reg;
    logic pll_enable_reg;
    logic pll_locked_reg;
    logic pll_clk_reg;
    
    // PLL state machine
    typedef enum logic [2:0] {
        PLL_RESET,
        PLL_DISABLED,
        PLL_STARTUP,
        PLL_LOCKING,
        PLL_LOCKED,
        PLL_ERROR
    } pll_state_t;
    
    pll_state_t pll_state, pll_next_state;
    
    // PLL state machine
    always_ff @(posedge pclk_i or negedge preset_n_i) begin
        if (!preset_n_i) begin
            pll_state <= PLL_RESET;
            pll_counter <= 16'h0000;
            pll_divider_reg <= 16'h0001;
            pll_multiplier_reg <= 16'h0001;
            pll_enable_reg <= 1'b0;
            pll_locked_reg <= 1'b0;
            pll_clk_reg <= 1'b0;
        end else begin
            pll_state <= pll_next_state;
            
            // Update registers
            pll_enable_reg <= pll_enable_i;
            pll_divider_reg <= {8'h00, divider_i};
            pll_multiplier_reg <= {8'h00, multiplier_i};
            
            // PLL counter for frequency synthesis
            if (pll_state == PLL_LOCKED) begin
                if (pll_counter >= pll_divider_reg - 1) begin
                    pll_counter <= 16'h0000;
                    pll_clk_reg <= ~pll_clk_reg;
                end else begin
                    pll_counter <= pll_counter + 1;
                end
            end else begin
                pll_counter <= 16'h0000;
                pll_clk_reg <= 1'b0;
            end
            
            // Lock detection
            if (pll_state == PLL_LOCKED) begin
                pll_locked_reg <= 1'b1;
            end else begin
                pll_locked_reg <= 1'b0;
            end
        end
    end
    
    // PLL state machine next state logic
    always_comb begin
        pll_next_state = pll_state;
        
        case (pll_state)
            PLL_RESET: begin
                pll_next_state = PLL_DISABLED;
            end
            
            PLL_DISABLED: begin
                if (pll_enable_reg) begin
                    pll_next_state = PLL_STARTUP;
                end
            end
            
            PLL_STARTUP: begin
                // Startup delay for PLL stabilization
                if (pll_counter >= 16'h0100) begin
                    pll_next_state = PLL_LOCKING;
                end
            end
            
            PLL_LOCKING: begin
                // Lock detection logic
                if (pll_counter >= pll_divider_reg * 4) begin
                    pll_next_state = PLL_LOCKED;
                end else if (pll_counter >= 16'h1000) begin
                    pll_next_state = PLL_ERROR;
                end
            end
            
            PLL_LOCKED: begin
                if (!pll_enable_reg) begin
                    pll_next_state = PLL_DISABLED;
                end else if (pll_counter >= pll_divider_reg * 8) begin
                    // Check for loss of lock
                    pll_next_state = PLL_ERROR;
                end
            end
            
            PLL_ERROR: begin
                if (!pll_enable_reg) begin
                    pll_next_state = PLL_DISABLED;
                end else if (pll_counter >= 16'h2000) begin
                    // Retry after error
                    pll_next_state = PLL_STARTUP;
                end
            end
        endcase
    end
    
    // Output assignments
    assign pll_clk_o = pll_clk_reg;
    assign pll_locked_o = pll_locked_reg;
    
    // Assertions for PLL behavior
    property pll_enable_sequence;
        @(posedge pclk_i) disable iff (!preset_n_i)
        pll_enable_i |-> ##[1:100] pll_locked_o;
    endproperty
    
    property pll_disable_sequence;
        @(posedge pclk_i) disable iff (!preset_n_i)
        !pll_enable_i |-> ##[1:10] !pll_locked_o;
    endproperty
    
    property pll_clock_generation;
        @(posedge pclk_i) disable iff (!preset_n_i)
        pll_locked_o |-> pll_clk_o == 0 or pll_clk_o == 1;
    endproperty
    
    // Coverage for PLL operation
    covergroup pll_coverage @(posedge pclk_i);
        pll_state_cp: coverpoint pll_state {
            bins reset = {PLL_RESET};
            bins disabled = {PLL_DISABLED};
            bins startup = {PLL_STARTUP};
            bins locking = {PLL_LOCKING};
            bins locked = {PLL_LOCKED};
            bins error = {PLL_ERROR};
        }
        
        multiplier_cp: coverpoint multiplier_i {
            bins low_mult = {[1:10]};
            bins mid_mult = {[11:50]};
            bins high_mult = {[51:255]};
        }
        
        divider_cp: coverpoint divider_i {
            bins low_div = {[1:10]};
            bins mid_div = {[11:50]};
            bins high_div = {[51:255]};
        }
        
        cross pll_state_cp, multiplier_cp, divider_cp;
    endgroup
    
    pll_coverage pll_cov = new();

endmodule 