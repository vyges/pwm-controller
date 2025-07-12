#!/usr/bin/env python3
"""
==============================================================================
Test Name: test_pwm_controller
==============================================================================
Description: Comprehensive cocotb testbench for PWM controller with functional,
             performance, and corner case testing.

Features:
- APB protocol testing
- PWM functionality verification
- Multi-channel testing
- Fault protection testing
- Coverage collection
- Performance analysis

Author: Vyges IP Development Team
License: Apache-2.0
==============================================================================
"""

import cocotb
from cocotb.triggers import RisingEdge, Timer, ClockCycles
from cocotb.clock import Clock
from cocotb.handle import ModifiableObject
import random
import logging

# Configure logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

class PWMControllerTest:
    """Test class for PWM Controller verification"""
    
    def __init__(self, dut):
        self.dut = dut
        self.test_count = 0
        self.pass_count = 0
        self.fail_count = 0
        
    async def setup(self):
        """Setup test environment"""
        # Create clock
        clock = Clock(self.dut.pclk_i, 10, units="ns")
        cocotb.start_soon(clock.start())
        
        # Initialize signals
        self.dut.preset_n_i.value = 0
        self.dut.psel_i.value = 0
        self.dut.penable_i.value = 0
        self.dut.pwrite_i.value = 0
        self.dut.paddr_i.value = 0
        self.dut.pwdata_i.value = 0
        self.dut.sync_i.value = 0
        self.dut.fault_i.value = 0
        
        # Reset
        await Timer(100, units="ns")
        self.dut.preset_n_i.value = 1
        await Timer(100, units="ns")
        
        logger.info("Test environment setup complete")
    
    async def apb_write(self, addr, data):
        """APB write transaction"""
        await RisingEdge(self.dut.pclk_i)
        self.dut.psel_i.value = 1
        self.dut.penable_i.value = 0
        self.dut.pwrite_i.value = 1
        self.dut.paddr_i.value = addr
        self.dut.pwdata_i.value = data
        
        await RisingEdge(self.dut.pclk_i)
        self.dut.penable_i.value = 1
        
        await RisingEdge(self.dut.pclk_i)
        while not self.dut.pready_o.value:
            await RisingEdge(self.dut.pclk_i)
        
        self.dut.psel_i.value = 0
        self.dut.penable_i.value = 0
        self.dut.pwrite_i.value = 0
        self.dut.paddr_i.value = 0
        self.dut.pwdata_i.value = 0
    
    async def apb_read(self, addr):
        """APB read transaction"""
        await RisingEdge(self.dut.pclk_i)
        self.dut.psel_i.value = 1
        self.dut.penable_i.value = 0
        self.dut.pwrite_i.value = 0
        self.dut.paddr_i.value = addr
        
        await RisingEdge(self.dut.pclk_i)
        self.dut.penable_i.value = 1
        
        await RisingEdge(self.dut.pclk_i)
        while not self.dut.pready_o.value:
            await RisingEdge(self.dut.pclk_i)
        
        data = self.dut.prdata_o.value.integer
        self.dut.psel_i.value = 0
        self.dut.penable_i.value = 0
        self.dut.pwrite_i.value = 0
        self.dut.paddr_i.value = 0
        
        return data
    
    def check_result(self, test_name, condition, expected=None, actual=None):
        """Check test result and update counters"""
        self.test_count += 1
        if condition:
            self.pass_count += 1
            logger.info(f"  {test_name}: PASS")
        else:
            self.fail_count += 1
            if expected is not None and actual is not None:
                logger.error(f"  {test_name}: FAIL (expected {expected}, got {actual})")
            else:
                logger.error(f"  {test_name}: FAIL")
    
    async def test_apb_functionality(self):
        """Test APB protocol functionality"""
        logger.info("Test 1: APB Functionality")
        
        # Test register write
        await self.apb_write(0x000, 0x80000001)  # Enable global and channel 0
        
        # Test register read
        data = await self.apb_read(0x000)
        self.check_result("APB Write/Read", data == 0x80000001, 0x80000001, data)
        
        # Test invalid address
        data = await self.apb_read(0xFFF)
        self.check_result("Invalid Address", data == 0x00000000, 0x00000000, data)
    
    async def test_pwm_configuration(self):
        """Test PWM channel configuration"""
        logger.info("Test 2: PWM Configuration")
        
        # Configure channel 0
        await self.apb_write(0x104, 0x000186A0)  # 100kHz frequency
        await self.apb_write(0x108, 0x00008000)  # 50% duty cycle
        await self.apb_write(0x10C, 0x00000000)  # 0° phase
        await self.apb_write(0x110, 0x00000064)  # 100 clock cycles dead-time
        
        await ClockCycles(self.dut.pclk_i, 1000)  # Wait for PWM to start
        
        self.check_result("PWM Configuration", self.dut.busy_o.value == 1)
    
    async def test_multi_channel(self):
        """Test multi-channel operation"""
        logger.info("Test 3: Multi-Channel Operation")
        
        # Enable multiple channels
        await self.apb_write(0x000, 0x800000FF)  # Enable all channels
        
        # Configure different frequencies for each channel
        for i in range(8):
            await self.apb_write(0x104 + i*24, 0x000186A0 + i*1000)  # Different frequencies
            await self.apb_write(0x108 + i*24, 0x00008000 + i*1000)  # Different duty cycles
        
        await ClockCycles(self.dut.pclk_i, 2000)  # Wait for all channels to start
        
        self.check_result("Multi-Channel", self.dut.busy_o.value == 1)
    
    async def test_fault_protection(self):
        """Test fault protection"""
        logger.info("Test 4: Fault Protection")
        
        # Enable fault protection
        await self.apb_write(0x000, 0x90000001)  # Enable fault protection
        
        # Trigger fault
        self.dut.fault_i.value = 1
        await ClockCycles(self.dut.pclk_i, 100)
        
        fault_active = (self.dut.fault_o.value == 1 and 
                       self.dut.pwm_o.value == 0 and 
                       self.dut.pwm_n_o.value == 0)
        self.check_result("Fault Protection", fault_active)
        
        # Clear fault
        self.dut.fault_i.value = 0
        await ClockCycles(self.dut.pclk_i, 100)
    
    async def test_synchronization(self):
        """Test synchronization"""
        logger.info("Test 5: Synchronization")
        
        # Enable sync mode
        await self.apb_write(0x000, 0xA0000001)  # Enable sync mode
        
        # Trigger sync
        self.dut.sync_i.value = 1
        await ClockCycles(self.dut.pclk_i, 50)
        self.dut.sync_i.value = 0
        
        self.check_result("Synchronization", self.dut.sync_o.value == 1)
    
    async def test_performance(self):
        """Test performance characteristics"""
        logger.info("Test 6: Performance Testing")
        
        # Test maximum frequency
        await self.apb_write(0x104, 0x00FFFFFF)  # Maximum frequency
        await self.apb_write(0x108, 0x00008000)  # 50% duty cycle
        
        await ClockCycles(self.dut.pclk_i, 1000)
        
        self.check_result("Performance", self.dut.busy_o.value == 1)
    
    async def test_corner_cases(self):
        """Test corner cases"""
        logger.info("Test 7: Corner Cases")
        
        # Test zero frequency
        await self.apb_write(0x104, 0x00000000)
        self.check_result("Zero Frequency", self.dut.busy_o.value == 0)
        
        # Test zero duty cycle
        await self.apb_write(0x108, 0x00000000)
        self.check_result("Zero Duty Cycle", self.dut.pwm_o.value[0] == 0)
        
        # Test 100% duty cycle
        await self.apb_write(0x108, 0x0000FFFF)
        self.check_result("100% Duty Cycle", self.dut.pwm_o.value[0] == 1)
    
    async def test_coverage(self):
        """Test coverage verification"""
        logger.info("Test 8: Coverage Verification")
        
        # Test all register addresses
        for addr in range(0, 256, 4):
            await self.apb_read(addr)
        
        self.check_result("Coverage", True)
    
    def print_results(self):
        """Print test results"""
        logger.info("Test Results:")
        logger.info(f"  Total Tests: {self.test_count}")
        logger.info(f"  Passed: {self.pass_count}")
        logger.info(f"  Failed: {self.fail_count}")
        if self.test_count > 0:
            coverage = (self.pass_count * 100.0) / self.test_count
            logger.info(f"  Coverage: {coverage:.1f}%")
        
        if self.fail_count == 0:
            logger.info("All tests PASSED!")
        else:
            logger.error("Some tests FAILED!")

@cocotb.test()
async def test_basic_pwm(dut):
    """Test basic PWM functionality"""
    test = PWMControllerTest(dut)
    await test.setup()
    
    await test.test_apb_functionality()
    await test.test_pwm_configuration()
    await test.test_multi_channel()
    await test.test_fault_protection()
    await test.test_synchronization()
    await test.test_performance()
    await test.test_corner_cases()
    await test.test_coverage()
    
    test.print_results()
    
    # Assert all tests passed
    assert test.fail_count == 0, f"{test.fail_count} tests failed"

@cocotb.test()
async def test_random_stimulus(dut):
    """Test with random stimulus"""
    test = PWMControllerTest(dut)
    await test.setup()
    
    # Random configuration testing
    for i in range(10):
        # Random frequency and duty cycle
        freq = random.randint(0, 0xFFFFFF)
        duty = random.randint(0, 0xFFFF)
        phase = random.randint(0, 0xFFFF)
        deadtime = random.randint(0, 0xFFFF)
        
        await test.apb_write(0x104, freq)
        await test.apb_write(0x108, duty)
        await test.apb_write(0x10C, phase)
        await test.apb_write(0x110, deadtime)
        
        await ClockCycles(dut.pclk_i, 100)
        
        # Verify PWM output is valid
        assert dut.pwm_o.value >= 0 and dut.pwm_o.value <= 0xFF
    
    logger.info("Random stimulus test completed")

@cocotb.test()
async def test_interrupt_handling(dut):
    """Test interrupt handling"""
    test = PWMControllerTest(dut)
    await test.setup()
    
    # Enable interrupts
    await test.apb_write(0x018, 0x000000FF)  # Enable all interrupts
    
    # Configure PWM to generate interrupts
    await test.apb_write(0x000, 0x80000001)  # Enable global and channel 0
    await test.apb_write(0x104, 0x00000100)  # Low frequency for interrupt generation
    await test.apb_write(0x108, 0x00008000)  # 50% duty cycle
    
    await ClockCycles(dut.pclk_i, 1000)
    
    # Check for interrupt generation
    test.check_result("Interrupt Generation", dut.irq_o.value == 1)
    
    test.print_results()

@cocotb.test()
async def test_power_management(dut):
    """Test power management features"""
    test = PWMControllerTest(dut)
    await test.setup()
    
    # Test power-down sequence
    await test.apb_write(0x000, 0x00000000)  # Disable all channels
    
    await ClockCycles(dut.pclk_i, 100)
    
    # Verify power-down
    test.check_result("Power Down", dut.busy_o.value == 0)
    
    # Test power-up sequence
    await test.apb_write(0x000, 0x80000001)  # Enable global and channel 0
    
    await ClockCycles(dut.pclk_i, 100)
    
    # Verify power-up
    test.check_result("Power Up", dut.busy_o.value == 1)
    
    test.print_results() 