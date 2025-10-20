# Getting Started with AXI4-Lite Verification Environment

**Masters Project Tutorial**

This guide provides step-by-step instructions for setting up and running the AXI4-Lite UVM verification environment.

---

## Table of Contents

1. [Prerequisites](#prerequisites)
2. [Environment Setup](#environment-setup)
3. [Running Your First Test](#running-your-first-test)
4. [Understanding the Output](#understanding-the-output)
5. [Running Different Tests](#running-different-tests)
6. [Viewing Waveforms](#viewing-waveforms)
7. [Debugging](#debugging)
8. [Next Steps](#next-steps)

---

## Prerequisites

### Required Tools

**Simulator** (one of the following):
- Mentor Graphics Questa/ModelSim 10.6c or later
- Synopsys VCS 2019.06 or later
- Cadence Xcelium 19.09 or later

**Build Tools**:
- GNU Make 4.0+
- Bash shell

**Optional**:
- GTKWave for waveform viewing
- Text editor with SystemVerilog support (VS Code, Vim, Emacs)

### Verify Installation

Check that you have access to a simulator:

```bash
# For Questa/ModelSim
which vsim

# For VCS
which vcs

# For Xcelium
which xrun
```

---

## Environment Setup

### Step 1: Clone the Repository

```bash
git clone https://github.com/DhariniPatel1109/axi4lite-uvm-verification-ip.git
cd axi4lite-uvm-verification-ip
```

### Step 2: Explore the Directory Structure

```bash
# View the project structure
ls -R

# Key directories:
# rtl/     - Design Under Test
# tb/      - Testbench files
# docs/    - Documentation
# sim/     - Simulation workspace (created automatically)
# results/ - Test results (created automatically)
```

### Step 3: Check Makefile Configuration

Open `Makefile` and verify the simulator paths match your installation.

---

## Running Your First Test

### Method 1: Using the Run Script

The simplest way to run a test:

```bash
./run.sh -t axi4lite_sanity_test
```

This script:
1. Navigates to the project directory
2. Compiles all source files
3. Runs the specified test
4. Saves results to the `results/` directory

### Method 2: Using Make Directly

For more control:

```bash
make sim_questa TEST=axi4lite_sanity_test
```

### What Happens During Compilation

1. The Makefile compiles the DUT (`rtl/axi4_lite_slave.sv`)
2. Compiles the UVM package and all testbench files
3. Creates a simulation executable
4. Runs the test
5. Generates a log file

**Expected Duration**: 30-60 seconds for sanity test

---

## Understanding the Output

### Successful Test Output

When a test passes, you should see output similar to:

```
UVM_INFO @ 0: reporter [RNTST] Running test axi4lite_sanity_test...

=== SANITY TEST STARTED ===

UVM_INFO @ 150: uvm_test_top.env.agent.drv [axi4lite_driver] 
   Driving transaction: TXN: WRITE | ADDR=0x00000000 | DATA=0x12345678

UVM_INFO @ 250: uvm_test_top.env.scb [axi4lite_scoreboard]
   WRITE CHECK PASSED: addr=0x00000000, data=0x12345678

========================================
      SCOREBOARD FINAL REPORT
========================================
Total Writes:       10
Total Reads:        10
Total Transactions: 20
Passed Checks:      20
Failed Checks:      0
*** ALL CHECKS PASSED ***

========================================
      COVERAGE REPORT
========================================
Transaction Coverage: 85.50%
Corner Case Coverage: 80.00%
Protocol Coverage:    100.00%
--------------------------------------------
OVERALL COVERAGE:     88.50%

========================================
        TEST SUMMARY
========================================
*** TEST PASSED ***
```

### Key Sections to Look For

1. **Test Start**: Confirms which test is running
2. **Transaction Info**: Shows each transaction being driven/monitored
3. **Scoreboard Report**: Statistics on checks performed
4. **Coverage Report**: Functional coverage metrics
5. **Test Result**: Final PASS/FAIL status

### Log File Location

Results are saved in:
```
results/axi4lite_sanity_test_<seed>.log
```

---

## Running Different Tests

### Available Test Cases

```bash
# 1. Sanity Test - Quick verification (recommended first test)
make sim_questa TEST=axi4lite_sanity_test

# 2. Directed Test - Systematic testing of all registers
make sim_questa TEST=axi4lite_directed_test

# 3. Random Test - Constrained-random transactions
make sim_questa TEST=axi4lite_random_test

# 4. Stress Test - High-intensity testing
make sim_questa TEST=axi4lite_stress_test
```

### Test Characteristics

| Test | Transactions | Duration | Purpose |
|------|--------------|----------|---------|
| Sanity | ~10 | 30 sec | Quick smoke test |
| Directed | 64 | 1 min | All registers systematically |
| Random | 50-250 | 2-3 min | Coverage building |
| Stress | 500+ | 5-10 min | Performance testing |

### Running All Tests (Regression)

To run all tests automatically:

```bash
make regression
```

This runs each test with a different random seed and saves all results.

---

## Viewing Waveforms

Waveforms help debug issues by showing signal-level timing.

### Enabling Waveform Dump

```bash
# Method 1: Using run script
./run.sh -t axi4lite_random_test -w

# Method 2: Using make
make sim_questa TEST=axi4lite_random_test WAVES=1
```

This generates `axi4lite_tb.vcd` in the sim directory.

### Opening Waveforms

```bash
# If GTKWave is installed
make waves

# Or manually
gtkwave sim/axi4lite_tb.vcd
```

### Important Signals to View

**Clock and Reset**:
- `clk`
- `rst_n`

**Write Channels**:
- `vif.AWADDR`, `vif.AWVALID`, `vif.AWREADY` (Write Address)
- `vif.WDATA`, `vif.WVALID`, `vif.WREADY` (Write Data)
- `vif.BRESP`, `vif.BVALID`, `vif.BREADY` (Write Response)

**Read Channels**:
- `vif.ARADDR`, `vif.ARVALID`, `vif.ARREADY` (Read Address)
- `vif.RDATA`, `vif.RRESP`, `vif.RVALID`, `vif.RREADY` (Read Data)

---

## Debugging

### Common Issues and Solutions

#### Issue 1: Compilation Errors

**Symptom**: Errors during vlog/vcs compilation

**Solution**:
```bash
# Check file paths in Makefile
# Ensure UVM library is accessible
# Verify SystemVerilog syntax
```

#### Issue 2: Test Fails with Scoreboard Mismatch

**Symptom**:
```
UVM_ERROR: DATA MISMATCH: addr=0x00000008 | Expected=0x12345678 | Got=0xDEADBEEF
```

**Debugging Steps**:
1. Re-run with waveforms enabled
2. Find the address in question
3. Check the write transaction
4. Verify no intermediate writes
5. Check read transaction timing

#### Issue 3: Assertion Failure

**Symptom**:
```
[ASSERTION FAILED] AWVALID/AWADDR must remain stable until handshake completes
```

**Debugging Steps**:
1. Enable waveforms
2. Find the time of assertion failure
3. Zoom into the signal transitions
4. Check if AWVALID drops before AWREADY asserts

#### Issue 4: Simulation Hangs

**Symptom**: Simulation doesn't complete

**Possible Causes**:
- DUT not responding to transactions
- Reset signal stuck
- Infinite loop in driver/monitor

**Solution**:
```bash
# Kill simulation: Ctrl+C
# Check waveforms for the last activity
# Add timeout: already included in testbench (10ms)
```

### Increasing Debug Verbosity

For more detailed output:

```bash
make sim_questa TEST=axi4lite_random_test VERBOSITY=UVM_HIGH
```

Verbosity levels:
- `UVM_LOW` - Minimal output
- `UVM_MEDIUM` - Standard output (default)
- `UVM_HIGH` - Detailed transaction info
- `UVM_DEBUG` - Everything

---

## Advanced Usage

### Running with Specific Seed

For reproducing specific test runs:

```bash
make sim_questa TEST=axi4lite_random_test SEED=12345
```

### Cleaning Simulation Files

```bash
make clean
```

This removes:
- Compiled libraries
- Simulation databases
- Waveform files
- Log files

### Using Different Simulators

```bash
# VCS
make sim_vcs TEST=axi4lite_sanity_test

# Xcelium
make sim_xcelium TEST=axi4lite_sanity_test
```

---

## Next Steps

### For Learning the Code

1. **Start with the transaction**:
   - Read `tb/uvm/axi4lite_txn.sv`
   - Understand the transaction format and constraints

2. **Study the driver**:
   - Read `tb/uvm/agents/axi4lite_agent/axi4lite_driver.sv`
   - See how transactions are driven onto the bus

3. **Examine the scoreboard**:
   - Read `tb/uvm/axi4lite_scoreboard.sv`
   - Understand the checking mechanism

4. **Review assertions**:
   - Read `tb/interfaces/axi4lite_if.sv`
   - See protocol checking implementation

### For Extending the Testbench

1. Create new sequences in `tb/uvm/sequences/axi4lite_seq_lib.sv`
2. Add new test cases in `tb/uvm/tests/`
3. Enhance coverage in `tb/uvm/axi4lite_coverage.sv`
4. Add new assertions in the interface

### For Understanding UVM

Refer to the UVM documentation:
- UVM 1.2 User Guide (Accellera)
- UVM Cookbook (Verification Academy)
- SystemVerilog for Verification (Chris Spear)

---

## Troubleshooting Reference

| Problem | Check | Solution |
|---------|-------|----------|
| Won't compile | File paths | Verify Makefile paths |
| Missing UVM | UVM library | Check simulator UVM installation |
| Test fails | Log file | Check for errors/warnings |
| No waveform | WAVES flag | Add WAVES=1 to command |
| Simulation hangs | Timeout | Wait for 10ms timeout or Ctrl+C |

---

## Summary Checklist

- [ ] Simulator installed and accessible
- [ ] Repository cloned
- [ ] First test run successfully
- [ ] Log file reviewed
- [ ] Waveforms viewed
- [ ] All four tests executed
- [ ] Regression run completed
- [ ] Code structure understood
- [ ] Ready to modify/extend

---

**For additional help, refer to**:
- **ARCHITECTURE.md** - Detailed design documentation
- **README.md** - Project overview
- Inline code comments in source files

---

*Tutorial for Masters Project in Digital Verification*  
*Last Updated: October 2025*
