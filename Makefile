################################################################################
# AXI4-Lite UVM Verification Makefile
# Supports: Questa/ModelSim, VCS, Xcelium, and Verilator
################################################################################

# Default simulator
SIM ?= questa

# Default test
TEST ?= axi4lite_sanity_test

# Verbosity
VERBOSITY ?= UVM_MEDIUM

# Seed
SEED ?= random

# Waveform dump
WAVES ?= 0

################################################################################
# Directory Structure
################################################################################

RTL_DIR     = rtl
TB_DIR      = tb
UVM_DIR     = $(TB_DIR)/uvm
IF_DIR      = $(TB_DIR)/interfaces
SIM_DIR     = sim
RESULTS_DIR = results

# Create directories
$(shell mkdir -p $(SIM_DIR) $(RESULTS_DIR))

################################################################################
# File Lists
################################################################################

RTL_FILES = \
	$(RTL_DIR)/axi4_lite_slave.sv

TB_FILES = \
	$(IF_DIR)/axi4lite_if.sv \
	$(TB_DIR)/axi4lite_tb_top.sv

UVM_PKG = $(UVM_DIR)/axi4lite_pkg.sv

ALL_FILES = $(RTL_FILES) $(TB_FILES)

################################################################################
# Questa/ModelSim Settings
################################################################################

QUESTA_VLOG_OPTS = -sv \
	-timescale 1ns/1ps \
	+incdir+$(UVM_DIR) \
	+incdir+$(UVM_DIR)/agents/axi4lite_agent \
	+incdir+$(UVM_DIR)/env \
	+incdir+$(UVM_DIR)/sequences \
	+incdir+$(UVM_DIR)/tests \
	-suppress 2577 \
	-suppress 7061

QUESTA_VSIM_OPTS = -sv_seed=$(SEED) \
	-voptargs="+acc" \
	+UVM_TESTNAME=$(TEST) \
	+UVM_VERBOSITY=$(VERBOSITY) \
	-do "run -all; quit -f"

ifeq ($(WAVES),1)
	QUESTA_VSIM_OPTS += +DUMP_VCD
endif

################################################################################
# VCS Settings
################################################################################

VCS_OPTS = -sverilog \
	-timescale=1ns/1ps \
	-full64 \
	-lca \
	-debug_access+all \
	+incdir+$(UVM_DIR) \
	+incdir+$(UVM_DIR)/agents/axi4lite_agent \
	+incdir+$(UVM_DIR)/env \
	+incdir+$(UVM_DIR)/sequences \
	+incdir+$(UVM_DIR)/tests \
	-ntb_opts uvm-1.2

VCS_RUN_OPTS = +UVM_TESTNAME=$(TEST) \
	+UVM_VERBOSITY=$(VERBOSITY) \
	+ntb_random_seed=$(SEED)

ifeq ($(WAVES),1)
	VCS_OPTS += -debug_access+all
	VCS_RUN_OPTS += +DUMP_VCD
endif

################################################################################
# Xcelium Settings
################################################################################

XCELIUM_OPTS = -sv \
	-timescale 1ns/1ps \
	-uvm \
	-uvmhome CDNS-1.2 \
	+incdir+$(UVM_DIR) \
	+incdir+$(UVM_DIR)/agents/axi4lite_agent \
	+incdir+$(UVM_DIR)/env \
	+incdir+$(UVM_DIR)/sequences \
	+incdir+$(UVM_DIR)/tests \
	-access +rwc

XCELIUM_RUN_OPTS = +UVM_TESTNAME=$(TEST) \
	+UVM_VERBOSITY=$(VERBOSITY) \
	-svseed $(SEED)

ifeq ($(WAVES),1)
	XCELIUM_RUN_OPTS += +DUMP_VCD
endif

################################################################################
# Targets
################################################################################

.PHONY: all clean help run compile sim_questa sim_vcs sim_xcelium

all: help

help:
	@echo "========================================================================"
	@echo "  AXI4-Lite UVM Verification Makefile"
	@echo "========================================================================"
	@echo ""
	@echo "Usage: make <target> [options]"
	@echo ""
	@echo "Targets:"
	@echo "  sim_questa    - Run simulation with Questa/ModelSim (default)"
	@echo "  sim_vcs       - Run simulation with Synopsys VCS"
	@echo "  sim_xcelium   - Run simulation with Cadence Xcelium"
	@echo "  clean         - Clean all generated files"
	@echo "  help          - Show this help message"
	@echo ""
	@echo "Options:"
	@echo "  TEST=<test_name>          - Test to run (default: axi4lite_sanity_test)"
	@echo "  VERBOSITY=<level>         - UVM verbosity (default: UVM_MEDIUM)"
	@echo "  SEED=<value>              - Random seed (default: random)"
	@echo "  WAVES=1                   - Enable waveform dump"
	@echo ""
	@echo "Available Tests:"
	@echo "  axi4lite_sanity_test      - Basic sanity check"
	@echo "  axi4lite_directed_test    - Directed register test"
	@echo "  axi4lite_random_test      - Constrained random test"
	@echo "  axi4lite_stress_test      - High-intensity stress test"
	@echo ""
	@echo "Examples:"
	@echo "  make sim_questa TEST=axi4lite_random_test WAVES=1"
	@echo "  make sim_vcs TEST=axi4lite_stress_test SEED=12345"
	@echo "========================================================================"

################################################################################
# Questa/ModelSim
################################################################################

sim_questa: clean
	@echo "========================================================================"
	@echo "  Running simulation with Questa/ModelSim"
	@echo "  Test: $(TEST)"
	@echo "  Seed: $(SEED)"
	@echo "========================================================================"
	cd $(SIM_DIR) && vlib work
	cd $(SIM_DIR) && vlog $(QUESTA_VLOG_OPTS) $(addprefix ../,$(UVM_PKG)) $(addprefix ../,$(ALL_FILES))
	cd $(SIM_DIR) && vsim $(QUESTA_VSIM_OPTS) work.axi4lite_tb_top -l ../$(RESULTS_DIR)/$(TEST)_$(SEED).log
	@echo "Simulation complete. Log: $(RESULTS_DIR)/$(TEST)_$(SEED).log"

################################################################################
# Synopsys VCS
################################################################################

sim_vcs: clean
	@echo "========================================================================"
	@echo "  Running simulation with Synopsys VCS"
	@echo "  Test: $(TEST)"
	@echo "  Seed: $(SEED)"
	@echo "========================================================================"
	cd $(SIM_DIR) && vcs $(VCS_OPTS) $(addprefix ../,$(UVM_PKG)) $(addprefix ../,$(ALL_FILES)) -o simv
	cd $(SIM_DIR) && ./simv $(VCS_RUN_OPTS) -l ../$(RESULTS_DIR)/$(TEST)_$(SEED).log
	@echo "Simulation complete. Log: $(RESULTS_DIR)/$(TEST)_$(SEED).log"

################################################################################
# Cadence Xcelium
################################################################################

sim_xcelium: clean
	@echo "========================================================================"
	@echo "  Running simulation with Cadence Xcelium"
	@echo "  Test: $(TEST)"
	@echo "  Seed: $(SEED)"
	@echo "========================================================================"
	cd $(SIM_DIR) && xrun $(XCELIUM_OPTS) $(addprefix ../,$(UVM_PKG)) $(addprefix ../,$(ALL_FILES)) \
		$(XCELIUM_RUN_OPTS) -l ../$(RESULTS_DIR)/$(TEST)_$(SEED).log
	@echo "Simulation complete. Log: $(RESULTS_DIR)/$(TEST)_$(SEED).log"

################################################################################
# Default simulation (Questa)
################################################################################

run: sim_questa

sim: sim_questa

################################################################################
# Regression - Run all tests
################################################################################

regression:
	@echo "Running regression with all tests..."
	@$(MAKE) sim_questa TEST=axi4lite_sanity_test SEED=1
	@$(MAKE) sim_questa TEST=axi4lite_directed_test SEED=2
	@$(MAKE) sim_questa TEST=axi4lite_random_test SEED=3
	@$(MAKE) sim_questa TEST=axi4lite_stress_test SEED=4
	@echo "Regression complete!"

################################################################################
# Clean
################################################################################

clean:
	@echo "Cleaning simulation files..."
	rm -rf $(SIM_DIR)/*
	rm -rf work
	rm -rf transcript
	rm -rf vsim.wlf
	rm -rf *.vcd
	rm -rf *.fst
	rm -rf simv*
	rm -rf csrc
	rm -rf ucli.key
	rm -rf vc_hdrs.h
	rm -rf DVEfiles
	rm -rf *.log
	rm -rf xcelium.d
	rm -rf INCA_libs
	rm -rf .simvision
	@echo "Clean complete."

################################################################################
# Coverage merge (if needed)
################################################################################

cov_merge:
	@echo "Merging coverage from multiple runs..."
	# Add coverage merge commands based on your simulator

################################################################################
# View waveforms
################################################################################

waves:
	@if [ -f "axi4lite_tb.vcd" ]; then \
		gtkwave axi4lite_tb.vcd; \
	elif [ -f "$(SIM_DIR)/axi4lite_tb.vcd" ]; then \
		gtkwave $(SIM_DIR)/axi4lite_tb.vcd; \
	else \
		echo "No waveform file found. Run with WAVES=1"; \
	fi

