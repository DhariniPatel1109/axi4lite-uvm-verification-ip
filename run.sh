#!/bin/bash
################################################################################
# Quick run script for AXI4-Lite UVM Verification
################################################################################

# Default values
TEST="axi4lite_sanity_test"
SIM="questa"
WAVES=0

# Parse arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        -t|--test)
            TEST="$2"
            shift 2
            ;;
        -s|--sim)
            SIM="$2"
            shift 2
            ;;
        -w|--waves)
            WAVES=1
            shift
            ;;
        -h|--help)
            echo "Usage: ./run.sh [options]"
            echo ""
            echo "Options:"
            echo "  -t, --test <name>   Test name (default: axi4lite_sanity_test)"
            echo "  -s, --sim <tool>    Simulator (questa, vcs, xcelium)"
            echo "  -w, --waves         Enable waveform dumping"
            echo "  -h, --help          Show this help"
            echo ""
            echo "Examples:"
            echo "  ./run.sh -t axi4lite_random_test -w"
            echo "  ./run.sh --test axi4lite_stress_test --sim vcs"
            exit 0
            ;;
        *)
            echo "Unknown option: $1"
            exit 1
            ;;
    esac
done

# Run simulation
echo "Running test: $TEST"
echo "Simulator: $SIM"
echo "Waves: $WAVES"

make sim_${SIM} TEST=${TEST} WAVES=${WAVES}

