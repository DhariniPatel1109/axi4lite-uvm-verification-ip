////////////////////////////////////////////////////////////////////////////////
// AXI4-Lite UVM Package
// Includes all UVM components, sequences, and tests
////////////////////////////////////////////////////////////////////////////////

package axi4lite_pkg;
   
   import uvm_pkg::*;
   
   `include "uvm_macros.svh"
   
   // Transaction
   `include "axi4lite_txn.sv"
   
   // Scoreboard
   `include "axi4lite_scoreboard.sv"
   
   // Coverage
   `include "axi4lite_coverage.sv"
   
   // Agent components
   `include "agents/axi4lite_agent/axi4lite_driver.sv"
   `include "agents/axi4lite_agent/axi4lite_monitor.sv"
   `include "agents/axi4lite_agent/axi4lite_sequencer.sv"
   `include "agents/axi4lite_agent/axi4lite_agent.sv"
   
   // Environment
   `include "env/axi4lite_env.sv"
   
   // Sequences
   `include "sequences/axi4lite_seq_lib.sv"
   
   // Tests
   `include "tests/axi4lite_base_test.sv"
   `include "tests/axi4lite_sanity_test.sv"
   `include "tests/axi4lite_directed_test.sv"
   `include "tests/axi4lite_random_test.sv"
   `include "tests/axi4lite_stress_test.sv"

endpackage : axi4lite_pkg

