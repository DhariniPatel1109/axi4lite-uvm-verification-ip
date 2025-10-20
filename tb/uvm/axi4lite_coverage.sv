////////////////////////////////////////////////////////////////////////////////
// AXI4-Lite Functional Coverage Collector
// Collects functional coverage for addresses, data patterns, transaction types,
// responses, and corner cases
////////////////////////////////////////////////////////////////////////////////

class axi4lite_coverage extends uvm_subscriber #(axi4lite_txn);
   
   `uvm_component_utils(axi4lite_coverage)
   
   // Local copy of transaction for coverage sampling
   axi4lite_txn txn;
   
   // Coverage tracking variables
   int num_read_txns;
   int num_write_txns;
   
   //============================================================================
   // Coverage Groups
   //============================================================================
   
   // Main transaction coverage
   covergroup cg_axi4lite_transactions;
      option.per_instance = 1;
      option.name = "cg_axi4lite_transactions";
      
      // Transaction type coverage
      cp_txn_type: coverpoint txn.txn_type {
         bins read  = {READ};
         bins write = {WRITE};
      }
      
      // Address coverage - bin each register
      cp_address: coverpoint txn.addr {
         bins reg_0_3   = {[0:3*4]};
         bins reg_4_7   = {[4*4:7*4]};
         bins reg_8_15  = {[8*4:15*4]};
         bins reg_16_23 = {[16*4:23*4]};
         bins reg_24_31 = {[24*4:31*4]};
         bins first_reg = {0};
         bins last_reg  = {31*4};
      }
      
      // Data patterns coverage
      cp_data_patterns: coverpoint txn.data {
         bins all_zeros  = {32'h00000000};
         bins all_ones   = {32'hFFFFFFFF};
         bins small_val  = {[32'h00000001:32'h000000FF]};
         bins large_val  = {[32'hFFFFFF00:32'hFFFFFFFE]};
         bins mid_range  = {[32'h00000100:32'hFFFFFF00]};
         bins alternating = {32'hAAAAAAAA, 32'h55555555};
      }
      
      // Response coverage
      cp_response: coverpoint txn.resp {
         bins okay   = {2'b00};
         bins exokay = {2'b01};
         bins slverr = {2'b10};
         bins decerr = {2'b11};
      }
      
      // Write strobe patterns
      cp_write_strobe: coverpoint txn.strb iff (txn.txn_type == WRITE) {
         bins all_lanes   = {4'b1111};
         bins byte_0      = {4'b0001};
         bins byte_1      = {4'b0010};
         bins byte_2      = {4'b0100};
         bins byte_3      = {4'b1000};
         bins half_low    = {4'b0011};
         bins half_high   = {4'b1100};
         bins non_contiguous = {4'b0101, 4'b1010};
      }
      
      // Inter-transaction delay coverage
      cp_delay: coverpoint txn.delay_cycles {
         bins no_delay      = {0};
         bins small_delay   = {[1:2]};
         bins medium_delay  = {[3:4]};
         bins large_delay   = {5};
      }
      
      // Cross coverage: transaction type x address
      cross_txn_addr: cross cp_txn_type, cp_address;
      
      // Cross coverage: transaction type x data patterns
      cross_txn_data: cross cp_txn_type, cp_data_patterns {
         // Only writes affect memory, so reads can have any data
         ignore_bins read_data = binsof(cp_txn_type) intersect {READ};
      }
      
      // Cross coverage: write strobe x address alignment
      cross_strb_addr: cross cp_write_strobe, cp_address;
      
   endgroup : cg_axi4lite_transactions
   
   //============================================================================
   // Corner Cases Coverage
   //============================================================================
   
   covergroup cg_corner_cases;
      option.per_instance = 1;
      option.name = "cg_corner_cases";
      
      // Back-to-back transactions
      cp_back_to_back: coverpoint txn.delay_cycles {
         bins b2b = {0};
      }
      
      // Consecutive reads/writes to same address
      cp_same_addr: coverpoint (txn.addr) {
         bins addr_repeated = (32'h0 => 32'h0), (32'h4 => 32'h4);
      }
      
   endgroup : cg_corner_cases
   
   //============================================================================
   // Protocol Coverage
   //============================================================================
   
   covergroup cg_protocol;
      option.per_instance = 1;
      option.name = "cg_protocol";
      
      // Protection type coverage
      cp_prot: coverpoint txn.prot {
         bins unprivileged_secure_data      = {3'b000};
         bins unprivileged_secure_instr     = {3'b001};
         bins unprivileged_nonsecure_data   = {3'b010};
         bins unprivileged_nonsecure_instr  = {3'b011};
         bins privileged_secure_data        = {3'b100};
         bins privileged_secure_instr       = {3'b101};
         bins privileged_nonsecure_data     = {3'b110};
         bins privileged_nonsecure_instr    = {3'b111};
      }
      
   endgroup : cg_protocol
   
   //============================================================================
   // Read-After-Write Coverage
   //============================================================================
   
   // Variables to track consecutive transactions
   axi4lite_txn prev_txn;
   bit          prev_txn_valid;
   
   covergroup cg_raw_scenarios;
      option.per_instance = 1;
      option.name = "cg_raw_scenarios";
      
      // Detect read-after-write to same address
      cp_raw: coverpoint (prev_txn_valid && 
                         prev_txn.txn_type == WRITE && 
                         txn.txn_type == READ &&
                         prev_txn.addr == txn.addr) {
         bins raw_occurred = {1};
         bins no_raw       = {0};
      }
      
   endgroup : cg_raw_scenarios
   
   //============================================================================
   // Constructor & Methods
   //============================================================================
   
   function new(string name, uvm_component parent);
      super.new(name, parent);
      cg_axi4lite_transactions = new();
      cg_corner_cases = new();
      cg_protocol = new();
      cg_raw_scenarios = new();
      num_read_txns = 0;
      num_write_txns = 0;
      prev_txn_valid = 0;
   endfunction
   
   //============================================================================
   // Write method - called by analysis port
   //============================================================================
   
   virtual function void write(axi4lite_txn t);
      $cast(txn, t.clone());
      
      // Sample all coverage groups
      cg_axi4lite_transactions.sample();
      cg_corner_cases.sample();
      cg_protocol.sample();
      cg_raw_scenarios.sample();
      
      // Update statistics
      if (txn.txn_type == READ)
         num_read_txns++;
      else
         num_write_txns++;
      
      // Save for RAW detection
      if (prev_txn == null)
         prev_txn = new("prev_txn");
      $cast(prev_txn, txn.clone());
      prev_txn_valid = 1;
      
      `uvm_info(get_type_name(), 
               $sformatf("Sampled coverage for: %s", txn.convert2string()),
               UVM_HIGH)
   endfunction
   
   //============================================================================
   // Report Phase
   //============================================================================
   
   virtual function void report_phase(uvm_phase phase);
      real txn_cov, corner_cov, protocol_cov, raw_cov, total_cov;
      
      super.report_phase(phase);
      
      // Get coverage percentages
      txn_cov = cg_axi4lite_transactions.get_coverage();
      corner_cov = cg_corner_cases.get_coverage();
      protocol_cov = cg_protocol.get_coverage();
      raw_cov = cg_raw_scenarios.get_coverage();
      total_cov = (txn_cov + corner_cov + protocol_cov + raw_cov) / 4.0;
      
      `uvm_info(get_type_name(), "============================================", UVM_NONE)
      `uvm_info(get_type_name(), "      COVERAGE REPORT", UVM_NONE)
      `uvm_info(get_type_name(), "============================================", UVM_NONE)
      `uvm_info(get_type_name(), $sformatf("Total Reads:         %0d", num_read_txns), UVM_NONE)
      `uvm_info(get_type_name(), $sformatf("Total Writes:        %0d", num_write_txns), UVM_NONE)
      `uvm_info(get_type_name(), $sformatf("Total Transactions:  %0d", num_read_txns + num_write_txns), UVM_NONE)
      `uvm_info(get_type_name(), "--------------------------------------------", UVM_NONE)
      `uvm_info(get_type_name(), $sformatf("Transaction Coverage: %0.2f%%", txn_cov), UVM_NONE)
      `uvm_info(get_type_name(), $sformatf("Corner Case Coverage: %0.2f%%", corner_cov), UVM_NONE)
      `uvm_info(get_type_name(), $sformatf("Protocol Coverage:    %0.2f%%", protocol_cov), UVM_NONE)
      `uvm_info(get_type_name(), $sformatf("RAW Coverage:         %0.2f%%", raw_cov), UVM_NONE)
      `uvm_info(get_type_name(), "--------------------------------------------", UVM_NONE)
      `uvm_info(get_type_name(), $sformatf("OVERALL COVERAGE:     %0.2f%%", total_cov), UVM_NONE)
      `uvm_info(get_type_name(), "============================================", UVM_NONE)
      
      if (total_cov >= 95.0)
         `uvm_info(get_type_name(), "*** COVERAGE GOAL ACHIEVED ***", UVM_NONE)
      else
         `uvm_warning(get_type_name(), 
                     $sformatf("Coverage goal not met. Need %0.2f%% more.", 95.0 - total_cov))
   endfunction

endclass : axi4lite_coverage

