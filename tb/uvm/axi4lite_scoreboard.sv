////////////////////////////////////////////////////////////////////////////////
// AXI4-Lite Scoreboard with Reference Memory Model
// This scoreboard implements a golden reference model and checks all
// transactions for data integrity
////////////////////////////////////////////////////////////////////////////////

class axi4lite_scoreboard extends uvm_scoreboard;
   
   `uvm_component_utils(axi4lite_scoreboard)
   
   // Analysis port for receiving transactions from monitor
   uvm_analysis_imp #(axi4lite_txn, axi4lite_scoreboard) item_collected_export;
   
   // Reference memory model (32 registers of 32-bit data)
   protected bit [31:0] ref_memory [bit[31:0]];
   protected int num_writes;
   protected int num_reads;
   protected int num_mismatches;
   protected int num_passed;
   
   // Queue to track write transactions for read-after-write checking
   protected axi4lite_txn write_history[$];
   
   //============================================================================
   // Constructor & Build Phase
   //============================================================================
   
   function new(string name, uvm_component parent);
      super.new(name, parent);
      num_writes = 0;
      num_reads = 0;
      num_mismatches = 0;
      num_passed = 0;
   endfunction
   
   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      item_collected_export = new("item_collected_export", this);
   endfunction
   
   //============================================================================
   // Analysis Port Write Method - Called when monitor sends a transaction
   //============================================================================
   
   virtual function void write(axi4lite_txn txn);
      axi4lite_txn txn_clone;
      
      // Clone the transaction for processing
      $cast(txn_clone, txn.clone());
      
      // Process based on transaction type
      case (txn_clone.txn_type)
         WRITE: process_write(txn_clone);
         READ:  process_read(txn_clone);
         default: `uvm_error(get_type_name(), "Unknown transaction type")
      endcase
   endfunction
   
   //============================================================================
   // Process Write Transaction
   //============================================================================
   
   virtual function void process_write(axi4lite_txn txn);
      bit [31:0] addr;
      addr = txn.addr;
      
      num_writes++;
      
      // Update reference memory
      ref_memory[addr] = txn.data;
      
      // Add to write history for future comparison
      write_history.push_back(txn);
      
      // Check write response
      if (txn.resp != 2'b00) begin  // OKAY response
         `uvm_error(get_type_name(), 
                    $sformatf("Write transaction got non-OKAY response: %s at addr=0x%08h",
                             txn.resp_to_string(txn.resp), addr))
         num_mismatches++;
      end else begin
         num_passed++;
         `uvm_info(get_type_name(),
                   $sformatf("WRITE CHECK PASSED: addr=0x%08h, data=0x%08h", addr, txn.data),
                   UVM_HIGH)
      end
   endfunction
   
   //============================================================================
   // Process Read Transaction
   //============================================================================
   
   virtual function void process_read(axi4lite_txn txn);
      bit [31:0] addr;
      bit [31:0] expected_data;
      
      addr = txn.addr;
      num_reads++;
      
      // Check if address was ever written
      if (!ref_memory.exists(addr)) begin
         // Address never written, expect default value (0)
         expected_data = 32'h00000000;
         `uvm_info(get_type_name(),
                   $sformatf("Reading unwritten address 0x%08h, expecting default value", addr),
                   UVM_MEDIUM)
      end else begin
         // Get expected data from reference memory
         expected_data = ref_memory[addr];
      end
      
      // Compare actual vs expected
      if (txn.data !== expected_data) begin
         `uvm_error(get_type_name(),
                    $sformatf("DATA MISMATCH: addr=0x%08h | Expected=0x%08h | Got=0x%08h",
                             addr, expected_data, txn.data))
         num_mismatches++;
      end else begin
         num_passed++;
         `uvm_info(get_type_name(),
                   $sformatf("READ CHECK PASSED: addr=0x%08h, data=0x%08h", addr, txn.data),
                   UVM_HIGH)
      end
      
      // Check read response
      if (txn.resp != 2'b00) begin  // OKAY response
         `uvm_warning(get_type_name(),
                      $sformatf("Read transaction got non-OKAY response: %s at addr=0x%08h",
                               txn.resp_to_string(txn.resp), addr))
      end
   endfunction
   
   //============================================================================
   // Special Checking Functions
   //============================================================================
   
   // Check for read-after-write hazards
   virtual function void check_raw_hazard(axi4lite_txn read_txn);
      foreach (write_history[i]) begin
         if (write_history[i].addr == read_txn.addr) begin
            if ((read_txn.start_time - write_history[i].end_time) < 2) begin
               `uvm_info(get_type_name(),
                        $sformatf("Detected RAW hazard at addr=0x%08h with %0d cycle gap",
                                 read_txn.addr, 
                                 (read_txn.start_time - write_history[i].end_time)),
                        UVM_MEDIUM)
            end
         end
      end
   endfunction
   
   //============================================================================
   // Report Phase - Print Statistics
   //============================================================================
   
   virtual function void report_phase(uvm_phase phase);
      super.report_phase(phase);
      
      `uvm_info(get_type_name(), "============================================", UVM_NONE)
      `uvm_info(get_type_name(), "      SCOREBOARD FINAL REPORT", UVM_NONE)
      `uvm_info(get_type_name(), "============================================", UVM_NONE)
      `uvm_info(get_type_name(), $sformatf("Total Writes:       %0d", num_writes), UVM_NONE)
      `uvm_info(get_type_name(), $sformatf("Total Reads:        %0d", num_reads), UVM_NONE)
      `uvm_info(get_type_name(), $sformatf("Total Transactions: %0d", num_writes + num_reads), UVM_NONE)
      `uvm_info(get_type_name(), $sformatf("Passed Checks:      %0d", num_passed), UVM_NONE)
      `uvm_info(get_type_name(), $sformatf("Failed Checks:      %0d", num_mismatches), UVM_NONE)
      
      if (num_mismatches == 0) begin
         `uvm_info(get_type_name(), "*** ALL CHECKS PASSED ***", UVM_NONE)
      end else begin
         `uvm_error(get_type_name(), 
                    $sformatf("*** %0d MISMATCHES DETECTED ***", num_mismatches))
      end
      `uvm_info(get_type_name(), "============================================", UVM_NONE)
   endfunction
   
   //============================================================================
   // Extract Phase - Used for final analysis
   //============================================================================
   
   virtual function void extract_phase(uvm_phase phase);
      super.extract_phase(phase);
      
      // Dump reference memory for debugging
      if (uvm_report_enabled(UVM_DEBUG)) begin
         `uvm_info(get_type_name(), "Reference Memory Dump:", UVM_DEBUG)
         foreach (ref_memory[addr]) begin
            `uvm_info(get_type_name(), 
                     $sformatf("  [0x%08h] = 0x%08h", addr, ref_memory[addr]),
                     UVM_DEBUG)
         end
      end
   endfunction

endclass : axi4lite_scoreboard

