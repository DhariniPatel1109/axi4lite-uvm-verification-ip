////////////////////////////////////////////////////////////////////////////////
// AXI4-Lite Sequence Library
// Collection of test sequences: directed tests and constrained-random tests
////////////////////////////////////////////////////////////////////////////////

//============================================================================
// Base Sequence
//============================================================================

class axi4lite_base_seq extends uvm_sequence #(axi4lite_txn);
   
   `uvm_object_utils(axi4lite_base_seq)
   
   function new(string name = "axi4lite_base_seq");
      super.new(name);
   endfunction

endclass : axi4lite_base_seq

//============================================================================
// Reset Sequence - Tests behavior during and after reset
//============================================================================

class axi4lite_reset_seq extends axi4lite_base_seq;
   
   `uvm_object_utils(axi4lite_reset_seq)
   
   function new(string name = "axi4lite_reset_seq");
      super.new(name);
   endfunction
   
   virtual task body();
      `uvm_info(get_type_name(), "Executing reset sequence", UVM_LOW)
      // Reset is handled by testbench, this sequence just waits
      #100ns;
      `uvm_info(get_type_name(), "Reset sequence complete", UVM_LOW)
   endtask

endclass : axi4lite_reset_seq

//============================================================================
// Single Write Sequence
//============================================================================

class axi4lite_single_write_seq extends axi4lite_base_seq;
   
   `uvm_object_utils(axi4lite_single_write_seq)
   
   rand bit [31:0] addr;
   rand bit [31:0] data;
   
   constraint c_addr { addr < 32*4; addr[1:0] == 2'b00; }
   
   function new(string name = "axi4lite_single_write_seq");
      super.new(name);
   endfunction
   
   virtual task body();
      axi4lite_txn txn;
      
      `uvm_info(get_type_name(), 
               $sformatf("Executing single write: addr=0x%08h, data=0x%08h", addr, data),
               UVM_LOW)
      
      txn = axi4lite_txn::type_id::create("txn");
      start_item(txn);
      assert(txn.randomize() with {
         txn_type == WRITE;
         addr == local::addr;
         data == local::data;
      });
      finish_item(txn);
   endtask

endclass : axi4lite_single_write_seq

//============================================================================
// Single Read Sequence
//============================================================================

class axi4lite_single_read_seq extends axi4lite_base_seq;
   
   `uvm_object_utils(axi4lite_single_read_seq)
   
   rand bit [31:0] addr;
   
   constraint c_addr { addr < 32*4; addr[1:0] == 2'b00; }
   
   function new(string name = "axi4lite_single_read_seq");
      super.new(name);
   endfunction
   
   virtual task body();
      axi4lite_txn txn;
      
      `uvm_info(get_type_name(), 
               $sformatf("Executing single read: addr=0x%08h", addr),
               UVM_LOW)
      
      txn = axi4lite_txn::type_id::create("txn");
      start_item(txn);
      assert(txn.randomize() with {
         txn_type == READ;
         addr == local::addr;
      });
      finish_item(txn);
   endtask

endclass : axi4lite_single_read_seq

//============================================================================
// Write-Read Sequence - Write then read back from same address
//============================================================================

class axi4lite_write_read_seq extends axi4lite_base_seq;
   
   `uvm_object_utils(axi4lite_write_read_seq)
   
   rand bit [31:0] addr;
   rand bit [31:0] data;
   
   constraint c_addr { addr < 32*4; addr[1:0] == 2'b00; }
   
   function new(string name = "axi4lite_write_read_seq");
      super.new(name);
   endfunction
   
   virtual task body();
      axi4lite_txn txn;
      
      `uvm_info(get_type_name(), 
               $sformatf("Executing write-read: addr=0x%08h, data=0x%08h", addr, data),
               UVM_LOW)
      
      // Write
      txn = axi4lite_txn::type_id::create("write_txn");
      start_item(txn);
      assert(txn.randomize() with {
         txn_type == WRITE;
         addr == local::addr;
         data == local::data;
      });
      finish_item(txn);
      
      // Read back
      txn = axi4lite_txn::type_id::create("read_txn");
      start_item(txn);
      assert(txn.randomize() with {
         txn_type == READ;
         addr == local::addr;
      });
      finish_item(txn);
   endtask

endclass : axi4lite_write_read_seq

//============================================================================
// Directed Sequence - Tests all registers sequentially
//============================================================================

class axi4lite_directed_seq extends axi4lite_base_seq;
   
   `uvm_object_utils(axi4lite_directed_seq)
   
   function new(string name = "axi4lite_directed_seq");
      super.new(name);
   endfunction
   
   virtual task body();
      axi4lite_txn txn;
      
      `uvm_info(get_type_name(), "Executing directed sequence - testing all registers", UVM_LOW)
      
      // Write to all 32 registers with incremental patterns
      for (int i = 0; i < 32; i++) begin
         txn = axi4lite_txn::type_id::create($sformatf("write_txn_%0d", i));
         start_item(txn);
         assert(txn.randomize() with {
            txn_type == WRITE;
            addr == i * 4;
            data == 32'hA5A5A500 + i;
            delay_cycles == 0;
         });
         finish_item(txn);
      end
      
      // Read back all 32 registers
      for (int i = 0; i < 32; i++) begin
         txn = axi4lite_txn::type_id::create($sformatf("read_txn_%0d", i));
         start_item(txn);
         assert(txn.randomize() with {
            txn_type == READ;
            addr == i * 4;
            delay_cycles == 0;
         });
         finish_item(txn);
      end
      
      `uvm_info(get_type_name(), "Directed sequence complete", UVM_LOW)
   endtask

endclass : axi4lite_directed_seq

//============================================================================
// Random Sequence - Constrained random reads and writes
//============================================================================

class axi4lite_random_seq extends axi4lite_base_seq;
   
   `uvm_object_utils(axi4lite_random_seq)
   
   rand int num_txns;
   
   constraint c_num_txns { num_txns inside {[10:50]}; }
   
   function new(string name = "axi4lite_random_seq");
      super.new(name);
   endfunction
   
   virtual task body();
      axi4lite_txn txn;
      
      `uvm_info(get_type_name(), 
               $sformatf("Executing random sequence with %0d transactions", num_txns),
               UVM_LOW)
      
      repeat(num_txns) begin
         txn = axi4lite_txn::type_id::create("random_txn");
         start_item(txn);
         assert(txn.randomize());
         finish_item(txn);
      end
      
      `uvm_info(get_type_name(), "Random sequence complete", UVM_LOW)
   endtask

endclass : axi4lite_random_seq

//============================================================================
// Back-to-Back Sequence - Tests zero-delay transactions
//============================================================================

class axi4lite_back_to_back_seq extends axi4lite_base_seq;
   
   `uvm_object_utils(axi4lite_back_to_back_seq)
   
   function new(string name = "axi4lite_back_to_back_seq");
      super.new(name);
   endfunction
   
   virtual task body();
      axi4lite_txn txn;
      
      `uvm_info(get_type_name(), "Executing back-to-back sequence", UVM_LOW)
      
      // 20 back-to-back transactions
      repeat(20) begin
         txn = axi4lite_txn::type_id::create("b2b_txn");
         start_item(txn);
         assert(txn.randomize() with {
            delay_cycles == 0;  // No delay between transactions
         });
         finish_item(txn);
      end
      
      `uvm_info(get_type_name(), "Back-to-back sequence complete", UVM_LOW)
   endtask

endclass : axi4lite_back_to_back_seq

//============================================================================
// Corner Case Sequence - Tests boundary conditions
//============================================================================

class axi4lite_corner_case_seq extends axi4lite_base_seq;
   
   `uvm_object_utils(axi4lite_corner_case_seq)
   
   function new(string name = "axi4lite_corner_case_seq");
      super.new(name);
   endfunction
   
   virtual task body();
      axi4lite_txn txn;
      
      `uvm_info(get_type_name(), "Executing corner case sequence", UVM_LOW)
      
      // Test 1: Write all zeros
      txn = axi4lite_txn::type_id::create("zeros_txn");
      start_item(txn);
      assert(txn.randomize() with {
         txn_type == WRITE;
         addr == 0;
         data == 32'h00000000;
      });
      finish_item(txn);
      
      // Test 2: Write all ones
      txn = axi4lite_txn::type_id::create("ones_txn");
      start_item(txn);
      assert(txn.randomize() with {
         txn_type == WRITE;
         addr == 4;
         data == 32'hFFFFFFFF;
      });
      finish_item(txn);
      
      // Test 3: Alternating pattern
      txn = axi4lite_txn::type_id::create("alt1_txn");
      start_item(txn);
      assert(txn.randomize() with {
         txn_type == WRITE;
         addr == 8;
         data == 32'hAAAAAAAA;
      });
      finish_item(txn);
      
      // Test 4: Opposite alternating pattern
      txn = axi4lite_txn::type_id::create("alt2_txn");
      start_item(txn);
      assert(txn.randomize() with {
         txn_type == WRITE;
         addr == 12;
         data == 32'h55555555;
      });
      finish_item(txn);
      
      // Test 5: First register
      txn = axi4lite_txn::type_id::create("first_reg_txn");
      start_item(txn);
      assert(txn.randomize() with {
         txn_type == WRITE;
         addr == 0;
         data == 32'hDEADBEEF;
      });
      finish_item(txn);
      
      // Test 6: Last register
      txn = axi4lite_txn::type_id::create("last_reg_txn");
      start_item(txn);
      assert(txn.randomize() with {
         txn_type == WRITE;
         addr == 31*4;
         data == 32'hCAFEBABE;
      });
      finish_item(txn);
      
      // Read back all corner cases
      for (int addr_val : '{0, 4, 8, 12, 0, 31*4}) begin
         txn = axi4lite_txn::type_id::create("corner_read_txn");
         start_item(txn);
         assert(txn.randomize() with {
            txn_type == READ;
            addr == addr_val;
         });
         finish_item(txn);
      end
      
      `uvm_info(get_type_name(), "Corner case sequence complete", UVM_LOW)
   endtask

endclass : axi4lite_corner_case_seq

//============================================================================
// Stress Sequence - High-intensity random traffic
//============================================================================

class axi4lite_stress_seq extends axi4lite_base_seq;
   
   `uvm_object_utils(axi4lite_stress_seq)
   
   function new(string name = "axi4lite_stress_seq");
      super.new(name);
   endfunction
   
   virtual task body();
      axi4lite_txn txn;
      
      `uvm_info(get_type_name(), "Executing stress sequence - 500 random transactions", UVM_LOW)
      
      repeat(500) begin
         txn = axi4lite_txn::type_id::create("stress_txn");
         start_item(txn);
         assert(txn.randomize());
         finish_item(txn);
      end
      
      `uvm_info(get_type_name(), "Stress sequence complete", UVM_LOW)
   endtask

endclass : axi4lite_stress_seq

