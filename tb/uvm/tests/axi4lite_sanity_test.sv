////////////////////////////////////////////////////////////////////////////////
// AXI4-Lite Sanity Test
// Simple test to verify basic read and write functionality
////////////////////////////////////////////////////////////////////////////////

class axi4lite_sanity_test extends axi4lite_base_test;
   
   `uvm_component_utils(axi4lite_sanity_test)
   
   function new(string name = "axi4lite_sanity_test", uvm_component parent = null);
      super.new(name, parent);
   endfunction
   
   task run_phase(uvm_phase phase);
      axi4lite_write_read_seq seq;
      
      phase.raise_objection(this, "Starting sanity test");
      
      `uvm_info(get_type_name(), "=== SANITY TEST STARTED ===", UVM_LOW)
      
      // Execute 10 write-read sequences
      repeat(10) begin
         seq = axi4lite_write_read_seq::type_id::create("seq");
         assert(seq.randomize());
         seq.start(env.agent.sqr);
      end
      
      #100ns;  // Allow transactions to complete
      
      `uvm_info(get_type_name(), "=== SANITY TEST COMPLETED ===", UVM_LOW)
      
      phase.drop_objection(this, "Sanity test complete");
   endtask

endclass : axi4lite_sanity_test

