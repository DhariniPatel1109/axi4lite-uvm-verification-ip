////////////////////////////////////////////////////////////////////////////////
// AXI4-Lite Random Test
// Constrained-random test for comprehensive coverage
////////////////////////////////////////////////////////////////////////////////

class axi4lite_random_test extends axi4lite_base_test;
   
   `uvm_component_utils(axi4lite_random_test)
   
   function new(string name = "axi4lite_random_test", uvm_component parent = null);
      super.new(name, parent);
   endfunction
   
   task run_phase(uvm_phase phase);
      axi4lite_random_seq seq;
      
      phase.raise_objection(this, "Starting random test");
      
      `uvm_info(get_type_name(), "=== RANDOM TEST STARTED ===", UVM_LOW)
      
      // Run 5 iterations of random sequences
      repeat(5) begin
         seq = axi4lite_random_seq::type_id::create("seq");
         assert(seq.randomize());
         seq.start(env.agent.sqr);
      end
      
      #100ns;
      
      `uvm_info(get_type_name(), "=== RANDOM TEST COMPLETED ===", UVM_LOW)
      
      phase.drop_objection(this, "Random test complete");
   endtask

endclass : axi4lite_random_test

