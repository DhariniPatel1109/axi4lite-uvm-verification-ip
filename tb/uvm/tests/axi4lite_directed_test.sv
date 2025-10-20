////////////////////////////////////////////////////////////////////////////////
// AXI4-Lite Directed Test
// Tests all registers with predictable patterns
////////////////////////////////////////////////////////////////////////////////

class axi4lite_directed_test extends axi4lite_base_test;
   
   `uvm_component_utils(axi4lite_directed_test)
   
   function new(string name = "axi4lite_directed_test", uvm_component parent = null);
      super.new(name, parent);
   endfunction
   
   task run_phase(uvm_phase phase);
      axi4lite_directed_seq seq;
      
      phase.raise_objection(this, "Starting directed test");
      
      `uvm_info(get_type_name(), "=== DIRECTED TEST STARTED ===", UVM_LOW)
      
      seq = axi4lite_directed_seq::type_id::create("seq");
      seq.start(env.agent.sqr);
      
      #100ns;
      
      `uvm_info(get_type_name(), "=== DIRECTED TEST COMPLETED ===", UVM_LOW)
      
      phase.drop_objection(this, "Directed test complete");
   endtask

endclass : axi4lite_directed_test

