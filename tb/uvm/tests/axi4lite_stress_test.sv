////////////////////////////////////////////////////////////////////////////////
// AXI4-Lite Stress Test
// High-intensity test with back-to-back transactions and stress patterns
////////////////////////////////////////////////////////////////////////////////

class axi4lite_stress_test extends axi4lite_base_test;
   
   `uvm_component_utils(axi4lite_stress_test)
   
   function new(string name = "axi4lite_stress_test", uvm_component parent = null);
      super.new(name, parent);
   endfunction
   
   task run_phase(uvm_phase phase);
      axi4lite_back_to_back_seq b2b_seq;
      axi4lite_stress_seq stress_seq;
      axi4lite_corner_case_seq corner_seq;
      
      phase.raise_objection(this, "Starting stress test");
      
      `uvm_info(get_type_name(), "=== STRESS TEST STARTED ===", UVM_LOW)
      
      // Back-to-back transactions
      b2b_seq = axi4lite_back_to_back_seq::type_id::create("b2b_seq");
      b2b_seq.start(env.agent.sqr);
      
      // Corner cases
      corner_seq = axi4lite_corner_case_seq::type_id::create("corner_seq");
      corner_seq.start(env.agent.sqr);
      
      // High-intensity stress
      stress_seq = axi4lite_stress_seq::type_id::create("stress_seq");
      stress_seq.start(env.agent.sqr);
      
      #100ns;
      
      `uvm_info(get_type_name(), "=== STRESS TEST COMPLETED ===", UVM_LOW)
      
      phase.drop_objection(this, "Stress test complete");
   endtask

endclass : axi4lite_stress_test

