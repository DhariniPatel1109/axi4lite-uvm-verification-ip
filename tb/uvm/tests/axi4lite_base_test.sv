////////////////////////////////////////////////////////////////////////////////
// AXI4-Lite Base Test
// Base test class that all other tests extend from
////////////////////////////////////////////////////////////////////////////////

class axi4lite_base_test extends uvm_test;
   
   `uvm_component_utils(axi4lite_base_test)
   
   // Environment instance
   axi4lite_env env;
   
   // Virtual interface
   virtual axi4lite_if vif;
   
   //============================================================================
   // Constructor & Build Phase
   //============================================================================
   
   function new(string name = "axi4lite_base_test", uvm_component parent = null);
      super.new(name, parent);
   endfunction
   
   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      
      // Get virtual interface from config DB
      if (!uvm_config_db#(virtual axi4lite_if)::get(this, "", "vif", vif))
         `uvm_fatal(get_type_name(), "Virtual interface not found in config DB")
      
      // Set interface for all components
      uvm_config_db#(virtual axi4lite_if)::set(this, "*", "vif", vif);
      
      // Create environment
      env = axi4lite_env::type_id::create("env", this);
      
      // Set verbosity
      set_report_verbosity_level(UVM_MEDIUM);
      
      `uvm_info(get_type_name(), "Base test built", UVM_LOW)
   endfunction
   
   //============================================================================
   // End of Elaboration Phase
   //============================================================================
   
   function void end_of_elaboration_phase(uvm_phase phase);
      super.end_of_elaboration_phase(phase);
      `uvm_info(get_type_name(), "Test topology complete", UVM_LOW)
   endfunction
   
   //============================================================================
   // Run Phase
   //============================================================================
   
   task run_phase(uvm_phase phase);
      // Derived tests will implement their specific sequences
      `uvm_info(get_type_name(), "Base test run phase started", UVM_LOW)
   endtask
   
   //============================================================================
   // Report Phase
   //============================================================================
   
   function void report_phase(uvm_phase phase);
      uvm_report_server svr;
      super.report_phase(phase);
      
      svr = uvm_report_server::get_server();
      
      `uvm_info(get_type_name(), "========================================", UVM_NONE)
      `uvm_info(get_type_name(), "        TEST SUMMARY", UVM_NONE)
      `uvm_info(get_type_name(), "========================================", UVM_NONE)
      
      if (svr.get_severity_count(UVM_FATAL) + svr.get_severity_count(UVM_ERROR) == 0) begin
         `uvm_info(get_type_name(), "*** TEST PASSED ***", UVM_NONE)
      end else begin
         `uvm_error(get_type_name(), "*** TEST FAILED ***")
      end
      
      `uvm_info(get_type_name(), "========================================", UVM_NONE)
   endfunction

endclass : axi4lite_base_test

