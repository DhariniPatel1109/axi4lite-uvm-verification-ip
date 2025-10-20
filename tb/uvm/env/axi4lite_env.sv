////////////////////////////////////////////////////////////////////////////////
// AXI4-Lite Environment
// Top-level verification environment containing agent, scoreboard, and coverage
////////////////////////////////////////////////////////////////////////////////

class axi4lite_env extends uvm_env;
   
   `uvm_component_utils(axi4lite_env)
   
   // Components
   axi4lite_agent         agent;
   axi4lite_scoreboard    scb;
   axi4lite_coverage      cov;
   
   //============================================================================
   // Constructor & Build Phase
   //============================================================================
   
   function new(string name, uvm_component parent);
      super.new(name, parent);
   endfunction
   
   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      
      // Create components
      agent = axi4lite_agent::type_id::create("agent", this);
      scb   = axi4lite_scoreboard::type_id::create("scb", this);
      cov   = axi4lite_coverage::type_id::create("cov", this);
      
      // Configure agent as active
      agent.is_active = UVM_ACTIVE;
      
      `uvm_info(get_type_name(), "Environment built successfully", UVM_LOW)
   endfunction
   
   //============================================================================
   // Connect Phase
   //============================================================================
   
   function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);
      
      // Connect monitor to scoreboard
      agent.mon.item_collected_port.connect(scb.item_collected_export);
      
      // Connect monitor to coverage collector
      agent.mon.item_collected_port.connect(cov.analysis_export);
      
      `uvm_info(get_type_name(), "Environment connections established", UVM_LOW)
   endfunction
   
   //============================================================================
   // End of Elaboration Phase
   //============================================================================
   
   function void end_of_elaboration_phase(uvm_phase phase);
      super.end_of_elaboration_phase(phase);
      `uvm_info(get_type_name(), "Environment topology:", UVM_LOW)
      uvm_top.print_topology();
   endfunction
   
   //============================================================================
   // Report Phase
   //============================================================================
   
   function void report_phase(uvm_phase phase);
      super.report_phase(phase);
      `uvm_info(get_type_name(), "Environment report phase complete", UVM_LOW)
   endfunction

endclass : axi4lite_env

