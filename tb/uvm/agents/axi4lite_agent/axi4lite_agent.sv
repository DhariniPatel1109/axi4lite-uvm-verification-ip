////////////////////////////////////////////////////////////////////////////////
// AXI4-Lite Agent
// Container for sequencer, driver, and monitor
////////////////////////////////////////////////////////////////////////////////

class axi4lite_agent extends uvm_agent;
   
   `uvm_component_utils(axi4lite_agent)
   
   // Components
   axi4lite_sequencer  sqr;
   axi4lite_driver     drv;
   axi4lite_monitor    mon;
   
   // Analysis port for external connections
   uvm_analysis_port #(axi4lite_txn) item_collected_port;
   
   //============================================================================
   // Constructor & Build Phase
   //============================================================================
   
   function new(string name, uvm_component parent);
      super.new(name, parent);
   endfunction
   
   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      
      // Create monitor (always present)
      mon = axi4lite_monitor::type_id::create("mon", this);
      
      // Create sequencer and driver if agent is active
      if (get_is_active() == UVM_ACTIVE) begin
         sqr = axi4lite_sequencer::type_id::create("sqr", this);
         drv = axi4lite_driver::type_id::create("drv", this);
      end
   endfunction
   
   //============================================================================
   // Connect Phase
   //============================================================================
   
   function void connect_phase(uvm_phase phase);
      super.connect_phase(phase);
      
      // Connect driver to sequencer if active
      if (get_is_active() == UVM_ACTIVE) begin
         drv.seq_item_port.connect(sqr.seq_item_export);
      end
      
      // Export monitor's analysis port
      item_collected_port = mon.item_collected_port;
   endfunction
   
   //============================================================================
   // Report Phase
   //============================================================================
   
   function void report_phase(uvm_phase phase);
      super.report_phase(phase);
      `uvm_info(get_type_name(), "Agent reporting phase complete", UVM_HIGH)
   endfunction

endclass : axi4lite_agent

