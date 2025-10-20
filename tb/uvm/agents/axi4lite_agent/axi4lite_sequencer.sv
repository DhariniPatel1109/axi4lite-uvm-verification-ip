////////////////////////////////////////////////////////////////////////////////
// AXI4-Lite Sequencer
// Controls the flow of transactions to the driver
////////////////////////////////////////////////////////////////////////////////

class axi4lite_sequencer extends uvm_sequencer #(axi4lite_txn);
   
   `uvm_component_utils(axi4lite_sequencer)
   
   function new(string name, uvm_component parent);
      super.new(name, parent);
   endfunction

endclass : axi4lite_sequencer

