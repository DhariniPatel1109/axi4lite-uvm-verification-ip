////////////////////////////////////////////////////////////////////////////////
// AXI4-Lite Monitor
// Monitors AXI4-Lite bus and collects completed transactions
////////////////////////////////////////////////////////////////////////////////

class axi4lite_monitor extends uvm_monitor;
   
   `uvm_component_utils(axi4lite_monitor)
   
   // Virtual interface
   virtual axi4lite_if vif;
   
   // Analysis port to broadcast collected transactions
   uvm_analysis_port #(axi4lite_txn) item_collected_port;
   
   //============================================================================
   // Constructor & Build Phase
   //============================================================================
   
   function new(string name, uvm_component parent);
      super.new(name, parent);
   endfunction
   
   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      item_collected_port = new("item_collected_port", this);
      if (!uvm_config_db#(virtual axi4lite_if)::get(this, "", "vif", vif))
         `uvm_fatal(get_type_name(), "Virtual interface not found in config DB")
   endfunction
   
   //============================================================================
   // Run Phase
   //============================================================================
   
   virtual task run_phase(uvm_phase phase);
      fork
         collect_write_transactions();
         collect_read_transactions();
      join
   endtask
   
   //============================================================================
   // Collect Write Transactions
   //============================================================================
   
   virtual task collect_write_transactions();
      axi4lite_txn txn;
      bit [31:0] addr;
      bit [31:0] data;
      bit [3:0]  strb;
      bit [2:0]  prot;
      bit [1:0]  resp;
      time       start_time, end_time;
      
      forever begin
         // Wait for reset
         @(posedge vif.clk);
         wait(vif.rst_n == 1'b1);
         
         // Wait for write address valid
         @(posedge vif.clk);
         if (vif.AWVALID && vif.AWREADY) begin
            // Capture write address phase
            addr = vif.AWADDR;
            prot = vif.AWPROT;
            start_time = $time;
            
            // Wait for write data phase (may occur simultaneously or later)
            while (!(vif.WVALID && vif.WREADY))
               @(posedge vif.clk);
            
            data = vif.WDATA;
            strb = vif.WSTRB;
            
            // Wait for write response
            while (!(vif.BVALID && vif.BREADY))
               @(posedge vif.clk);
            
            resp = vif.BRESP;
            end_time = $time;
            
            // Create and populate transaction
            txn = axi4lite_txn::type_id::create("txn");
            txn.txn_type = WRITE;
            txn.addr = addr;
            txn.data = data;
            txn.strb = strb;
            txn.prot = prot;
            txn.resp = resp;
            txn.start_time = start_time;
            txn.end_time = end_time;
            
            `uvm_info(get_type_name(),
                     $sformatf("Collected WRITE: %s", txn.convert2string()),
                     UVM_MEDIUM)
            
            // Broadcast to subscribers
            item_collected_port.write(txn);
         end
      end
   endtask
   
   //============================================================================
   // Collect Read Transactions
   //============================================================================
   
   virtual task collect_read_transactions();
      axi4lite_txn txn;
      bit [31:0] addr;
      bit [31:0] data;
      bit [2:0]  prot;
      bit [1:0]  resp;
      time       start_time, end_time;
      
      forever begin
         // Wait for reset
         @(posedge vif.clk);
         wait(vif.rst_n == 1'b1);
         
         // Wait for read address valid
         @(posedge vif.clk);
         if (vif.ARVALID && vif.ARREADY) begin
            // Capture read address phase
            addr = vif.ARADDR;
            prot = vif.ARPROT;
            start_time = $time;
            
            // Wait for read data phase
            while (!(vif.RVALID && vif.RREADY))
               @(posedge vif.clk);
            
            data = vif.RDATA;
            resp = vif.RRESP;
            end_time = $time;
            
            // Create and populate transaction
            txn = axi4lite_txn::type_id::create("txn");
            txn.txn_type = READ;
            txn.addr = addr;
            txn.data = data;
            txn.prot = prot;
            txn.resp = resp;
            txn.start_time = start_time;
            txn.end_time = end_time;
            
            `uvm_info(get_type_name(),
                     $sformatf("Collected READ:  %s", txn.convert2string()),
                     UVM_MEDIUM)
            
            // Broadcast to subscribers
            item_collected_port.write(txn);
         end
      end
   endtask
   
   //============================================================================
   // Protocol Violation Checks (Optional - assertions in interface are primary)
   //============================================================================
   
   virtual task check_protocol_violations();
      // Additional runtime checks can be added here
      // The interface assertions handle most protocol checking
   endtask

endclass : axi4lite_monitor

