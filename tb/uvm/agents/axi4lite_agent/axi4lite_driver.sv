////////////////////////////////////////////////////////////////////////////////
// AXI4-Lite Driver
// Drives AXI4-Lite transactions onto the interface
////////////////////////////////////////////////////////////////////////////////

class axi4lite_driver extends uvm_driver #(axi4lite_txn);
   
   `uvm_component_utils(axi4lite_driver)
   
   // Virtual interface
   virtual axi4lite_if vif;
   
   //============================================================================
   // Constructor & Build Phase
   //============================================================================
   
   function new(string name, uvm_component parent);
      super.new(name, parent);
   endfunction
   
   function void build_phase(uvm_phase phase);
      super.build_phase(phase);
      if (!uvm_config_db#(virtual axi4lite_if)::get(this, "", "vif", vif))
         `uvm_fatal(get_type_name(), "Virtual interface not found in config DB")
   endfunction
   
   //============================================================================
   // Run Phase
   //============================================================================
   
   virtual task run_phase(uvm_phase phase);
      fork
         get_and_drive();
         reset_monitor();
      join
   endtask
   
   //============================================================================
   // Get and Drive Task
   //============================================================================
   
   virtual task get_and_drive();
      axi4lite_txn txn;
      
      forever begin
         // Wait for reset to be deasserted
         @(posedge vif.clk);
         wait(vif.rst_n == 1'b1);
         
         // Get next transaction from sequencer
         seq_item_port.get_next_item(txn);
         
         // Record start time
         txn.start_time = $time;
         
         `uvm_info(get_type_name(), 
                  $sformatf("Driving transaction: %s", txn.convert2string()),
                  UVM_MEDIUM)
         
         // Add inter-transaction delay
         repeat(txn.delay_cycles) @(posedge vif.clk);
         
         // Drive the transaction
         if (txn.txn_type == WRITE)
            drive_write(txn);
         else
            drive_read(txn);
         
         // Record end time
         txn.end_time = $time;
         
         // Indicate transaction is done
         seq_item_port.item_done();
      end
   endtask
   
   //============================================================================
   // Drive Write Transaction
   //============================================================================
   
   virtual task drive_write(axi4lite_txn txn);
      // Drive write address and write data channels simultaneously
      fork
         drive_write_address(txn);
         drive_write_data(txn);
      join
      
      // Wait for write response
      wait_write_response(txn);
   endtask
   
   // Drive Write Address Channel
   virtual task drive_write_address(axi4lite_txn txn);
      vif.AWADDR  <= txn.addr;
      vif.AWPROT  <= txn.prot;
      vif.AWVALID <= 1'b1;
      
      // Wait for AWREADY
      @(posedge vif.clk);
      while (!vif.AWREADY) @(posedge vif.clk);
      
      // Deassert after handshake
      vif.AWVALID <= 1'b0;
      vif.AWADDR  <= 32'h0;
      vif.AWPROT  <= 3'h0;
   endtask
   
   // Drive Write Data Channel
   virtual task drive_write_data(axi4lite_txn txn);
      vif.WDATA  <= txn.data;
      vif.WSTRB  <= txn.strb;
      vif.WVALID <= 1'b1;
      
      // Wait for WREADY
      @(posedge vif.clk);
      while (!vif.WREADY) @(posedge vif.clk);
      
      // Deassert after handshake
      vif.WVALID <= 1'b0;
      vif.WDATA  <= 32'h0;
      vif.WSTRB  <= 4'h0;
   endtask
   
   // Wait for Write Response
   virtual task wait_write_response(axi4lite_txn txn);
      int timeout_count = 0;
      
      vif.BREADY <= 1'b1;
      
      // Wait for BVALID
      @(posedge vif.clk);
      while (!vif.BVALID) begin
         @(posedge vif.clk);
         timeout_count++;
         if (timeout_count > 100) begin
            `uvm_error(get_type_name(), "Timeout waiting for BVALID")
            return;
         end
      end
      
      // Capture response
      txn.resp = vif.BRESP;
      
      if (vif.BRESP != 2'b00)
         `uvm_warning(get_type_name(), 
                     $sformatf("Write response error: %s", txn.resp_to_string(vif.BRESP)))
      
      // Complete handshake
      @(posedge vif.clk);
      vif.BREADY <= 1'b1;  // Keep ready high
   endtask
   
   //============================================================================
   // Drive Read Transaction
   //============================================================================
   
   virtual task drive_read(axi4lite_txn txn);
      // Drive read address channel
      drive_read_address(txn);
      
      // Wait for read data response
      wait_read_data(txn);
   endtask
   
   // Drive Read Address Channel
   virtual task drive_read_address(axi4lite_txn txn);
      vif.ARADDR  <= txn.addr;
      vif.ARPROT  <= txn.prot;
      vif.ARVALID <= 1'b1;
      
      // Wait for ARREADY
      @(posedge vif.clk);
      while (!vif.ARREADY) @(posedge vif.clk);
      
      // Deassert after handshake
      vif.ARVALID <= 1'b0;
      vif.ARADDR  <= 32'h0;
      vif.ARPROT  <= 3'h0;
   endtask
   
   // Wait for Read Data
   virtual task wait_read_data(axi4lite_txn txn);
      int timeout_count = 0;
      
      vif.RREADY <= 1'b1;
      
      // Wait for RVALID
      @(posedge vif.clk);
      while (!vif.RVALID) begin
         @(posedge vif.clk);
         timeout_count++;
         if (timeout_count > 100) begin
            `uvm_error(get_type_name(), "Timeout waiting for RVALID")
            return;
         end
      end
      
      // Capture read data and response
      txn.data = vif.RDATA;
      txn.resp = vif.RRESP;
      
      if (vif.RRESP != 2'b00)
         `uvm_warning(get_type_name(),
                     $sformatf("Read response error: %s", txn.resp_to_string(vif.RRESP)))
      
      // Complete handshake
      @(posedge vif.clk);
      vif.RREADY <= 1'b1;  // Keep ready high
   endtask
   
   //============================================================================
   // Reset Monitor - Reset signals when reset is asserted
   //============================================================================
   
   virtual task reset_monitor();
      forever begin
         @(negedge vif.rst_n);
         
         `uvm_info(get_type_name(), "Reset asserted - clearing all signals", UVM_MEDIUM)
         
         // Clear all signals
         vif.AWADDR  <= 32'h0;
         vif.AWPROT  <= 3'h0;
         vif.AWVALID <= 1'b0;
         vif.WDATA   <= 32'h0;
         vif.WSTRB   <= 4'h0;
         vif.WVALID  <= 1'b0;
         vif.BREADY  <= 1'b1;
         vif.ARADDR  <= 32'h0;
         vif.ARPROT  <= 3'h0;
         vif.ARVALID <= 1'b0;
         vif.RREADY  <= 1'b1;
         
         @(posedge vif.rst_n);
         `uvm_info(get_type_name(), "Reset deasserted", UVM_MEDIUM)
      end
   endtask

endclass : axi4lite_driver

