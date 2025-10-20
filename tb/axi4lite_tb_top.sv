////////////////////////////////////////////////////////////////////////////////
// AXI4-Lite Testbench Top Module
// Instantiates DUT, interface, clock/reset generation, and UVM test
////////////////////////////////////////////////////////////////////////////////

`timescale 1ns/1ps

module axi4lite_tb_top;
   
   import uvm_pkg::*;
   import axi4lite_pkg::*;
   
   `include "uvm_macros.svh"
   
   //============================================================================
   // Clock and Reset
   //============================================================================
   
   logic clk;
   logic rst_n;
   
   // Clock generation - 100MHz (10ns period)
   initial begin
      clk = 0;
      forever #5ns clk = ~clk;
   end
   
   // Reset generation
   initial begin
      rst_n = 0;
      repeat(5) @(posedge clk);
      rst_n = 1;
      `uvm_info("TB_TOP", "Reset deasserted", UVM_LOW)
   end
   
   //============================================================================
   // Interface Instance
   //============================================================================
   
   axi4lite_if vif(clk, rst_n);
   
   //============================================================================
   // DUT Instance
   //============================================================================
   
   axi4_lite_slave #(
      .ADDRESS(32),
      .DATA_WIDTH(32)
   ) dut (
      .ACLK      (clk),
      .ARESETN   (rst_n),
      // Write Address Channel
      .S_AWADDR  (vif.AWADDR),
      .S_AWVALID (vif.AWVALID),
      .S_AWREADY (vif.AWREADY),
      // Write Data Channel
      .S_WDATA   (vif.WDATA),
      .S_WSTRB   (vif.WSTRB),
      .S_WVALID  (vif.WVALID),
      .S_WREADY  (vif.WREADY),
      // Write Response Channel
      .S_BRESP   (vif.BRESP),
      .S_BVALID  (vif.BVALID),
      .S_BREADY  (vif.BREADY),
      // Read Address Channel
      .S_ARADDR  (vif.ARADDR),
      .S_ARVALID (vif.ARVALID),
      .S_ARREADY (vif.ARREADY),
      // Read Data Channel
      .S_RDATA   (vif.RDATA),
      .S_RRESP   (vif.RRESP),
      .S_RVALID  (vif.RVALID),
      .S_RREADY  (vif.RREADY)
   );
   
   //============================================================================
   // Waveform Dumping
   //============================================================================
   
   initial begin
      if ($test$plusargs("DUMP_VCD")) begin
         $dumpfile("axi4lite_tb.vcd");
         $dumpvars(0, axi4lite_tb_top);
         `uvm_info("TB_TOP", "VCD dump enabled", UVM_LOW)
      end
      
      if ($test$plusargs("DUMP_FST")) begin
         $dumpfile("axi4lite_tb.fst");
         $dumpvars(0, axi4lite_tb_top);
         `uvm_info("TB_TOP", "FST dump enabled", UVM_LOW)
      end
   end
   
   //============================================================================
   // UVM Configuration and Test Execution
   //============================================================================
   
   initial begin
      // Set the virtual interface in config DB
      uvm_config_db#(virtual axi4lite_if)::set(null, "*", "vif", vif);
      
      // Configure report verbosity
      uvm_top.set_report_verbosity_level_hier(UVM_MEDIUM);
      
      // Print UVM version and test info
      `uvm_info("TB_TOP", $sformatf("UVM Version: %s", uvm_revision_string()), UVM_LOW)
      `uvm_info("TB_TOP", "Starting AXI4-Lite UVM Testbench", UVM_LOW)
      
      // Run the test
      run_test();
   end
   
   //============================================================================
   // Timeout Watchdog
   //============================================================================
   
   initial begin
      #10ms;  // 10ms timeout
      `uvm_fatal("TB_TOP", "Test timeout - simulation exceeded 10ms")
   end
   
   //============================================================================
   // Final Block - Simulation Summary
   //============================================================================
   
   final begin
      `uvm_info("TB_TOP", "Simulation ended", UVM_LOW)
   end

endmodule : axi4lite_tb_top

