////////////////////////////////////////////////////////////////////////////////
// AXI4-Lite Interface with Protocol Assertions
// This interface includes all AXI4-Lite signals, clocking blocks, modports,
// and embedded SystemVerilog Assertions for protocol compliance checking
////////////////////////////////////////////////////////////////////////////////

interface axi4lite_if(input logic clk, input logic rst_n);
   
   // AXI4-Lite Write Address Channel
   logic [31:0]     AWADDR;
   logic [ 2:0]     AWPROT;
   logic            AWVALID;
   logic            AWREADY;
   
   // AXI4-Lite Write Data Channel
   logic [31:0]     WDATA;
   logic [ 3:0]     WSTRB;
   logic            WVALID;
   logic            WREADY;
   
   // AXI4-Lite Write Response Channel
   logic [1:0]      BRESP;
   logic            BVALID;
   logic            BREADY;
   
   // AXI4-Lite Read Address Channel
   logic [31:0]     ARADDR;
   logic [ 2:0]     ARPROT;
   logic            ARVALID;
   logic            ARREADY;
   
   // AXI4-Lite Read Data Channel
   logic [31:0]     RDATA;
   logic [ 1:0]     RRESP;
   logic            RVALID;
   logic            RREADY;

   //============================================================================
   // Clocking Blocks for Synchronous Driving/Sampling
   //============================================================================
   
   clocking driver_cb @(posedge clk);
      default input #1step output #1ns;
      output AWADDR, AWPROT, AWVALID;
      input  AWREADY;
      output WDATA, WSTRB, WVALID;
      input  WREADY;
      input  BRESP, BVALID;
      output BREADY;
      output ARADDR, ARPROT, ARVALID;
      input  ARREADY;
      input  RDATA, RRESP, RVALID;
      output RREADY;
   endclocking
   
   clocking monitor_cb @(posedge clk);
      default input #1step;
      input AWADDR, AWPROT, AWVALID, AWREADY;
      input WDATA, WSTRB, WVALID, WREADY;
      input BRESP, BVALID, BREADY;
      input ARADDR, ARPROT, ARVALID, ARREADY;
      input RDATA, RRESP, RVALID, RREADY;
   endclocking

   //============================================================================
   // Modports
   //============================================================================
   
   modport driver (clocking driver_cb, input clk, rst_n);
   modport monitor (clocking monitor_cb, input clk, rst_n);
   modport dut (
      input  AWADDR, AWPROT, AWVALID,
      output AWREADY,
      input  WDATA, WSTRB, WVALID,
      output WREADY,
      output BRESP, BVALID,
      input  BREADY,
      input  ARADDR, ARPROT, ARVALID,
      output ARREADY,
      output RDATA, RRESP, RVALID,
      input  RREADY,
      input  clk, rst_n
   );

   //============================================================================
   // SystemVerilog Assertions for Protocol Compliance
   //============================================================================
   
   // Assertion: AWVALID must remain stable until AWREADY is asserted
   property p_awvalid_stable;
      @(posedge clk) disable iff (!rst_n)
      (AWVALID && !AWREADY) |=> $stable(AWVALID) && $stable(AWADDR) && $stable(AWPROT);
   endproperty
   a_awvalid_stable: assert property(p_awvalid_stable)
      else $error("[ASSERTION FAILED] AWVALID/AWADDR must remain stable until handshake completes");
   
   // Assertion: WVALID must remain stable until WREADY is asserted
   property p_wvalid_stable;
      @(posedge clk) disable iff (!rst_n)
      (WVALID && !WREADY) |=> $stable(WVALID) && $stable(WDATA) && $stable(WSTRB);
   endproperty
   a_wvalid_stable: assert property(p_wvalid_stable)
      else $error("[ASSERTION FAILED] WVALID/WDATA must remain stable until handshake completes");
   
   // Assertion: BVALID must remain stable until BREADY is asserted
   property p_bvalid_stable;
      @(posedge clk) disable iff (!rst_n)
      (BVALID && !BREADY) |=> $stable(BVALID) && $stable(BRESP);
   endproperty
   a_bvalid_stable: assert property(p_bvalid_stable)
      else $error("[ASSERTION FAILED] BVALID/BRESP must remain stable until handshake completes");
   
   // Assertion: ARVALID must remain stable until ARREADY is asserted
   property p_arvalid_stable;
      @(posedge clk) disable iff (!rst_n)
      (ARVALID && !ARREADY) |=> $stable(ARVALID) && $stable(ARADDR) && $stable(ARPROT);
   endproperty
   a_arvalid_stable: assert property(p_arvalid_stable)
      else $error("[ASSERTION FAILED] ARVALID/ARADDR must remain stable until handshake completes");
   
   // Assertion: RVALID must remain stable until RREADY is asserted
   property p_rvalid_stable;
      @(posedge clk) disable iff (!rst_n)
      (RVALID && !RREADY) |=> $stable(RVALID) && $stable(RDATA) && $stable(RRESP);
   endproperty
   a_rvalid_stable: assert property(p_rvalid_stable)
      else $error("[ASSERTION FAILED] RVALID/RDATA must remain stable until handshake completes");
   
   // Assertion: Write response should come after both AW and W handshakes
   property p_write_response_order;
      @(posedge clk) disable iff (!rst_n)
      (AWVALID && AWREADY && WVALID && WREADY) |-> ##[1:10] BVALID;
   endproperty
   a_write_response_order: assert property(p_write_response_order)
      else $error("[ASSERTION FAILED] Write response (BVALID) should follow write address and data handshakes");
   
   // Assertion: Read data should come after AR handshake
   property p_read_data_after_address;
      @(posedge clk) disable iff (!rst_n)
      (ARVALID && ARREADY) |-> ##[1:10] RVALID;
   endproperty
   a_read_data_after_address: assert property(p_read_data_after_address)
      else $error("[ASSERTION FAILED] Read data (RVALID) should follow read address handshake");

   // Assertion: No X/Z on VALID signals during operation
   property p_no_x_on_awvalid;
      @(posedge clk) disable iff (!rst_n)
      !$isunknown(AWVALID);
   endproperty
   a_no_x_on_awvalid: assert property(p_no_x_on_awvalid)
      else $error("[ASSERTION FAILED] AWVALID has X/Z value");
   
   property p_no_x_on_wvalid;
      @(posedge clk) disable iff (!rst_n)
      !$isunknown(WVALID);
   endproperty
   a_no_x_on_wvalid: assert property(p_no_x_on_wvalid)
      else $error("[ASSERTION FAILED] WVALID has X/Z value");
   
   property p_no_x_on_arvalid;
      @(posedge clk) disable iff (!rst_n)
      !$isunknown(ARVALID);
   endproperty
   a_no_x_on_arvalid: assert property(p_no_x_on_arvalid)
      else $error("[ASSERTION FAILED] ARVALID has X/Z value");

   //============================================================================
   // Coverage for handshake scenarios
   //============================================================================
   
   covergroup cg_handshakes @(posedge clk);
      option.per_instance = 1;
      
      cp_aw_handshake: coverpoint (AWVALID && AWREADY) {
         bins occurred = {1};
      }
      
      cp_w_handshake: coverpoint (WVALID && WREADY) {
         bins occurred = {1};
      }
      
      cp_b_handshake: coverpoint (BVALID && BREADY) {
         bins occurred = {1};
      }
      
      cp_ar_handshake: coverpoint (ARVALID && ARREADY) {
         bins occurred = {1};
      }
      
      cp_r_handshake: coverpoint (RVALID && RREADY) {
         bins occurred = {1};
      }
   endgroup
   
   cg_handshakes cg_hs = new();

endinterface : axi4lite_if

