////////////////////////////////////////////////////////////////////////////////
// AXI4-Lite Transaction Class
// Defines the transaction item for AXI4-Lite read/write operations
////////////////////////////////////////////////////////////////////////////////

typedef enum bit { READ = 0, WRITE = 1 } axi4lite_txn_type_e;

class axi4lite_txn extends uvm_sequence_item;
   
   // Transaction fields
   rand bit [31:0]              addr;
   rand bit [31:0]              data;
   rand axi4lite_txn_type_e     txn_type;
   rand int unsigned            delay_cycles;  // Inter-transaction delay
   rand bit [2:0]               prot;          // Protection attributes
   rand bit [3:0]               strb;          // Write strobes
   
   // Response fields (filled by driver/monitor)
   bit [1:0]                    resp;          // BRESP or RRESP
   bit                          resp_error;
   
   // Timing info
   time                         start_time;
   time                         end_time;
   
   //============================================================================
   // Constraints
   //============================================================================
   
   // Reasonable delay between transactions
   constraint c_delay {
      delay_cycles inside {[0:5]};
      delay_cycles dist {0 := 40, [1:2] := 40, [3:5] := 20};
   }
   
   // Address should be word-aligned for 32-bit data
   constraint c_addr_align {
      addr[1:0] == 2'b00;
   }
   
   // Address within valid range (32 registers)
   constraint c_addr_range {
      addr < 32*4;  // 32 registers, 4 bytes each
   }
   
   // Default protection is unprivileged, secure, data access
   constraint c_prot_default {
      prot == 3'b000;
   }
   
   // Write strobes default to all lanes enabled
   constraint c_strb_default {
      strb == 4'b1111;
   }
   
   // Even distribution of reads and writes
   constraint c_txn_type_dist {
      txn_type dist {READ := 50, WRITE := 50};
   }
   
   //============================================================================
   // UVM Automation
   //============================================================================
   
   `uvm_object_utils_begin(axi4lite_txn)
      `uvm_field_int     (addr,         UVM_ALL_ON | UVM_HEX)
      `uvm_field_int     (data,         UVM_ALL_ON | UVM_HEX)
      `uvm_field_enum    (axi4lite_txn_type_e, txn_type, UVM_ALL_ON)
      `uvm_field_int     (delay_cycles, UVM_ALL_ON | UVM_DEC)
      `uvm_field_int     (prot,         UVM_ALL_ON | UVM_HEX)
      `uvm_field_int     (strb,         UVM_ALL_ON | UVM_BIN)
      `uvm_field_int     (resp,         UVM_ALL_ON | UVM_HEX)
      `uvm_field_int     (resp_error,   UVM_ALL_ON)
   `uvm_object_utils_end
   
   //============================================================================
   // Constructor
   //============================================================================
   
   function new(string name = "axi4lite_txn");
      super.new(name);
   endfunction
   
   //============================================================================
   // Methods
   //============================================================================
   
   // Convert transaction to string for display
   virtual function string convert2string();
      string s;
      s = $sformatf("TXN: %s | ADDR=0x%08h | DATA=0x%08h | STRB=0b%04b | RESP=%s",
                    txn_type.name(),
                    addr,
                    data,
                    strb,
                    resp_to_string(resp));
      return s;
   endfunction
   
   // Helper function to convert response code to string
   function string resp_to_string(bit [1:0] r);
      case (r)
         2'b00: return "OKAY";
         2'b01: return "EXOKAY";
         2'b10: return "SLVERR";
         2'b11: return "DECERR";
         default: return "UNKNOWN";
      endcase
   endfunction
   
   // Check if response indicates an error
   function bit is_error_response();
      return (resp[1] == 1'b1);  // SLVERR or DECERR
   endfunction
   
   // Deep copy
   virtual function void do_copy(uvm_object rhs);
      axi4lite_txn rhs_;
      if (!$cast(rhs_, rhs))
         `uvm_fatal(get_type_name(), "Cast failed in do_copy")
      super.do_copy(rhs);
      addr = rhs_.addr;
      data = rhs_.data;
      txn_type = rhs_.txn_type;
      delay_cycles = rhs_.delay_cycles;
      prot = rhs_.prot;
      strb = rhs_.strb;
      resp = rhs_.resp;
      resp_error = rhs_.resp_error;
      start_time = rhs_.start_time;
      end_time = rhs_.end_time;
   endfunction
   
   // Compare
   virtual function bit do_compare(uvm_object rhs, uvm_comparer comparer);
      axi4lite_txn rhs_;
      if (!$cast(rhs_, rhs)) begin
         `uvm_error(get_type_name(), "Cast failed in do_compare")
         return 0;
      end
      return (super.do_compare(rhs, comparer) &&
              (addr == rhs_.addr) &&
              (data == rhs_.data) &&
              (txn_type == rhs_.txn_type));
   endfunction

endclass : axi4lite_txn

