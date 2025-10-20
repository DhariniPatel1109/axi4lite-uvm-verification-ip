# AXI4-Lite UVM Verification Architecture

## Table of Contents

1. [Overview](#overview)
2. [UVM Component Hierarchy](#uvm-component-hierarchy)
3. [Transaction Class](#transaction-class)
4. [Agent Architecture](#agent-architecture)
5. [Scoreboard Design](#scoreboard-design)
6. [Coverage Model](#coverage-model)
7. [Sequence Library](#sequence-library)
8. [Test Structure](#test-structure)
9. [Interface and Assertions](#interface-and-assertions)

---

## Overview

This verification environment follows the standard UVM architecture pattern with a layered approach:

```
┌─────────────────────────────────────────────────┐
│              Test Layer                         │
│  (axi4lite_*_test extends base_test)           │
└────────────────┬────────────────────────────────┘
                 │
┌────────────────▼────────────────────────────────┐
│           Environment Layer                     │
│  • Agent (Sequencer + Driver + Monitor)        │
│  • Scoreboard (Reference Model)                │
│  • Coverage Collector                          │
└────────────────┬────────────────────────────────┘
                 │
┌────────────────▼────────────────────────────────┐
│         Transaction Layer                       │
│  (axi4lite_txn sequence_item)                  │
└────────────────┬────────────────────────────────┘
                 │
┌────────────────▼────────────────────────────────┐
│          Interface Layer                        │
│  (axi4lite_if with protocol assertions)        │
└─────────────────────────────────────────────────┘
```

---

## UVM Component Hierarchy

### Component Tree

```
uvm_test (axi4lite_base_test)
  │
  └── axi4lite_env
      │
      ├── axi4lite_agent (Active)
      │   │
      │   ├── axi4lite_sequencer
      │   │   └── Manages sequence flow
      │   │
      │   ├── axi4lite_driver
      │   │   └── Drives transactions to DUT
      │   │
      │   └── axi4lite_monitor
      │       └── Observes DUT behavior
      │
      ├── axi4lite_scoreboard
      │   └── Reference model + checking
      │
      └── axi4lite_coverage
          └── Functional coverage collection
```

---

## Transaction Class

### `axi4lite_txn`

The transaction class encapsulates a single AXI4-Lite operation.

**Key Fields:**
- `addr` [31:0] - Target address
- `data` [31:0] - Data payload
- `txn_type` - READ or WRITE
- `strb` [3:0] - Write byte strobes
- `prot` [2:0] - Protection attributes
- `resp` [1:0] - Response code (OKAY, SLVERR, etc.)

**Constraints:**
```systemverilog
constraint c_addr_align {
   addr[1:0] == 2'b00;  // Word-aligned
}

constraint c_addr_range {
   addr < 32*4;  // 32 registers
}
```

**Methods:**
- `convert2string()` - Human-readable format
- `resp_to_string()` - Decode response codes
- `do_copy()` - Deep copy support
- `do_compare()` - Comparison support

---

## Agent Architecture

### Driver (`axi4lite_driver`)

**Responsibilities:**
- Get transactions from sequencer
- Drive AXI4-Lite bus signals
- Handle handshaking protocol
- Capture responses

**Key Tasks:**
```systemverilog
drive_write(txn):
   1. Drive write address channel
   2. Drive write data channel (parallel)
   3. Wait for write response

drive_read(txn):
   1. Drive read address channel
   2. Wait for read data response
   3. Capture read data
```

**Features:**
- Automatic reset handling
- Timeout detection (100 cycles)
- Response error checking
- Parallel AW/W channel driving

### Monitor (`axi4lite_monitor`)

**Responsibilities:**
- Passively observe DUT signals
- Reconstruct completed transactions
- Broadcast to scoreboard and coverage

**Operation:**
```systemverilog
// Separate threads for read and write
fork
   collect_write_transactions();
   collect_read_transactions();
join
```

**Transaction Reconstruction:**
1. Detect address handshake (AWVALID & AWREADY)
2. Capture data handshake (WVALID & WREADY)
3. Capture response handshake (BVALID & BREADY)
4. Create complete transaction object
5. Broadcast via analysis port

### Sequencer (`axi4lite_sequencer`)

Standard UVM sequencer - no custom modifications needed.

---

## Scoreboard Design

### Reference Model

**Architecture:**
```
Monitor → Scoreboard → Check → Pass/Fail
                ↓
         Reference Memory
          (Associative Array)
```

**Memory Model:**
```systemverilog
bit [31:0] ref_memory [bit[31:0]];  // Sparse memory
```

**Write Processing:**
1. Update reference memory: `ref_memory[addr] = data`
2. Store in write history
3. Verify response is OKAY

**Read Processing:**
1. Get expected data from reference memory
2. Compare: `actual_data vs expected_data`
3. Report mismatch if different
4. Check response is OKAY

**Statistics Tracked:**
- Total writes
- Total reads
- Passed checks
- Failed checks (mismatches)

---

## Coverage Model

### Coverage Groups

#### 1. Transaction Coverage (`cg_axi4lite_transactions`)

**Coverpoints:**
- Transaction type (READ/WRITE)
- Address bins (register ranges)
- Data patterns (zeros, ones, random)
- Response codes
- Write strobes
- Inter-transaction delays

**Cross Coverage:**
- `txn_type × address`
- `txn_type × data_patterns`
- `write_strobes × address`

#### 2. Corner Cases (`cg_corner_cases`)

- Back-to-back transactions (delay = 0)
- Same address accessed consecutively
- Boundary addresses (first, last register)

#### 3. Protocol Coverage (`cg_protocol`)

- Protection type variations
- All AWPROT/ARPROT combinations

#### 4. RAW Scenarios (`cg_raw_scenarios`)

- Read-After-Write detection
- Hazard tracking

### Coverage Goals

| Metric | Target | Description |
|--------|--------|-------------|
| Transaction Coverage | 95%+ | All txn types, addresses, data |
| Corner Cases | 100% | Boundary conditions |
| Protocol Variations | 90%+ | Different protection modes |
| RAW Scenarios | 80%+ | Hazard detection |

---

## Sequence Library

### Base Sequence (`axi4lite_base_seq`)

Parent class for all sequences.

### Available Sequences

#### 1. **Reset Sequence**
- Waits for reset completion
- Used in test initialization

#### 2. **Single Write/Read Sequences**
- Atomic single-transaction operations
- Used for targeted testing

#### 3. **Write-Read Sequence**
```systemverilog
task body():
   write(addr, data);
   read(addr);  // Verify written data
```

#### 4. **Directed Sequence**
```systemverilog
// Test all 32 registers
for i = 0 to 31:
   write(i*4, pattern[i]);
for i = 0 to 31:
   read(i*4);
```

#### 5. **Random Sequence**
```systemverilog
repeat(10-50):  // Randomized count
   send(random_transaction);
```

#### 6. **Back-to-Back Sequence**
```systemverilog
repeat(20):
   send(txn with delay_cycles = 0);
```

#### 7. **Corner Case Sequence**
- All zeros data
- All ones data
- Alternating patterns (0xAAAAAAAA, 0x55555555)
- First and last registers

#### 8. **Stress Sequence**
- 500+ random transactions
- Maximum intensity testing

---

## Test Structure

### Base Test (`axi4lite_base_test`)

**Responsibilities:**
- Create environment
- Get virtual interface from config DB
- Set up UVM configuration
- Report final test status

### Derived Tests

#### Sanity Test
```systemverilog
run_phase():
   repeat(10) write_read_seq.start();
```

#### Directed Test
```systemverilog
run_phase():
   directed_seq.start();  // All registers
```

#### Random Test
```systemverilog
run_phase():
   repeat(5) random_seq.start();
```

#### Stress Test
```systemverilog
run_phase():
   back_to_back_seq.start();
   corner_case_seq.start();
   stress_seq.start();
```

---

## Interface and Assertions

### Interface Structure

```systemverilog
interface axi4lite_if(input clk, rst_n);
   // Signals
   logic [31:0] AWADDR, WDATA, ARADDR, RDATA;
   logic AWVALID, AWREADY, WVALID, WREADY;
   logic BVALID, BREADY, ARVALID, ARREADY;
   logic RVALID, RREADY;
   
   // Clocking blocks
   clocking driver_cb @(posedge clk);
      // Output/input specifications
   endclocking
   
   // Modports
   modport driver(...);
   modport monitor(...);
   
   // Protocol assertions
   property p_awvalid_stable;
      ...
   endproperty
endinterface
```

### Key Assertions

#### 1. VALID Stability
```systemverilog
(AWVALID && !AWREADY) |=> $stable(AWVALID)
```
Once asserted, VALID must stay high until READY.

#### 2. Response Ordering
```systemverilog
(AWVALID && AWREADY && WVALID && WREADY) |-> ##[1:10] BVALID
```
Write response must follow address and data phases.

#### 3. No X/Z Propagation
```systemverilog
!$isunknown(AWVALID)
```
VALID signals must be 0 or 1, never X or Z.

---

## Data Flow Diagram

```
┌─────────┐      ┌──────────┐      ┌─────┐      ┌─────────┐
│Sequence │─────▶│Sequencer │─────▶│ Drv │─────▶│   DUT   │
└─────────┘      └──────────┘      └─────┘      └────┬────┘
                                                       │
                              ┌────────────────────────┘
                              │
                              ▼
                        ┌──────────┐
                        │ Monitor  │
                        └─────┬────┘
                              │
                    ┌─────────┴─────────┐
                    │                   │
                    ▼                   ▼
              ┌────────────┐      ┌──────────┐
              │ Scoreboard │      │ Coverage │
              └────────────┘      └──────────┘
```

---

## Timing Diagram Example

### Write Transaction

```
CLK     : ┌─┐ ┌─┐ ┌─┐ ┌─┐ ┌─┐
          ─┘ └─┘ └─┘ └─┘ └─┘ └─

AWVALID : ───┐   ┌───────────────
          ───┘   └───────────────

AWREADY : ───────┐   ┌───────────
          ───────┘   └───────────

WVALID  : ───┐   ┌───────────────
          ───┘   └───────────────

WREADY  : ───────┐   ┌───────────
          ───────┘   └───────────

BVALID  : ───────────┐   ┌───────
          ───────────┘   └───────

BREADY  : ─────────────────────────
          ─────────────────────────
```

---

## Key Design Decisions

1. **Parallel AW/W Channels**: Driver drives both simultaneously for efficiency
2. **Associative Memory**: Scoreboard uses sparse memory for unlimited address space
3. **Separate Read/Write Monitors**: Independent threads prevent blocking
4. **Embedded Assertions**: Interface contains assertions for immediate violation detection
5. **Hierarchical Coverage**: Multiple coverage groups for granular analysis

---

## Extension Points

To extend this verification environment:

1. **Add new sequences**: Extend `axi4lite_base_seq`
2. **Add virtual sequences**: Coordinate multiple agents
3. **Add passive agents**: Monitor-only agents for other interfaces
4. **Enhanced coverage**: Add cross-coverage for complex scenarios
5. **Performance analysis**: Add latency/bandwidth measurements

