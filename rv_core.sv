import instructions::*;
import bus_if_types_pkg::*;

`define NOP 32'h00000013

// TODO: convert to enum
`include "funct3.sv" // funct3 encoded values in BRANCH and SYSTEM major opcodes

// Core with I-Bus interface and D-bus interface; both maybe connected with a crossbar
// but to avoid structural hazard, allow high performance SRAM to have dual ports
// TODO: make sure no race condition happens between always_ff and always_comb
module  rv_core #(parameter logic [31:0] INITIAL_PC) (
    // bus interfaces
    master_bus_if.master dbus,
    master_bus_if.master ibus,

    // clock and reset
    input bit clk,
    input bit rst_n,

    // debug access
    input bit haltreq = 1'b0,
    input bit resumereq = 1'b0,
    input bit resethaltreq = 1'b0,

    output bit halted, // if not one of those then it is changing state
    output bit running,

    input access_register_command_control_t dbg_arcc,
    input logic [31:0] dbg_rwrdata,
    output logic [31:0] dbg_regout,

    // interrupts from PLIC or timer or external
    input bit irq_sw = 1'b0,
    input bit irq_ext = 1'b0,
    input bit irq_timer = 1'b0
);

//-----------------------------------------------------------------------------
// Vital signals, hazard detection, flushing and stalling
//-----------------------------------------------------------------------------


privilege_t privilege;

logic hazard = 1'b0;
logic stall, stall_if_id, stall_id_ex, stall_ex_ma, bubble_instruction, bubble_if_id, bubble_id_ex, bubble_ex_ma, bubble_ma_wb; // due to hazards or memory delay
logic flush, control_hazard; // if jump or branch was taken

assign flush = control_hazard | interrupt | return_from_interrupt | return_from_dbg;

always_ff @(negedge clk or negedge rst_n) begin
    if (!rst_n) begin
        control_hazard <= 0;
    end else begin
        case(ma_wb.instruction[6:2])
            BRANCH: begin 
                control_hazard <= ma_wb.branch;
            end
            JALR: begin
                control_hazard <= 1'b1;
            end
            JAL: begin
                control_hazard <= 1'b1;
            end
            default: control_hazard <= 1'b0;
        endcase
    end
end

//-----------------------------------------------------------------------------
// Debuging
//-----------------------------------------------------------------------------

enum logic [2:0] {RESET, NORMAL, HALTING, HALTED, RESUMING} hstate, next_hstate; // hart state for DM

always_ff @(posedge clk, negedge rst_n) begin
    if (!rst_n)
        hstate <= RESET;
    else begin
        hstate <= next_hstate;
    end
end


always_comb begin
    halted = hstate == HALTED;
    running = hstate == NORMAL;
    dbg_regout = rf_r1;
    
    case(hstate)
        RESET: next_hstate = resethaltreq ? HALTED : NORMAL;
        NORMAL: next_hstate = haltreq ? HALTING : (wb_dbg_step ? HALTED : NORMAL); // added to the FSM in the spec
        HALTING: next_hstate = (1'b1) ? HALTED : NORMAL; // no need to wait for halting. (originally halt next after writing back (IF phase))
        HALTED: next_hstate = resumereq ? RESUMING : HALTED; // for fsm to be like DM spec
        RESUMING: next_hstate = NORMAL;
        default: next_hstate = NORMAL;
    endcase
end

//-----------------------------------------------------------------------------
// Interrupts and Traps
//-----------------------------------------------------------------------------

logic sync_int;
logic async_int;
logic dbg_int;
logic [8:6] dbg_cause;

logic interrupt, return_from_interrupt, return_from_dbg;

always_comb return_from_dbg = (hstate == RESUMING);

logic [31:0] pc_to_store;
mcause_t mcause_to_store;

always_comb begin
    dbg_cause = hstate == HALTING ? 3 : (wb_dbg_step ? 4 : 0);
end

always_ff @(negedge clk) begin
    return_from_interrupt = ma_wb.mret; // higher priority // only signal return_from_interrupt when really 
    interrupt = 0;
    mcause_to_store = 0;
    pc_to_store = 0;
    sync_int =  ma_wb.ecall | ma_wb.illegal_instruction;
    async_int = (irq_ext | mip.MEIP) | (irq_timer | mip.MTIP) | (irq_sw | mip.MSIP);
    dbg_int = hstate == HALTING | wb_dbg_step; // explicit debug halt request or single stepping not masked
    
    if (sync_int) begin
        pc_to_store = ibus.addr; // gauranteed as ECALL or Illegal Instrcution are only one in pipeline
        // instructuion_pc may be bubbled take ibus.addr always correct next fetch
    end else if (async_int | dbg_int)
        pc_to_store = ma_wb.pc != 0 ? ma_wb.pc : (ex_ma.pc != 0 ? ex_ma.pc : (id_ex.pc != 0 ? id_ex.pc : (if_id.pc != 0 ? if_id.pc : ibus.addr)));

    if (mstatus.MIE) begin
        if (sync_int) begin
            interrupt = 1'b1;
            mcause_to_store.interr = 0;

            mcause_to_store.code = ma_wb.ecall ? 11 : 2; // 11 and 2 from the spec
        end else if (async_int) begin
            interrupt = 1'b1;
            mcause_to_store.interr = 1;

            if ((irq_ext | mip.MEIP) && mie.MEIE)
                mcause_to_store.code = 11;
            else if ((irq_timer | mip.MTIP) && mie.MTIE)
                mcause_to_store.code = 7;
            else if ((irq_sw | mip.MSIP) && mie.MSIE)    
                mcause_to_store.code = 3;
        end
    end
end

//-----------------------------------------------------------------------------
// PC and I-bus interface
//-----------------------------------------------------------------------------

logic [31:0] pc;

typedef enum logic [1:0] {IDLE, START, DELAY, ONGOING} bus_state_e;

bus_state_e ibus_state;
bus_state_e dbus_state, next_dbus_state;

// TODO: pipeline the bus!
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
        ibus_state <= ONGOING;
    else
        case(ibus_state)
            ONGOING: ibus_state <= ibus.bdone ? ((flush || (!bubble_instruction && !stall_if_id)) ? ONGOING : IDLE) : ONGOING;
            IDLE: ibus_state <= (flush || (!bubble_instruction && !stall_if_id)) ? ONGOING : IDLE;
        endcase
end

// TODO: make sure we read after outputting address! (will fail in peripherals outputting in same cycle!)
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
        dbus_state <= IDLE;
    else
        dbus_state <= next_dbus_state;
end

logic dbus_transaction_finished;
always_comb begin
    dbus.bstart = dbus_state == START;
    dbus_transaction_finished = (dbus_state == DELAY) | ((dbus_state == ONGOING) && dbus.bdone);
end

logic start_dbus_transaction;
assign start_dbus_transaction = ex_ma.mem_wr | ex_ma.mem_rd;

always_comb begin
    case(dbus_state)
        IDLE: next_dbus_state =  start_dbus_transaction ? START : IDLE;
        START: next_dbus_state = dbus.bdone ? DELAY : ONGOING;
        DELAY: next_dbus_state = IDLE;
        ONGOING: next_dbus_state = dbus.bdone ? IDLE : ONGOING;
    endcase
end

always_comb begin
    ibus.bstart = 1; // Always keep fetching instructions until pipeline flush
    ibus.breq = 1'b1;
    ibus.ttype = READ;
    ibus.tsize = WORD;
    ibus.wdata = 32'b0;
end

always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        ibus.addr <= INITIAL_PC;
    end     
    else if (return_from_interrupt)
        ibus.addr <= mepc;
    else if (return_from_dbg)
        ibus.addr <= dpc;
    else if (interrupt)
        ibus.addr <= {mtvec.base, 2'b00};
    else if (control_hazard)
        ibus.addr <= ma_wb.next_pc; // must fetch from that instruction (discarding all that entered pipeline)
    else if (!bubble_instruction && !stall_if_id) begin
        ibus.addr <= ibus.addr + 4; // assume branches are not taken, includes (unconditional jumps) and let the pipeline flush when it has to
    end
end


always_comb begin
    if (!bubble_instruction) begin
        instruction = ibus.rdata;
        instruction_pc = ibus.addr;
    end else begin
        instruction = `NOP;
        instruction_pc = 0;
    end
end

logic [31:0] instruction, instruction_pc;


//-----------------------------------------------------------------------------
// Pipeline stage definitions
//-----------------------------------------------------------------------------

// TODO: use modports with interfaces if this makes it more readible

struct packed {
    logic [31:0] instruction;
    logic [31:0] pc;

    // FATAL: only flag when it reaches ma_wb, pipeline still has instructions!
    logic illegal_instruction;
    logic wfi;
    logic ecall;
    logic mret;

    // intrinsic
    logic [4:0] rf_rs1;
    logic [4:0] rf_rs2;
    logic [4:0] rf_rd;

    // control
    logic rf_wr;
    logic mem_wr;
    logic mem_rd;
    logic csr_wr;
    logic [2:0] alu_funct3;
    logic [6:0] alu_funct7;
    tsize_e tsize;

    // debug
    logic step;
} if_id;

struct packed {
    logic [31:0] instruction;
    logic [31:0] pc;

    logic [2:0] alu_funct3;
    logic [6:0] alu_funct7;
    logic [31:0] rf_r1;
    logic [31:0] rf_r2;

    // passed from CU
    tsize_e tsize;
    logic rf_wr;
    logic [4:0] rf_rd;
    logic mem_wr;
    logic mem_rd;
    logic csr_wr;

    // flags
    logic illegal_instruction;
    logic wfi;
    logic ecall;
    logic mret;
    logic step;
} id_ex;

struct packed {
    logic [31:0] instruction;
    logic [31:0] pc;

    // passed
    logic [31:0] rf_r1;
    logic csr_wr;
    logic rf_wr;
    logic [4:0] rf_rd;

    
    // intrinsic
    logic [31:0] rf_r2;
    logic [31:0] mem_addr;
    tsize_e tsize;
    logic mem_rd;
    logic mem_wr;
    logic [31:0] csr_read;
    logic [31:0] alu_out;
    logic alu_out_c;
    logic alu_out_n;
    logic alu_out_overflow;
    logic alu_out_z;
    logic branch;

    // flags
    logic illegal_instruction;
    logic wfi;
    logic ecall;
    logic mret;
    logic step;
} ex_ma;

struct packed {
    logic [31:0] instruction;
    logic [31:0] pc;

    // passed
    logic [31:0] alu_out;
    logic [31:0] csr_read;
    logic branch;

    // intrinsic
    logic [31:0] mem_rdata;
    logic [4:0] rf_rd;
    logic rf_wr;
    logic csr_wr;
    logic [31:0] csr_wrdata;
    logic [31:0] next_pc;

    // flags
    logic illegal_instruction;
    logic wfi;
    logic ecall;
    logic mret;
    logic step;
} ma_wb;

logic wb_dbg_step;

//-----------------------------------------------------------------------------
// Interconnections and type casts
//-----------------------------------------------------------------------------

rtype rtype_i;
itype itype_i;
stype stype_i;
btype btype_i;
utype utype_i;
jtype jtype_i;

itype if_id_itype_i;
itype id_ex_itype_i;
btype id_ex_btype_i;

jtype ex_ma_jtype_i;
btype ex_ma_btype_i;
itype ex_ma_itype_i;
stype id_ex_stype_i;

itype ma_wb_itype_i;

itype wb_itype_i;
utype wb_utype_i;

always_comb begin
    rtype_i = instruction;
    itype_i = instruction;
    stype_i = instruction;
    btype_i = instruction;
    utype_i = instruction;
    jtype_i = instruction;

    if_id_itype_i = if_id.instruction;

    id_ex_btype_i = id_ex.instruction;
    id_ex_stype_i = id_ex.instruction;
    id_ex_itype_i = id_ex.instruction;

    ex_ma_btype_i = ex_ma.instruction;
    ex_ma_jtype_i = ex_ma.instruction;
    ex_ma_itype_i = ex_ma.instruction;

    ma_wb_itype_i = ma_wb.instruction;

    wb_itype_i = ma_wb.instruction;
    wb_utype_i = ma_wb.instruction;
end


logic [6:0] opcode;

logic [31:0] alu_out;
logic [31:0] rf_wrdata, rf_r1, rf_r2;
logic alu_out_c, alu_out_z, alu_out_n, alu_out_overflow;

//-----------------------------------------------------------------------------
// Exposed CSRs
//-----------------------------------------------------------------------------

logic [31:0] mepc, dpc;
mstatus_t mstatus;
mtvec_t mtvec;
mcause_t mcause;
mip_t mip;
mie_t mie;

// Output
logic [31:0] csr_read;


//-----------------------------------------------------------------------------
// Data Forwarding
//-----------------------------------------------------------------------------

logic [31:0] correct_rf_r1, correct_rf_r2;

logic rf_r1_hazard, rf_r2_hazard, can_forward_rf_r1, can_forward_rf_r2;

always_comb begin
    can_forward_rf_r1 = 0;
    rf_r1_hazard = 1'b0;
    can_forward_rf_r2 = 0;
    rf_r2_hazard = 1'b0;
    correct_rf_r1 = rf_r1;
    correct_rf_r2 = rf_r2;

    // steal signals
    if (if_id.rf_rs1 == id_ex.rf_rd && id_ex.rf_rd != 5'b0)
        rf_r1_hazard = 1'b1;
    else if (if_id.rf_rs1 == ex_ma.rf_rd && ex_ma.rf_rd != 5'b0) begin // steal if only from alu
        rf_r1_hazard = 1'b1;
        if (ex_ma.instruction[6:2] inside {OP, OP_IMM}) begin
            can_forward_rf_r1 = 1'b1;
            correct_rf_r1 = ex_ma.alu_out;
        end
    end else if (if_id.rf_rs1 == ma_wb.rf_rd && ma_wb.rf_rd != 5'b0) begin //
        rf_r1_hazard = 1'b1;
        can_forward_rf_r1 = 1'b1;
        correct_rf_r1 = rf_wrdata; // steal
    end

    if (if_id.rf_rs2 == id_ex.rf_rd && id_ex.rf_rd != 5'b0)
        rf_r2_hazard = 1'b1;
    else if (if_id.rf_rs2 == ex_ma.rf_rd && ex_ma.rf_rd != 5'b0) begin // steal if only from alu
        rf_r2_hazard = 1'b1;
        if (ex_ma.instruction[6:2] inside {OP, OP_IMM}) begin
            correct_rf_r2 = ex_ma.alu_out;
            can_forward_rf_r2 = 1'b1;
        end
    end else if (if_id.rf_rs2 == ma_wb.rf_rd && ma_wb.rf_rd != 5'b0) begin
        rf_r2_hazard = 1'b1;
        correct_rf_r2 = rf_wrdata; // steal
        can_forward_rf_r2 = 1'b1;
    end 
end

//-----------------------------------------------------------------------------
// Hazard Detection
//-----------------------------------------------------------------------------

// next clock edge
always_comb begin
    // TODO: make sure instruction entering pipeline is ok
    stall =  (ma_wb.wfi && !interrupt) | (hstate != NORMAL); // WFI and Core Debug

    stall_if_id = stall;
    stall_id_ex = stall;
    stall_ex_ma = stall;
    
    bubble_instruction = (ibus_state != IDLE);
    bubble_if_id = 0; // TODO: pipeline it!
    bubble_id_ex = 0;
    bubble_ex_ma = 0;
    bubble_ma_wb = start_dbus_transaction && !dbus_transaction_finished; // TODO: make sure at least lasts 1 more instruction to latch output (in a more cleaner way)
    
    // stall if the pipeline have any SYSTEM instruction (atomic and effects CSR module) TODO: implement data forwarding or more fine stalls (hard)
    // fallback to multicycle mode
    if (if_id.instruction[6:2] == SYSTEM || id_ex.instruction[6:2] == SYSTEM || ex_ma.instruction[6:2] == SYSTEM || ma_wb.instruction[6:2] == SYSTEM)
        bubble_instruction = 1'b1;    

    // stall if pipeline has an illegal instruction
    if (if_id.illegal_instruction || id_ex.illegal_instruction || ex_ma.illegal_instruction || ma_wb.illegal_instruction)
        bubble_instruction = 1'b1;    

    // stall if can't data forward
    if ((rf_r1_hazard && !can_forward_rf_r1) || (rf_r2_hazard && !can_forward_rf_r2))
        bubble_id_ex = 1'b1; // next id_ex is bubbled

    stall_ex_ma = stall_ex_ma | bubble_ma_wb;
    stall_id_ex = stall_id_ex | stall_ex_ma | bubble_ex_ma;
    stall_if_id = stall_if_id | stall_id_ex | bubble_id_ex;
end

//-----------------------------------------------------------------------------
// D-bus interface
//-----------------------------------------------------------------------------

always_comb begin
    dbus.wdata = ex_ma.rf_r2; // always writing from data in register
    // dbus.bstart = ; handle by FSM
    dbus.ttype = ex_ma.mem_wr ? WRITE : READ;
    dbus.breq = dbus.bstart; // TODO: breq and bstart are same? either have clear sepearion in logic or collapse into one
    dbus.addr = ex_ma.mem_addr;
    dbus.tsize = ex_ma.tsize;
end

//-----------------------------------------------------------------------------
// Major Op-codes
//-----------------------------------------------------------------------------

typedef enum logic [4:0] {
    LOAD        = 5'b00000,
    LOAD_FP     = 5'b00001,
    custom_0    = 5'b00010,
    MISC_MEM    = 5'b00011,
    OP_IMM      = 5'b00100,
    AUIPC       = 5'b00101,
    OP_IMM_32   = 5'b00110,
    STORE       = 5'b01000,
    STORE_FP    = 5'b01001,
    custom_1    = 5'b01010,
    AMO         = 5'b01011,
    OP          = 5'b01100,
    LUI         = 5'b01101,
    OP_32       = 5'b01110,
    MADD        = 5'b10000,
    MSUB        = 5'b10001,
    NMSUB       = 5'b10010,
    NMADD       = 5'b10011,
    OP_FP       = 5'b10100,
    OP_V        = 5'b10101,
    custom_2    = 5'b10110,
    BRANCH      = 5'b11000,
    JALR        = 5'b11001,
    // reserved = 5'b11010,
    JAL         = 5'b11011,
    SYSTEM      = 5'b11100,
    OP_VE       = 5'b11101,
    custom_3    = 5'b11110
} mopcode_t;

//-----------------------------------------------------------------------------
// IF/ID (input instruction)
//-----------------------------------------------------------------------------

always_comb begin
    opcode = instruction[6:0];
end

always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n || flush)
        if_id <= 0;
    else if (stall_if_id)
        if_id <= if_id;
    else if (bubble_if_id)
        if_id <= 0;
    else begin
        if_id <= '0; // zero out everything
        if_id.step <= dcsr.step; // from debug csr
        if_id.instruction <= instruction; // combinational, preserve in stall
        if_id.pc <= instruction_pc;
        if (opcode[1:0] == 2'b11)
            case(opcode[6:5])
                2'b00:
                    case(opcode[4:2])
                        3'b000: begin // LOAD
                            assert (mopcode_t'(opcode[6:2]) == LOAD);
                            if_id.rf_rd <= itype_i.rd;
                            if_id.rf_rs1 <= itype_i.rs1;
                            
                            if_id.rf_wr <= 1'b1;
                            
                            if_id.tsize <= tsize_e'(itype_i.funct3[14:12]); // by ISA

                            if_id.mem_rd <= 1'b1;
                            
                        end
                        //3'b001: assert (mopcode_t'(opcode[6:2]) == LOAD_FP); // LOAD-FP
                        //3'b010: assert (mopcode_t'(opcode[6:2]) == custom_0); // custom-0
                        //3'b011: assert (mopcode_t'(opcode[6:2]) == MISC_MEM); // MISC-MEM
                        3'b100: begin // OP-IMM
                            assert (mopcode_t'(opcode[6:2]) == OP_IMM);
                            if_id.rf_rd <= itype_i.rd;
                            if_id.rf_rs1 <= itype_i.rs1;
                            if_id.rf_wr <= 1'b1;
                            if_id.alu_funct3 <= itype_i.funct3;
                            if_id.alu_funct7 <= itype_i.funct3 == 3'b101 ? itype_i.imm[31:25] : 7'b0;
                        end
                        3'b101: begin // AUIPC
                            assert (mopcode_t'(opcode[6:2]) == AUIPC);
                            if_id.rf_wr <= 1'b1;
                            if_id.rf_rd <= utype_i.rd;
                        end
                        3'b110: assert (mopcode_t'(opcode[6:2]) == OP_IMM_32); // OP-IMM-32
                        default: if_id.illegal_instruction <= 1;
                    endcase
                2'b01:
                    case(opcode[4:2])
                        3'b000: begin // STORE
                            assert (mopcode_t'(opcode[6:2]) == STORE);
                            if_id.rf_rs1 <= stype_i.rs1;
                            if_id.rf_rs2 <= stype_i.rs2;
        
                            if_id.mem_wr <= 1'b1;
                            

                            if_id.tsize <= tsize_e'(stype_i.funct3[14:12]);
                        end
                        //3'b001: assert (mopcode_t'(opcode[6:2]) == STORE_FP); // STORE-FP
                        //3'b010: assert (mopcode_t'(opcode[6:2]) == custom_1); // custom-1
                        //3'b011: assert (mopcode_t'(opcode[6:2]) == AMO); // AMO
                        3'b100: begin // OP
                            assert (mopcode_t'(opcode[6:2]) == OP);
                            if_id.rf_rd <= rtype_i.rd;
                            if_id.rf_rs1 <= rtype_i.rs1;
                            if_id.rf_rs2 <= rtype_i.rs2;
                            if_id.rf_wr <= 1'b1;
                            
                            if_id.alu_funct3 <= rtype_i.funct3;
                            if_id.alu_funct7 <= rtype_i.funct7;
                        end
                        3'b101: begin // LUI
                            assert (mopcode_t'(opcode[6:2]) == LUI);
                            if_id.rf_wr <= 1'b1;
                            if_id.rf_rd <= utype_i.rd;
                        end
                        //3'b110: assert (mopcode_t'(opcode[6:2]) == OP_32); // OP-32
                        default: if_id.illegal_instruction <= 1;
                    endcase
                2'b10:
                    case(opcode[4:2])
                        //3'b000: assert (mopcode_t'(opcode[6:2]) == MADD); // MADD
                        //3'b001: assert (mopcode_t'(opcode[6:2]) == MSUB); // MSUB
                        //3'b010: assert (mopcode_t'(opcode[6:2]) == NMSUB); // NMSUB
                        //3'b011: assert (mopcode_t'(opcode[6:2]) == NMADD); // NMADD
                        //3'b100: assert (mopcode_t'(opcode[6:2]) == OP_FP); // OP-FP
                        //3'b101: assert (mopcode_t'(opcode[6:2]) == OP_V); // OP-V
                        //3'b110: assert (mopcode_t'(opcode[6:2]) == custom_2); // custom-2/RV128
                        default: if_id.illegal_instruction <= 1;
                    endcase
                2'b11:
                    case(opcode[4:2])
                        3'b000: begin // BRANCH                     
                            assert (mopcode_t'(opcode[6:2]) == BRANCH);
                            if_id.rf_rs1 <= btype_i.rs1;
                            if_id.rf_rs2 <= btype_i.rs2;
                            if_id.alu_funct7 <= 7'b0100000; // subtract
                            if_id.alu_funct3 <= 3'b000; // subtract
                        end
                        3'b001: begin // JALR
                            assert (mopcode_t'(opcode[6:2]) == JALR);
                            if_id.rf_rs1 <= itype_i.rs1;
                            if_id.rf_rd <= itype_i.rd;
                            if_id.rf_wr <= 1'b1;
                        end
                        //3'b010: ; // reserved
                        3'b011: begin // JAL
                            assert (mopcode_t'(opcode[6:2]) == JAL);
                            if_id.rf_rd <= jtype_i.rd;
                            if_id.rf_wr <= 1'b1;
                        end
                        3'b100: begin // SYSTEM
                            // Ensured in Hazard Detection Unit only 1 instruction exists, no other instruction in pipeline
                            assert (mopcode_t'(opcode[6:2]) == SYSTEM);
                            if (itype_i.funct3 inside {`CSRRW, `CSRRS, `CSRRC, `CSRRWI, `CSRRSI, `CSRRCI}) begin
                                if_id.rf_wr <= 1;
                                if_id.rf_rd <= itype_i.rd;
                                if_id.rf_rs1 <= itype_i.rs1;

                                // zero extend csr_addr

                                case(itype_i.funct3)
                                    `CSRRW: begin
                                        if_id.csr_wr <= 1;
                                    end
                                    `CSRRS: begin
                                        if_id.csr_wr <= itype_i.rs1 != 0;
                                    end
                                    `CSRRC: begin
                                        if_id.csr_wr <= itype_i.rs1 != 0;
                                    end
                                    `CSRRWI: begin
                                        if_id.csr_wr <= 1;
                                    end
                                    `CSRRSI: begin
                                        if_id.csr_wr <= itype_i.rs1 != 0;
                                    end
                                    `CSRRCI: begin
                                        if_id.csr_wr <= itype_i.rs1 != 0;
                                    end
                                    default: if_id.illegal_instruction <= 1;
                                endcase
                            end else if (itype_i.funct3 == 3'b000) begin
                                case(itype_i.imm)
                                    12'b000000000000: begin // ECALL
                                        if_id.ecall <= 1'b1;
                                    end
                                    12'b000000000001: begin // EBREAK
                                    end
                                    12'b000100000010: begin // SRET
                                    end
                                    12'b001100000010: begin // MRET
                                        if_id.mret <= 1'b1;
                                    end
                                    12'b000100000101: begin // WFI
                                        if_id.wfi <= 1'b1;
                                    end
                                    default: if_id.illegal_instruction <= 1;
                                endcase
                            end
                        end
                        //3'b101: assert (mopcode_t'(opcode[6:2]) == OP_VE); // OP-VE
                        //3'b110: assert (mopcode_t'(opcode[6:2]) == custom_3); // custom-3/RV128
                        default: if_id.illegal_instruction <= 1;
                    endcase
                    default: if_id.illegal_instruction <= 1;
            endcase
    end
end

//-----------------------------------------------------------------------------
// ID/EX (input IF/ID)
//-----------------------------------------------------------------------------

always_ff @(posedge clk or negedge rst_n)
    if (!rst_n || flush)
        id_ex <= 0;
    else if (stall_id_ex)
        id_ex <= id_ex;
    else if (bubble_id_ex)
        id_ex <= 0;
    else begin
        id_ex <= '0;
        id_ex.step <= if_id.step;
        id_ex.instruction <= if_id.instruction;
        id_ex.pc <= if_id.pc;
        id_ex.alu_funct3 <= if_id.alu_funct3;
        id_ex.alu_funct7 <= if_id.alu_funct7;
        id_ex.tsize <= if_id.tsize;
        id_ex.rf_r1 <= correct_rf_r1;
        id_ex.rf_r2 <= correct_rf_r2;
        id_ex.rf_wr <= if_id.rf_wr;
        id_ex.rf_rd <= if_id.rf_rd;
        id_ex.mem_wr <= if_id.mem_wr;
        id_ex.mem_rd <= if_id.mem_rd;
        id_ex.csr_wr <= if_id.csr_wr;

        // flags
        id_ex.illegal_instruction <= if_id.illegal_instruction;
        id_ex.wfi <= if_id.wfi;
        id_ex.ecall <= if_id.ecall;
        id_ex.mret <= if_id.mret;
    end


//-----------------------------------------------------------------------------
// EX/MA (input ID/EX)
//-----------------------------------------------------------------------------

// input ALU, CSR
// memory access address, branching, alu, csr
// TODO: use ALU if free to calculate
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n || flush) // if bubble, need to recalculate
        ex_ma <= 0;
    else if (stall_ex_ma)
        ex_ma <= ex_ma;
    else if (bubble_ex_ma)
        ex_ma <= 0;
    else begin
        ex_ma <= '0;
        ex_ma.step <= id_ex.step;
        ex_ma.rf_r1 <= id_ex.rf_r1;
        ex_ma.rf_r2 <= id_ex.rf_r2;
        ex_ma.alu_out <= alu_out;
        ex_ma.csr_read <= csr_read;
        ex_ma.instruction <= id_ex.instruction;
        ex_ma.tsize <= id_ex.tsize;
        ex_ma.pc <= id_ex.pc;

        ex_ma.mem_rd <= id_ex.mem_rd;
        ex_ma.mem_wr <= id_ex.mem_wr;
        ex_ma.rf_wr <= id_ex.rf_wr;
        ex_ma.rf_rd <= id_ex.rf_rd;
        ex_ma.csr_wr <= id_ex.csr_wr;

        // flags
        ex_ma.illegal_instruction <= id_ex.illegal_instruction;
        ex_ma.wfi <= id_ex.wfi;
        ex_ma.ecall <= id_ex.ecall;
        ex_ma.mret <= id_ex.mret;

        if (id_ex.instruction[6:2] == BRANCH)
            case(id_ex_btype_i.funct3)
                3'b000: ex_ma.branch <= (alu_out_z); // BEQ
                3'b001: ex_ma.branch <= !(alu_out_z); // BNEQ
                3'b100: ex_ma.branch <= (alu_out_n ^ alu_out_overflow); // BLT
                3'b101: ex_ma.branch <= !(alu_out_n ^ alu_out_overflow); // BGE
                3'b110: ex_ma.branch <= !alu_out_c; // BLTU
                3'b111: ex_ma.branch <= alu_out_c; // BGEU
            endcase

        case(id_ex.instruction[6:2])
            LOAD: ex_ma.mem_addr <= id_ex.rf_r1 + $signed({{20{id_ex_itype_i.imm[31]}}, id_ex_itype_i.imm});
            STORE: ex_ma.mem_addr <= id_ex.rf_r1 + $signed({{20{id_ex_stype_i.imm_b11_5[31]}},id_ex_stype_i.imm_b11_5, id_ex_stype_i.imm_b4_0});
            default: ex_ma.mem_addr <= 32'b0;
        endcase
    end
end


//-----------------------------------------------------------------------------
// MA/WB (input EX/MA)
//-----------------------------------------------------------------------------

// pc write and memory read and CSRs
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n || flush) // all stages are flushed, notice the last ma_wb was a branch or jump so the moved in instruction is fake
        ma_wb <= 0;
    //else if (bubble_ma_wb) degenerate bubble, need to obtain dbus.rdata, rely on stalling ex_ma TODO: rename to `recalculate`
    //    ma_wb <= 0;
    else begin
        ma_wb <= '0;
        ma_wb.step <= ex_ma.step;
        ma_wb.instruction <= ex_ma.instruction;
        ma_wb.pc <= ex_ma.pc;
        ma_wb.branch <= ex_ma.branch;
        ma_wb.alu_out <= ex_ma.alu_out;
        ma_wb.csr_read <= ex_ma.csr_read;
        ma_wb.rf_rd <= ex_ma.rf_rd;
        ma_wb.rf_wr <= ex_ma.rf_wr;
        ma_wb.csr_wr <= ex_ma.csr_wr;
        ma_wb.mem_rdata <= dbus.rdata; // TODO: who said it was ready?

        // flags
        ma_wb.illegal_instruction <= ex_ma.illegal_instruction;
        ma_wb.wfi <= ex_ma.wfi;
        ma_wb.ecall <= ex_ma.ecall;
        ma_wb.mret <= ex_ma.mret;

        if(ex_ma.instruction[6:2] == SYSTEM)
            case(ex_ma_itype_i.funct3)
                `CSRRW: begin
                    ma_wb.csr_wrdata <= ex_ma.rf_r1;
                end
                `CSRRS: begin
                    ma_wb.csr_wrdata <= ex_ma.csr_read | ex_ma.rf_r1;
                end
                `CSRRC: begin
                    ma_wb.csr_wrdata <= ex_ma.csr_read & (~ex_ma.rf_r1);
                end
                `CSRRWI: begin
                    ma_wb.csr_wrdata <= {27'b0, ex_ma_itype_i.rs1};
                end
                `CSRRSI: begin
                    ma_wb.csr_wrdata <= ex_ma.csr_read | {27'b0, ex_ma_itype_i.rs1};
                end
                `CSRRCI: begin
                    ma_wb.csr_wrdata <= ex_ma.csr_read & ~({27'b0, ex_ma_itype_i.rs1});
                end
            endcase

        case(ex_ma.instruction[6:2])
            BRANCH: begin 
                if (ex_ma.branch)
                    ma_wb.next_pc <= ex_ma.pc + $signed({{19{ex_ma_btype_i.imm_b12}}, ex_ma_btype_i.imm_b12, ex_ma_btype_i.imm_b11, ex_ma_btype_i.imm_b10_5, ex_ma_btype_i.imm_b4_1, 1'b0});
                else
                    ma_wb.next_pc <= ex_ma.pc + 4; // default
            end
            JALR: begin
                ma_wb.next_pc <= ($signed({{20{ex_ma_itype_i.imm[31]}}, ex_ma_itype_i.imm}) + ex_ma.rf_r1) & 32'hfffffffe;
            end
            JAL: begin
                ma_wb.next_pc <= ex_ma.pc + $signed({{11{ex_ma_jtype_i.imm_b20}}, ex_ma_jtype_i.imm_b20, ex_ma_jtype_i.imm_b19_12, ex_ma_jtype_i.imm_b11, ex_ma_jtype_i.imm_b10_1, 1'b0});
            end
            default: ma_wb.next_pc <= ex_ma.pc + 4;
        endcase
    end
end

//-----------------------------------------------------------------------------
// WB (input MA/WB)
//-----------------------------------------------------------------------------

always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
        wb_dbg_step <= 0;
    else begin
        wb_dbg_step <= ma_wb.step;
    end
end

// register file write
always_comb
    case(ma_wb.instruction[6:2])
        LOAD: 
            case(wb_itype_i.funct3)
                3'b000: rf_wrdata = {{24{ma_wb.mem_rdata[7]}}, ma_wb.mem_rdata[7:0]}; // LB
                3'b001: rf_wrdata = {{16{ma_wb.mem_rdata[15]}}, ma_wb.mem_rdata[15:0]}; // LH
                3'b010: rf_wrdata = ma_wb.mem_rdata; // LW
                3'b100: rf_wrdata = {{24{1'b0}}, ma_wb.mem_rdata[7:0]}; // LBU
                3'b101: rf_wrdata = {{16{ma_wb.mem_rdata[15]}}, ma_wb.mem_rdata[15:0]}; // LHU
                default: rf_wrdata = 32'b0;
            endcase
        OP_IMM: rf_wrdata = ma_wb.alu_out;
        AUIPC: rf_wrdata = {wb_utype_i.imm, {12{1'b0}}} + ma_wb.pc;
        OP: rf_wrdata = ma_wb.alu_out;
        LUI: rf_wrdata = {wb_utype_i.imm, {12{1'b0}}};
        JALR: rf_wrdata = ma_wb.pc + 4;
        JAL: rf_wrdata = ma_wb.pc + 4;
        SYSTEM: rf_wrdata = ma_wb.csr_read;
        default: rf_wrdata = 32'b0;
    endcase

//-----------------------------------------------------------------------------
// Register File
//-----------------------------------------------------------------------------


// rf_rs*, rf_rd IF/ID
// rf_wr, rf_wrdata imm (IF/ID) or csr (EX/MA) or mem (MA/WB)
rf rf_u0(
    .clk(clk),
    .rst_n(rst_n),

    // input IF/ID
    .rs1( halted ? (dbg_arcc.regno & 16'h7FFF) : if_id.rf_rs1),
    .rs2(if_id.rf_rs2),
    .rd( halted ? (dbg_arcc.regno & 16'h7FFF) : ma_wb.rf_rd),

    // input MA/WB
    .wr(halted ? (dbg_arcc.transfer & dbg_arcc.write) : ma_wb.rf_wr), // state changing
    .wrdata(halted ? dbg_rwrdata : rf_wrdata),

    // output ID/EX
    .r1(rf_r1),
    .r2(rf_r2)
);

//-----------------------------------------------------------------------------
// CSRs
//-----------------------------------------------------------------------------


logic [11:0] csr_addr;
dcsr_t dcsr;
assign csr_addr = ma_wb.csr_wr ? ma_wb_itype_i.imm : id_ex_itype_i.imm;

csr csr_u0(
    .clk(clk),
    .rst_n(rst_n),

    // input EX/MA
    .wr(ma_wb.csr_wr),

    // input ID/EX
    .address(csr_addr),

    // input MA/WB
    .wrdata(ma_wb.csr_wrdata),

    // interrupt store and restoring
    // TODO: privilege escaltion and restore
    .pc(pc_to_store),
    .privilege(privilege),
    .xEIP(irq_ext),
    .xTIP(irq_timer),
    .xSIP(irq_sw),
    .interrupt(interrupt),
    .dbg(dbg_int),
    .dbg_cause(dbg_cause),
    .return_from_interrupt(return_from_interrupt),

    // output EX/MA
    .out(csr_read),

    // exposed regs (very frequent use)
    // may use pipeline/multi-cycle to arbitrary access any reg before it's side effect affects
    .o_mstatus(mstatus),
    .o_mie(mie),
    .o_mip(mip),
    .o_mtvec(mtvec),
    .o_mcause(mcause),
    .o_mepc(mepc),
    .o_dpc(dpc),
    .o_dcsr(dcsr)
);

//-----------------------------------------------------------------------------
// ALU
//-----------------------------------------------------------------------------


alu alu_u0(
    // input ID/EX
    .in1(id_ex.rf_r1), // always
    .in2((id_ex.instruction[6:2] == OP_IMM) ? $signed({{20{id_ex_itype_i.imm[31]}}, id_ex_itype_i.imm}) : id_ex.rf_r2),
    .use_shamt(id_ex.instruction[6:2] == OP_IMM),
    .shamt(id_ex_itype_i.imm[24:20]),

    
    // output EX/MA
    .out(alu_out),
    .carry(alu_out_c),
    .negative(alu_out_n),
    .zero(alu_out_z),
    .overflow(alu_out_overflow),

    // input ID/EX
    .funct3(id_ex.alu_funct3),
    .funct7(id_ex.alu_funct7)
);

endmodule
