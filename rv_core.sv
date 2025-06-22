import instructions::*;
import bus_if_types_pkg::*;

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

    // interrupts from PLIC or timer or external
    input bit irq_sw = 1'b0,
    input bit irq_ext = 1'b0,
    input bit irq_timer = 1'b0
);

//-----------------------------------------------------------------------------
// Vital signals, hazard detection, flushing and stalling
//-----------------------------------------------------------------------------


logic halted; // TODO: wire up to pipeline

logic hazard = 1'b0;
logic stall; // due to hazards or memory delay
logic flush; // if jump or branch was taken
logic [2:0] pipeline_fill;

always_ff @(negedge clk or negedge rst_n) begin
    if (!rst_n) begin
        stall <= 0;
        flush <= 0;
    end else begin
        stall <= hazard | (ibus_state != IDLE) | (dbus_state != IDLE);
        flush <= pipeline_fill == 4 && ma_wb.next_pc != ex_ma.pc;
    end
end

always_ff @(posedge clk, negedge rst_n) 
    if (!rst_n || flush)
        pipeline_fill <= 0;
    else if (!stall)
        pipeline_fill <= pipeline_fill == 4 ? pipeline_fill : pipeline_fill + 1;

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


always_comb
    case(hstate)
        RESET: next_hstate = resethaltreq ? HALTED : NORMAL;
        NORMAL: next_hstate = haltreq ? HALTING : NORMAL;
        HALTING: next_hstate = (halted) ? HALTED : NORMAL; // halt next after writing back (IF phase)
        HALTED: next_hstate = resumereq ? RESUMING : HALTED; // for fsm to be like DM spec
        RESUMING: next_hstate = NORMAL;
        default: next_hstate = NORMAL;
    endcase

//-----------------------------------------------------------------------------
// PC and I-bus interface
//-----------------------------------------------------------------------------

logic [31:0] pc;

typedef enum logic [1:0] {IDLE, AD, DA} bus_state_e;

bus_state_e ibus_state;
bus_state_e dbus_state;

always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
        ibus_state <= IDLE;
    else
        case(ibus_state)
            IDLE: ibus_state <= ibus.bstart ? AD : IDLE;
            AD: ibus_state <= ibus.bdone ? DA : AD;
            DA: ibus_state <= IDLE;
        endcase
end

always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
        dbus_state <= IDLE;
    else
        case(dbus_state)
            IDLE: dbus_state <= dbus.bstart ? AD : IDLE;
            AD: dbus_state <= dbus.bdone ? DA : AD;
            DA: dbus_state <= IDLE;
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
    else if (flush)
        ibus.addr <= ma_wb.next_pc; // must fetch from that instruction (discarding all that entered pipeline)
    else if (!stall) begin
        ibus.addr <= ibus.addr + 4; // assume branches are not taken, includes (unconditional jumps) and let the pipeline flush when it has to
    end
end


always_comb begin
    instruction = ibus.rdata;
end

logic [31:0] instruction;


//-----------------------------------------------------------------------------
// Pipeline stage definitions
//-----------------------------------------------------------------------------

// TODO: use modports with interfaces if this makes it more readible

struct packed {
    logic [31:0] instruction;
    logic [31:0] pc;

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
} ex_ma;

struct packed {
    logic [31:0] instruction;
    logic [31:0] pc;

    // passed
    logic [31:0] alu_out;
    logic [31:0] csr_read;


    // intrinsic
    logic [31:0] mem_rdata;
    logic [4:0] rf_rd;
    logic rf_wr;
    logic csr_wr;
    logic [31:0] csr_wrdata;
    logic [31:0] next_pc;
} ma_wb;

//-----------------------------------------------------------------------------
// Interconnections and type casts
//-----------------------------------------------------------------------------

rtype rtype_i;
itype itype_i;
stype stype_i;
btype btype_i;
utype utype_i;
jtype jtype_i;

itype id_ex_itype_i;

btype ex_ma_btype_i;
jtype ex_ma_jtype_i;
itype ex_ma_itype_i;
stype ex_ma_stype_i;

itype ma_wb_itype_i;
utype ma_wb_utype_i;

itype wb_itype_i;
utype wb_utype_i;

always_comb begin
    rtype_i = instruction;
    itype_i = instruction;
    stype_i = instruction;
    btype_i = instruction;
    utype_i = instruction;
    jtype_i = instruction;

    id_ex_itype_i = if_id.instruction;

    ex_ma_btype_i = id_ex.instruction;
    ex_ma_jtype_i = id_ex.instruction;
    ex_ma_itype_i = id_ex.instruction;
    ex_ma_stype_i = id_ex.instruction;

    ma_wb_itype_i = ex_ma.instruction;
    ma_wb_utype_i = ex_ma.instruction;

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

mstatus_t mstatus;
mtvec_t mtvec;
mcause_t mcause;
logic [31:0] mip, mie;

// Output
logic [31:0] csr_read;


//-----------------------------------------------------------------------------
// D-bus interface
//-----------------------------------------------------------------------------

always_comb begin
    dbus.wdata = ex_ma.rf_r2; // always writing from data in register
    dbus.bstart = ex_ma.mem_wr | ex_ma.mem_rd;
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

mopcode_t mopcode; // major opcode

//-----------------------------------------------------------------------------
// IF/ID (input instruction)
//-----------------------------------------------------------------------------

always_comb begin
    opcode = instruction[6:0];
end

always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n || flush)
        if_id <= 0;
    else if (!stall) begin
        if_id.instruction <= instruction;
        if_id.pc <= ibus.addr;
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
                        3'b001: assert (mopcode_t'(opcode[6:2]) == LOAD_FP); // LOAD-FP
                        3'b010: assert (mopcode_t'(opcode[6:2]) == custom_0); // custom-0
                        3'b011: assert (mopcode_t'(opcode[6:2]) == MISC_MEM); // MISC-MEM
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
                        3'b001: assert (mopcode_t'(opcode[6:2]) == STORE_FP); // STORE-FP
                        3'b010: assert (mopcode_t'(opcode[6:2]) == custom_1); // custom-1
                        3'b011: assert (mopcode_t'(opcode[6:2]) == AMO); // AMO
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
                        3'b110: assert (mopcode_t'(opcode[6:2]) == OP_32); // OP-32
                    endcase
                2'b10:
                    case(opcode[4:2])
                        3'b000: assert (mopcode_t'(opcode[6:2]) == MADD); // MADD
                        3'b001: assert (mopcode_t'(opcode[6:2]) == MSUB); // MSUB
                        3'b010: assert (mopcode_t'(opcode[6:2]) == NMSUB); // NMSUB
                        3'b011: assert (mopcode_t'(opcode[6:2]) == NMADD); // NMADD
                        3'b100: assert (mopcode_t'(opcode[6:2]) == OP_FP); // OP-FP
                        3'b101: assert (mopcode_t'(opcode[6:2]) == OP_V); // OP-V
                        3'b110: assert (mopcode_t'(opcode[6:2]) == custom_2); // custom-2/RV128
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
                        3'b010: ; // reserved
                        3'b011: begin // JAL
                            assert (mopcode_t'(opcode[6:2]) == JAL);
                            if_id.rf_rd <= jtype_i.rd;
                            if_id.rf_wr <= 1'b1;
                        end
                        3'b100: begin // SYSTEM
                            assert (mopcode_t'(opcode[6:2]) == SYSTEM);

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
                            endcase
                        end
                        3'b101: assert (mopcode_t'(opcode[6:2]) == OP_VE); // OP-VE
                        3'b110: assert (mopcode_t'(opcode[6:2]) == custom_3); // custom-3/RV128
                    endcase
            endcase
    end
end

//-----------------------------------------------------------------------------
// ID/EX (input IF/ID)
//-----------------------------------------------------------------------------

always_ff @(posedge clk or negedge rst_n)
    if (!rst_n || flush)
        id_ex <= 0;
    else if (!stall) begin
        id_ex.instruction <= if_id.instruction;
        id_ex.pc <= if_id.pc;
        id_ex.alu_funct3 <= if_id.alu_funct3;
        id_ex.alu_funct7 <= if_id.alu_funct7;
        id_ex.tsize <= if_id.tsize;
        id_ex.rf_r1 <= rf_r1;
        id_ex.rf_r2 <= rf_r1;
        id_ex.rf_wr <= if_id.rf_wr;
        id_ex.rf_rd <= if_id.rf_rd;
        id_ex.mem_wr <= if_id.mem_wr;
        id_ex.mem_rd <= if_id.mem_rd;
        id_ex.csr_wr <= if_id.csr_wr;
    end


//-----------------------------------------------------------------------------
// EX/MA (input ID/EX)
//-----------------------------------------------------------------------------

// input ALU, CSR
// memory access address, branching, alu, csr
// TODO: use ALU if free to calculate
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n || flush)
        ex_ma <= 0;
    else if (!stall) begin
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

        if (id_ex.instruction[6:2] == BRANCH)
            case(ex_ma_btype_i.funct3)
                3'b000: ex_ma.branch <= (alu_out_z); // BEQ
                3'b001: ex_ma.branch <= !(alu_out_z); // BNEQ
                3'b100: ex_ma.branch <= (alu_out_n ^ alu_out_overflow); // BLT
                3'b101: ex_ma.branch <= !(alu_out_n ^ alu_out_overflow); // BGE
                3'b110: ex_ma.branch <= !alu_out_c; // BLTU
                3'b111: ex_ma.branch <= alu_out_c; // BGEU
            endcase

        case(mopcode)
            LOAD: ex_ma.mem_addr <= id_ex.rf_r1 + $signed({{20{ex_ma_itype_i.imm[31]}}, ex_ma_itype_i.imm});
            STORE: ex_ma.mem_addr <= id_ex.rf_r1 + $signed({{20{ex_ma_stype_i.imm_b11_5[31]}},ex_ma_stype_i.imm_b11_5, ex_ma_stype_i.imm_b4_0});
            default: ex_ma.mem_addr <= 32'b0;
        endcase
    end
end


//-----------------------------------------------------------------------------
// MA/WB (input EX/MA)
//-----------------------------------------------------------------------------

// pc write and memory read and CSRs
always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) //  `|| flush` no need as all stages before would be discarded
        ma_wb <= 0;
    else if (!stall) begin
        ma_wb.instruction <= ex_ma.instruction;
        ma_wb.pc <= ex_ma.pc;
        ma_wb.alu_out <= ex_ma.alu_out;
        ma_wb.csr_read <= csr_read;
        ma_wb.rf_rd <= ex_ma.rf_rd;
        ma_wb.rf_wr <= ex_ma.rf_wr;
        ma_wb.csr_wr <= ex_ma.csr_wr;
        ma_wb.mem_rdata <= dbus.rdata;

        if(ex_ma.instruction[6:2] == SYSTEM)
            case(itype_i.funct3)
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
                    ma_wb.csr_wrdata <= ex_ma.csr_read & {27'b0, (~ex_ma_itype_i.rs1)};
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
    .rs1(if_id.rf_rs1),
    .rs2(if_id.rf_rs2),
    .rd(ma_wb.rf_rd),

    // input MA/WB
    .wr(ma_wb.rf_wr), // state changing
    .wrdata(rf_wrdata),

    // output ID/EX
    .r1(rf_r1),
    .r2(rf_r2)
);

//-----------------------------------------------------------------------------
// CSRs
//-----------------------------------------------------------------------------


csr csr_u0(
    .clk(clk),
    .rst_n(rst_n),

    // input EX/MA
    .wr(ma_wb.csr_wr),

    // input ID/EX
    .address(id_ex_itype_i.imm),

    // input MA/WB
    .wrdata(ma_wb.csr_wrdata),

    // output EX/MA
    .out(csr_read),

    // exposed regs (very frequent use)
    // may use pipeline/multi-cycle to arbitrary access any reg before it's side effect affects
    .o_mstatus(mstatus),
    .o_mie(mie),
    .o_mip(mip),
    .o_mtvec(mtvec),
    .o_mcause(mcause)
);

//-----------------------------------------------------------------------------
// ALU
//-----------------------------------------------------------------------------


alu alu_u0(
    // input ID/EX
    .in1(id_ex.rf_r1), // always
    .in2((id_ex.instruction[6:2] == OP_IMM) ? $signed({{20{ex_ma_itype_i.imm[31]}}, ex_ma_itype_i.imm}) : id_ex.rf_r2),
    .use_shamt(id_ex.instruction[6:2] == OP_IMM),
    .shamt(ex_ma_itype_i.imm[24:20]),

    
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
