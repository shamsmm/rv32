import instructions::*;
import bus_if_types_pkg::*;

// Core with I-Bus interface and D-bus interface; both maybe connected with a crossbar
// but to avoid structural hazard, allow high performance SRAM to have dual ports
module  rv_core #(parameter logic [31:0] INITIAL_PC) (
    master_bus_if.master dbus,
    master_bus_if.master ibus,
    input bit clk,
    input bit rst_n,

    input bit haltreq = 1'b0,
    input bit resumereq = 1'b0,
    input bit resethaltreq = 1'b0
);

// rv_core_csr zicsr(.csr_*)

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
        HALTING: next_hstate = (state == WB) ? HALTED : NORMAL; // halt next after writing back (IF phase)
        HALTED: next_hstate = resumereq ? RESUMING : HALTED; // for fsm to be like DM spec
        RESUMING: next_hstate = NORMAL;
    endcase

enum logic [1:0] {IF, EX, MA, WB} state, next_state;

always_ff @(posedge clk or negedge rst_n)
    if(!rst_n)
        state <= IF;
    else
        state <= next_state;

logic halt = (hstate == HALTED);

always_comb begin 
    next_state = IF;
    ibus.bstart = 1'b0;

    if (!halt) // gaurantee to halt only on Instruction Fetch
        case(state)
            IF: begin 
                ibus.bstart = 1'b1;
                next_state = ibus.bdone ? EX : IF; 
            end
            EX: next_state = (mem_wr | mem_rd) ? MA : WB;
            MA: next_state = dbus.bdone ? WB : MA;
            WB: next_state = IF;
        endcase
end

localparam bit [31:0] NOP = 0;

logic [31:0] pc, next_pc;

always_comb begin
    ibus.breq = 1'b1;
    ibus.ttype = READ;
    ibus.tsize = WORD;
    ibus.addr = pc;
    ibus.wdata = 32'b0;
end

always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
        pc <= INITIAL_PC;
    else if (state == WB) // last state
        pc <= next_pc;
end

always_ff @(posedge clk) begin
    if (state == IF && ibus.bdone)
        instruction <= ibus.rdata;
end

// IF
logic [31:0] instruction;

// ID

// EX

// MA

// WB

rtype rtype_i;
itype itype_i;
stype stype_i;
btype btype_i;
utype utype_i;
jtype jtype_i;

always_comb begin
    rtype_i = instruction;
    itype_i = instruction;
    stype_i = instruction;
    btype_i = instruction;
    utype_i = instruction;
    jtype_i = instruction; 
end

logic [6:0] opcode;

logic [31:0] alu_out;
logic alu_use_shamt;
logic [4:0] alu_shamt;
logic [2:0] alu_funct3;
logic [6:0] alu_funct7;
logic id_imm;

logic [31:0] rf_wrdata, rf_r1, rf_r2;
logic [4:0] rf_rs1, rf_rs2, rf_rd;
logic rf_wr;

logic branch;

logic mem_wr;
logic mem_rd;
logic [31:0] mem_addr, mem_rdata;
logic mem_r;

tsize_e tsize;

logic alu_out_c, alu_out_z, alu_out_n, alu_out_overflow;


always_comb begin
    dbus.wdata = rf_r2; // always writing from data in register
    dbus.breq = 1'b1;
    dbus.addr = mem_addr;
    mem_rdata = dbus.rdata;
    dbus.tsize = tsize;
end

// state changing
always_comb begin
    dbus.bstart = 1'b0;
    dbus.ttype = READ;

    if (state == MA) begin
        if (mem_wr) begin
            dbus.bstart = 1'b1;
            dbus.ttype = WRITE;
        end else if (mem_rd) begin
            dbus.bstart = 1'b1;
            dbus.ttype = READ;
        end
    end
end


enum logic [4:0] {LOAD, LOAD_FP, custom_0, MISC_MEM, OP_IMM, AUIPC, OP_IMM_32, STORE, STORE_FP, custom_1, AMO, OP, LUI, OP_32, MADD, MSUB, NMSUB, NMADD, OP_FP, OP_V, custom_2, BRANCH, JALR, JAL, SYSTEM, OP_VE, custom_3} mopcode; // major opcode

always_comb begin
    opcode = instruction[6:0];

    // defaults
    rf_wr = 1'b0;
    rf_rd = 5'b0;
    rf_rs1 = 5'b0;
    rf_rs2 = 5'b0;

    mem_wr = 1'b0;
    mem_rd = 1'b0;

    branch = 0;

    id_imm = 1'b0;
    alu_funct7 = 7'b0;
    alu_funct3 = 3'b0;
    alu_use_shamt = 1'b0;
    alu_shamt = 5'b0;

    tsize = WORD;

    if (opcode[1:0] == 2'b11)
        case(opcode[6:5])
            2'b00:
                case(opcode[4:2])
                    3'b000: begin // LOAD
                        mopcode = LOAD;

                        rf_rd = itype_i.rd;
                        rf_rs1 = itype_i.rs1;
                         
                        rf_wr = 1'b1;
                        
                        tsize = tsize_e'(itype_i.funct3[14:12]); // by ISA

                        mem_rd = 1'b1;
                        
                    end
                    3'b001: mopcode = LOAD_FP; // LOAD-FP
                    3'b010: mopcode = custom_0; // custom-0
                    3'b011: mopcode = MISC_MEM; // MISC-MEM
                    3'b100: begin // OP-IMM
                        mopcode = OP_IMM;
                        rf_rd = itype_i.rd;
                        rf_rs1 = itype_i.rs1;
                        rf_wr = 1'b1;
                        alu_funct3 = itype_i.funct3;
                        alu_funct7 = alu_funct3 == 3'b101 ? itype_i.imm[31:25] : 7'b0;
                    end
                    3'b101: begin // AUIPC
                        mopcode = AUIPC;
                        rf_wr = 1'b1;
                        rf_rd = utype_i.rd;
                    end
                    3'b110: mopcode = OP_IMM_32; // OP-IMM-32
                endcase
            2'b01:
                case(opcode[4:2])
                    3'b000: begin // STORE
                        mopcode = STORE;
                        rf_rs1 = stype_i.rs1;
                        rf_rs2 = stype_i.rs2;
    
                        mem_wr = 1'b1;
                        

                        tsize = tsize_e'(stype_i.funct3[14:12]);
                    end
                    3'b001: mopcode = STORE_FP; // STORE-FP
                    3'b010: mopcode = custom_1; // custom-1
                    3'b011: mopcode = AMO; // AMO
                    3'b100: begin // OP
                        mopcode = OP;
                        rf_rd = rtype_i.rd;
                        rf_rs1 = rtype_i.rs1;
                        rf_rs2 = rtype_i.rs2;
                        rf_wr = 1'b1;
                        
                        alu_funct3 = rtype_i.funct3;
                        alu_funct7 = rtype_i.funct7;
                    end
                    3'b101: begin // LUI
                        mopcode = LUI;
                        rf_wr = 1'b1;
                        rf_rd = utype_i.rd;
                    end
                    3'b110: mopcode = OP_32; // OP-32
                endcase
            2'b10:
                case(opcode[4:2])
                    3'b000: mopcode = MADD; // MADD
                    3'b001: mopcode = MSUB; // MSUB
                    3'b010: mopcode = NMSUB; // NMSUB
                    3'b011: mopcode = NMADD; // NMADD
                    3'b100: mopcode = OP_FP; // OP-FP
                    3'b101: mopcode = OP_V; // OP-V
                    3'b110: mopcode = custom_2; // custom-2/RV128
                endcase
            2'b11:
                case(opcode[4:2])
                    3'b000: begin // BRANCH                     
                        mopcode = BRANCH;
                        rf_rs1 = btype_i.rs1;
                        rf_rs2 = btype_i.rs2;
                        alu_funct7 = 7'b0100000; // subtract
                        alu_funct3 = 3'b000; // subtract

                        case(btype_i.funct3)
                            3'b000: branch = (alu_out_z); // BEQ
                            3'b001: branch = !(alu_out_z); // BNEQ
                            3'b100: branch = (alu_out_n ^ alu_out_overflow); // BLT
                            3'b101: branch = !(alu_out_n ^ alu_out_overflow); // BGE
                            3'b110: branch = !alu_out_c; // BLTU
                            3'b111: branch = alu_out_c; // BGEU
                        endcase
                        
                        
                    end
                    3'b001: begin // JALR
                        mopcode = JALR;
                        rf_rs1 = itype_i.rs1;
                        rf_rd = itype_i.rd;
                        rf_wr = 1'b1;
                    end
                    3'b010: ; // reserved
                    3'b011: begin // JAL
                        mopcode = JAL;
                        rf_rd = jtype_i.rd;
                        rf_wr = 1'b1;
                    end
                    3'b100: mopcode = SYSTEM; // SYSTEM
                    3'b101: mopcode = OP_VE; // OP-VE
                    3'b110: mopcode = custom_3; // custom-3/RV128
                endcase
        endcase
end

// memory access address
always_comb
    case(mopcode)
        LOAD: mem_addr = rf_r1 + $signed({{20{itype_i.imm[31]}},itype_i.imm});
        STORE: mem_addr = rf_r1 + $signed({{20{stype_i.imm_b11_5[31]}},stype_i.imm_b11_5, stype_i.imm_b4_0});
        default: mem_addr = 32'b0;
    endcase

// pc write
always_comb
    case(mopcode)
        BRANCH: begin 
            if (branch)
                next_pc = pc + $signed({{19{btype_i.imm_b12}}, btype_i.imm_b12, btype_i.imm_b11, btype_i.imm_b10_5, btype_i.imm_b4_1, 1'b0});
            else
                next_pc = pc + 4;
        end
        JALR: begin
            next_pc = $signed({{20{itype_i.imm[31]}}, itype_i.imm}) + rf_r1;
            next_pc[0] = 1'b0;
        end
        JAL: next_pc = pc + $signed({{11{jtype_i.imm_b20}}, jtype_i.imm_b20, jtype_i.imm_b19_12, jtype_i.imm_b11,jtype_i.imm_b10_1, 1'b0});
        default: next_pc = pc + 4;
    endcase

// register file write
always_comb
    case(mopcode)
        LOAD: 
            case(itype_i.funct3)
                3'b000: rf_wrdata = {{24{mem_rdata[7]}}, mem_rdata[7:0]}; // LB
                3'b001: rf_wrdata = {{16{mem_rdata[15]}}, mem_rdata[15:0]}; // LH
                3'b010: rf_wrdata = mem_rdata; // LW
                3'b100: rf_wrdata = {{24{1'b0}}, mem_rdata[7:0]}; // LBU
                3'b101: rf_wrdata = {{16{mem_rdata[15]}}, mem_rdata[15:0]}; // LHU
                default: rf_wrdata = 32'b0;
            endcase
        OP_IMM: rf_wrdata = alu_out;
        AUIPC: rf_wrdata = {utype_i.imm, {12{1'b0}}} + pc;
        OP: rf_wrdata = alu_out;
        LUI: rf_wrdata = {utype_i.imm, {12{1'b0}}};
        JALR: rf_wrdata = pc + 4;
        JAL: rf_wrdata = pc + 4;
        default: rf_wrdata = 32'b0;
    endcase

rf rf_u0(
    .clk(clk),
    .rst_n(rst_n),
    .rs1(rf_rs1),
    .rs2(rf_rs2),
    .rd(rf_rd),
    .wr((state == WB) ? rf_wr : 1'b0), // state changing
    .wrdata(rf_wrdata),
    .r1(rf_r1),
    .r2(rf_r2)
);

logic [31:0] imm = $signed({{20{itype_i.imm[31]}}, itype_i.imm});

alu alu_u0(
    .in1(rf_r1), // always
    .in2((mopcode == OP_IMM) ? imm : rf_r2),
    .use_shamt(mopcode == OP_IMM),
    .shamt(itype_i.imm[24:20]),
    .out(alu_out),
    .carry(alu_out_c),
    .negative(alu_out_n),
    .zero(alu_out_z),
    .overflow(alu_out_overflow),
    .funct3(alu_funct3),
    .funct7(alu_funct7)
);

endmodule
