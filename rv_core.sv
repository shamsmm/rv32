`include "bus_if.svh"
`include "instructions.svh"

// Core with I-Bus interface and D-bus interface; both maybe connected with a crossbar
// but to avoid structural hazard, allow high performance SRAM to have dual ports
module  rv_core #(parameter logic [31:0] INITIAL_PC) (
    master_bus_if.master dbus,
    master_bus_if.master ibus,
    input clk,
    input rst_n
);

enum {IF, EX, MA, WB} state, next_state;

always_ff @(posedge clk or negedge rst_n)
    if(!rst_n)
        state <= IF;
    else
        state <= next_state;

always_comb 
    case(state)
        IF: next_state = ibus.bdone ? EX : IF;
        EX: next_state = (mem_wr | mem_rd) ? MA : WB;
        MA: next_state = dbus.bdone ? WB : MA;
        WB: next_state = IF;
    endcase

localparam bit [31:0] NOP = 0;

logic [31:0] pc, next_pc;

always_comb begin
    ibus.breq = 1'b1;
    ibus.ttype = READ;
    ibus.tsize = WORD;
    ibus.bstart = 1'b1;
    ibus.addr = pc;
end

always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
        pc <= INITIAL_PC;
    else if (next_state == IF)
        pc <= next_pc;
end

always_ff @(posedge clk) begin
    if (state == IF)
        instruction <= ibus.rdata; // may be grabage but after some time it is ok
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

logic [31:0] alu_in1, alu_in2, alu_out;
logic alu_use_shamt;
logic [4:0] alu_shamt;
logic [2:0] alu_funct3;
logic [6:0] alu_funct7;

logic [31:0] rf_wrdata, rf_r1, rf_r2;
logic [4:0] rf_rs1, rf_rs2, rf_rd;
logic rf_wr;

logic branch;

logic mem_wr;
logic mem_rd;
logic [31:0] mem_addr, mem_wrdata, mem_rdata;
logic mem_r;

tsize_e tsize;

logic alu_out_c, alu_out_z, alu_out_n, alu_out_overflow;

logic wb_rf_wr = (state == WB) ? rf_wr : 1'b0;

always_comb begin
    dbus.wdata = mem_wrdata;
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


always_comb begin
    opcode = instruction[6:0];

    next_pc = pc + 4;
    assert(next_pc[1:0] == 2'b00);

    // defaults
    rf_wr = 1'b0;
    mem_wr = 1'b0;
    mem_rd = 1'b0;

    if (opcode[1:0] == 2'b11)
        case(opcode[6:5])
            2'b00:
                case(opcode[4:2])
                    3'b000: begin // LOAD
                        rf_rd = itype_i.rd;
                        rf_rs1 = itype_i.rs1;
                         
                        rf_wr = 1'b1;
                        
                        tsize = tsize_e'(itype_i.funct3[14:12]); // by ISA

                        case(itype_i.funct3)
                            3'b000: rf_wrdata = {{24{mem_rdata[7]}}, mem_rdata[7:0]}; // LB
                            3'b001: rf_wrdata = {{16{mem_rdata[15]}}, mem_rdata[15:0]}; // LH
                            3'b010: rf_wrdata = mem_rdata; // LW
                            3'b100: rf_wrdata = {{24{1'b0}}, mem_rdata[7:0]}; // LBU
                            3'b101: rf_wrdata = {{16{mem_rdata[15]}}, mem_rdata[15:0]}; // LHU
                        endcase

                        mem_rd = 1'b1;
                        mem_addr = rf_r1 + $signed({{20{itype_i.imm[31]}},itype_i.imm});
                    end
                    3'b001: ; // LOAD-FP
                    3'b010: ; // custom-0
                    3'b011: ; // MISC-MEM
                    3'b100: begin // OP-IMM
                        rf_rd = itype_i.rd;
                        rf_rs1 = itype_i.rs1;
                        rf_wr = 1'b1;
                        rf_wrdata = alu_out;
                        alu_funct3 = itype_i.funct3;
                        alu_funct7 = alu_funct3 == 3'b101 ? itype_i.imm[31:25] : 7'b0;
                        alu_use_shamt = 1'b1;
                        alu_shamt = itype_i.imm[24:20];
                        alu_in1 = rf_r1;
                        alu_in2 = $signed({{20{itype_i.imm[31]}}, itype_i.imm});
                    end
                    3'b101: begin // AUIPC
                        rf_wr = 1'b1;
                        rf_rd = utype_i.rd;
                        rf_wrdata = {utype_i.imm, {12{1'b0}}} + pc;
                    end
                    3'b110: ; // OP-IMM-32
                endcase
            2'b01:
                case(opcode[4:2])
                    3'b000: begin // STORE
                        rf_rs1 = stype_i.rs1;
                        rf_rs2 = stype_i.rs2;
    
                        mem_wr = 1'b1;
                        mem_addr = rf_r1 + $signed({{20{stype_i.imm_b11_5[31]}},stype_i.imm_b11_5, stype_i.imm_b4_0});
                        mem_wrdata = rf_r2; // will be trimmed

                        tsize = tsize_e'(stype_i.funct3[14:12]);
                    end
                    3'b001: ; // STORE-FP
                    3'b010: ; // custom-1
                    3'b011: ; // AMO
                    3'b100: begin // OP
                        rf_rd = rtype_i.rd;
                        rf_rs1 = rtype_i.rs1;
                        rf_rs2 = rtype_i.rs2;
                        rf_wr = 1'b1;
                        rf_wrdata = alu_out;
                        alu_in1 = rf_r1;
                        alu_in2 = rf_r2;
                        alu_funct3 = rtype_i.funct3;
                        alu_funct7 = rtype_i.funct7;
                    end
                    3'b101: begin // LUI
                        rf_wr = 1'b1;
                        rf_rd = utype_i.rd;
                        rf_wrdata = {utype_i.imm, {12{1'b0}}};
                    end
                    3'b110: ; // OP-32
                endcase
            2'b10:
                case(opcode[4:2])
                    3'b000: ; // MADD
                    3'b001: ; // MSUB
                    3'b010: ; // NMSUB
                    3'b011: ; // NMADD
                    3'b100: ; // OP-FP
                    3'b101: ; // reserved
                    3'b110: ; // custom-2/RV128
                endcase
            2'b11:
                case(opcode[4:2])
                    3'b000: begin // BRANCH
                        branch = 0;
                        
                        rf_rs1 = btype_i.rs1;
                        rf_rs2 = btype_i.rs2;
                        alu_in1 = rf_r1;
                        alu_in2 = rf_r2;
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
                        
                        if (branch)
                            next_pc = pc + $signed({{19{btype_i.imm_b12}}, btype_i.imm_b12, btype_i.imm_b11, btype_i.imm_b10_5, btype_i.imm_b4_1, 1'b0});
                    end
                    3'b001: begin // JALR
                        rf_rs1 = itype_i.rs1;
                        rf_rd = itype_i.rd;
                        rf_wr = 1'b1;
                        rf_wrdata = pc + 4;
                        
                        next_pc = $signed({{20{itype_i.imm[31]}}, itype_i.imm}) + rf_r1;
                        next_pc[0] = 1'b0;
                    end
                    3'b010: ; // reserved
                    3'b011: begin // JAL
                        next_pc = pc + $signed({{11{jtype_i.imm_b20}}, jtype_i.imm_b20, jtype_i.imm_b19_12, jtype_i.imm_b11,jtype_i.imm_b10_1, 1'b0});
                        rf_rd = jtype_i.rd;
                        rf_wr = 1'b1;
                        rf_wrdata = pc + 4;
                    end
                    3'b100: ; // SYSTEM
                    3'b101: ; // reserved
                    3'b110: ; // custom-3/RV128
                endcase
        endcase
end

rf rf_u0(
    .clk(clk),
    .rst_n(rst_n),
    .rs1(rf_rs1),
    .rs2(rf_rs2),
    .rd(rf_rd),
    .wr(wb_rf_wr), // state changing
    .wrdata(rf_wrdata),
    .r1(rf_r1),
    .r2(rf_r2)
);



alu alu_u0(
    .in1(alu_in1),
    .in2(alu_in2),
    .use_shamt(alu_use_shamt),
    .shamt(alu_shamt),
    .out(alu_out),
    .carry(alu_out_c),
    .negative(alu_out_n),
    .zero(alu_out_z),
    .overflow(alu_out_overflow),
    .funct3(alu_funct3),
    .funct7(alu_funct7)
);

endmodule
