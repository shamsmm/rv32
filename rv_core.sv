module rv_core(bus_if.master bus, input clk, input rst_n);

logic [31:0] pc, next_pc;

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

logic [31:0] rf_rs1, rf_rs2, rf_rd, rf_wr, rf_wrdata, rf_r1, rf_r2;

always_comb begin
    opcode = instruction[6:0];

    if (opcode[1:0] == 2'b11)
        case(opcode[6:5])
            2'b00:
                case(opcode[4:2])
                    3'b000: ; // LOAD
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
                        alu_in2 = {{20{itype_i.imm[31]}}, itype_i.imm};
                    end
                    3'b101: ; // AUIPC
                    3'b110: ; // OP-IMM-32
                endcase
            2'b01:
                case(opcode[4:2])
                    3'b000: begin // STORE
                        
                    end
                    3'b001: ; // STORE-FP
                    3'b010: ; // custom-1
                    3'b011: ; // AMO
                    3'b100: ; // OP
                    3'b101: begin // LUI
                        rf_wr = 1'b1;
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
            2'b10:
                case(opcode[4:2])
                    3'b000: begin // BRANCH
                        
                    end
                    3'b001: ; // JALR
                    3'b010: ; // reserved
                    3'b011: ; // JAL
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
    .wr(rf_wr),
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
    .funct3(alu_funct3),
    .funct7(alu_funct7)
);

endmodule
