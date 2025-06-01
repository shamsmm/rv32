module cu(input logic [31:0] instruction);

rtype rtype_i;
itype itype_i;
stype stype_i;
btype btype_i;
utype utype_i;
jtype jtype_i;

logic [6:0] opcode;

always_comb begin
    opcode = instruction[6:0];
    rtype_i = instruction;
    itype_i = instruction;
    stype_i = instruction;
    btype_i = instruction;
    utype_i = instruction;
    jtype_i = instruction;


    if (opcode[1:0] == 2'b11)
        case(opcode[6:5])
            2'b00:
                case(opcode[4:2])
                    3'b000: ; // LOAD
                    3'b001: ; // LOAD-FP
                    3'b010: ; // custom-0
                    3'b011: ; // MISC-MEM
                    3'b100: begin // OP-IMM
                        alu_in2 = IMM;
                        regwrdata = alu_out;
                    end
                    3'b101: ; // AUIPC
                    3'b110: ; // OP-IMM-32
                endcase
            2'b01:
                case(opcode[4:2])
                    3'b000: begin // STORE
                        memwraddr = alu_out;
                        memwrdata = rd;
                    end
                    3'b001: ; // STORE-FP
                    3'b010: ; // custom-1
                    3'b011: ; // AMO
                    3'b100: ; // OP
                    3'b101: begin // LUI
                        wre = 1'b1;
                        wrdata = {utype_i.imm, 12{1b'0}};
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
                        b = 1'b0;



                        pc = b ? imm : next;
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

endmodule