module alu(input logic [31:0] in1, [31:0] in2, [4:0] shamt, output logic[31:0] out, carry, negative, zero, [14:12] funct3, [31:20] funct7);

assign negative = out[31];
assign zero = out == 0;
assign overflow = (in1[31] == in2[31]) && (in1[31] != out[31]);

always_comb begin
    case(funct7)
        7'b000000: begin
            case(funct3)
                3'b000: {carry, out} = 33'(in1) + in2; // ADD/ADDI
                3'b001: out = in1 << shamt; // SLL/SLLI
                3'b010: out = $signed(in1) < $signed(in2); // SLT/SLTI
                3'b011: out = in1 < in2; // SLTU/SLTIU
                3'b100: out = in1 ^ in2; // XOR/XORI
                3'b101: out = in1 >> shamt; // SRL/SRLI
                3'b110: out = in1 | in2; // OR/ORI
                3'b111: out = in1 & in2; // AND/ANDI
            endcase
        end
        7'b010000: begin
            case(funct3)
                3'b000: {carry, out} = 33'(in1) - in2; // SUB
                3'b101: out = in1 >>> shamt; // SRA/SRAI
            endcase
        end
    endcase
end


endmodule