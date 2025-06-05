module alu (
    input logic [31:0] in1,
    input logic [31:0] in2,
    input logic [4:0] shamt,
    input logic use_shamt,
    output logic[31:0] out,
    output logic carry,
    output logic negative,
    output logic zero,
    output logic overflow,
    input logic [14:12] funct3,
    input logic [31:25] funct7
);

assign negative = out[31];
assign zero = out == 0;
assign overflow = (in1[31] == in2[31]) && (in1[31] != out[31]);

always_comb begin
    out = 0;
    carry = 0;

    case(funct7)
        7'b0000000: begin
            case(funct3)
                3'b000: {carry, out} = 33'(in1) + in2; // ADD/ADDI
                3'b001: out = !use_shamt ? in1 << in2 : in1 << shamt ; // SLL/SLLI
                3'b010: out = {{31{1'b0}}, $signed(in1) < $signed(in2)}; // SLT/SLTI
                3'b011: out = {{31{1'b0}}, in1 < in2}; // SLTU/SLTIU
                3'b100: out = in1 ^ in2; // XOR/XORI
                3'b101: out = !use_shamt ? in1 >> in2 : in1 >> shamt; // SRL/SRLI
                3'b110: out = in1 | in2; // OR/ORI
                3'b111: out = in1 & in2; // AND/ANDI
            endcase
        end
        7'b0100000: begin
            case(funct3)
                3'b000: {carry, out} = 33'(in1) - in2; // SUB
                3'b101: out = !use_shamt ? in1 >>> in2 : in1 >>> shamt; // SRA/SRAI
            endcase
        end
        default: begin
            out = 0; 
            carry = 0;
        end
    endcase
end


endmodule