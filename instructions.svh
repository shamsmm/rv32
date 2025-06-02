typedef struct packed {
    bit [6:0] opcode;
    bit [11:7] rd;
    bit [14:12] funct3;
    bit [19:15] rs1;
    bit [24:20] rs2;
    bit [31:25] funct7;
} rtype;

typedef struct packed {
    bit [6:0] opcode;
    bit [11:7] rd;
    bit [14:12] funct3;
    bit [19:15] rs1;
    bit [31:20] imm;
} itype;

typedef struct packed {
    bit [6:0] opcode;
    bit [11:7] imm_b4_0;
    bit [14:12] funct3;
    bit [19:15] rs1;
    bit [24:20] rs2;
    bit [31:25] imm_b11_5;
} stype;

typedef struct packed {
    bit [6:0] opcode;
    bit imm_b11;
    bit [11:8] imm_b4_1;
    bit [14:12] funct3;
    bit [19:15] rs1;
    bit [24:20] rs2;
    bit [30:25] imm_b10_5;
    bit imm_b12;
} btype;

typedef struct packed {
    bit [6:0] opcode;
    bit [11:7] rd;
    bit [31:12] imm;
} utype;

typedef struct packed {
    bit [6:0] opcode;
    bit [11:7] rd;
    bit [19:12] imm_b19_12;
    bit imm_b11;
    bit [30:21] imm_b10_1;
    bit imm_b20;
} jtype;
