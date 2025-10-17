package instructions;

typedef struct packed {
    bit [31:25] funct7;
    bit [24:20] rs2;
    bit [19:15] rs1;
    bit [14:12] funct3;
    bit [11:7] rd;
    bit [6:0] opcode;
} rtype;

typedef struct packed {
    bit [31:20] imm;
    bit [19:15] rs1;
    bit [14:12] funct3;
    bit [11:7] rd;
    bit [6:0] opcode;
} itype;

typedef struct packed {
    bit [31:25] imm_b11_5;
    bit [24:20] rs2;
    bit [19:15] rs1;
    bit [14:12] funct3;
    bit [11:7] imm_b4_0;
    bit [6:0] opcode;
} stype;

typedef struct packed {
    bit imm_b12;
    bit [30:25] imm_b10_5;
    bit [24:20] rs2;
    bit [19:15] rs1;
    bit [14:12] funct3;
    bit [11:8] imm_b4_1;
    bit imm_b11;
    bit [6:0] opcode;
} btype;

typedef struct packed {
    bit [31:12] imm;
    bit [11:7] rd;
    bit [6:0] opcode;
} utype;

typedef struct packed {
    bit imm_b20;
    bit [30:21] imm_b10_1;
    bit imm_b11;
    bit [19:12] imm_b19_12;
    bit [11:7] rd;
    bit [6:0] opcode;
} jtype;

typedef struct packed {
    bit SD;
    bit [30:25] WPRI0;
    bit SDT;
    bit SPELP;
    bit TSR;
    bit TW;
    bit TVM;
    bit MXR;
    bit SUM;
    bit MPRV;
    bit [1:0] XS;
    bit [1:0] FS;
    bit [1:0] MPP;
    bit [1:0] VS;
    bit SPP;
    bit MPIE;
    bit UBE;
    bit SPIE;
    bit WPRI1;
    bit MIE;
    bit WPRI2;
    bit SIE;
    bit WPRI3;
} mstatus_t;

typedef struct packed {
    bit [31:2] base;
    bit [1:0] mode;
} mtvec_t;

typedef struct packed {
    bit interr;
    bit [30:0] code;
} mcause_t;

typedef struct packed {
    bit [31:14] _zero_31_14;
    bit LCOFIP;
    bit _zero_12;
    bit MEIP;
    bit _zero_10;
    bit SEIP;
    bit _zero_8;
    bit MTIP;
    bit _zero_6;
    bit STIP;
    bit _zero_4;
    bit MSIP;
    bit _zero_2;
    bit SSIP;
    bit _zero_0;
} mip_t;

typedef struct packed {
    bit [31:14] _zero_31_14;
    bit LCOFIE;
    bit _zero_12;
    bit MEIE;
    bit _zero_10;
    bit SEIE;
    bit _zero_8;
    bit MTIE;
    bit _zero_6;
    bit STIE;
    bit _zero_4;
    bit MSIE;
    bit _zero_2;
    bit SSIE;
    bit _zero_0;
} mie_t;

typedef struct packed {
    bit [1:0] prv;
    bit step;
    bit nmip;
    bit mprven;
    bit _5;
    bit [8:6] cause;
    bit stoptime;
    bit stopcount;
    bit stepie;
    bit ebreaku;
    bit ebreaks;
    bit _14;
    bit ebreakm; // 
    bit [27:16] _27_16;
    bit [31:28] xdebugver; // hardwire to 4
} dcsr_t;

typedef enum logic [1:0] {M = 2'b11, S = 2'b01, U = 2'b00} privilege_t;

typedef struct packed {
    logic dmactive;
    logic ndmreset;
    logic clrresethaltreq;
    logic setresethaltreq;
    logic [5:4] _5_4;
    logic [15:6] hartselhi; // should make all 0 except hartsel[0]
    logic [25:16] hartsello;
    logic hasel; // tie to zero
    logic _27;
    logic ackhavereset;
    logic hartreset;
    logic resumereq;
    logic haltreq;
} dmcontrol_t;

typedef struct packed {
    logic [3:0] datacount; // hard wire to any of 1-12 (I implement 3 registers)
    logic [7:4] _7_4;
    logic [10:8] cmderr;
    logic _11;
    logic busy;
    logic [23:13] _23_13;
    logic [28:24] progbufsize; // hardwire to 0
} abstractcs_t;

typedef struct packed {
    logic [23:0] control;
    logic [31:24] cmdtype;
} command_t;

typedef struct packed {
    logic sbaccess8;
    logic sbaccess16;
    logic sbaccess32; // only supported, rest 0s
    logic sbaccess64;
    logic sbaccess128;
    logic [11:5] sbasize; // 32
    logic [14:12] sberror;
    logic sbreadondata;
    logic sbautoincrement;
    logic [19:17] sbaccess;
    logic sbreadonaddr;
    logic sbbusy;
    logic sbbusyerror;
    logic [28:23] _28_23;
    logic [31:29] sbversion; // tie to one
} sbcs_t;

typedef struct packed {
    logic [3:0] version;
    logic confstrptrvalid;
    logic hasresethaltreq;
    logic authbusy;
    logic authenticated;
    logic anyhalted;
    logic allhalted;
    logic anyrunning;
    logic allrunning;
    logic anyunavail;
    logic allunavail;
    logic anynonexistent;
    logic allnonexistent;
    logic anyresumeack;
    logic allresumeack;
    logic anyhavereset;
    logic allhavereset;
    logic [21:20] _21_20;
    logic impebreak;
    logic [31:23] _31_23;
} dmstatus_t;

endpackage
