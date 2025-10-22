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

// Debug
typedef struct packed {
    bit [31:28] xdebugver; // hardwire to 4
    bit [27:16] _27_16;
    bit ebreakm; //
    bit _14;
    bit ebreaks;
    bit ebreaku;
    bit stepie;
    bit stopcount;
    bit stoptime;
    bit [8:6] cause;
    bit _5;
    bit mprven;
    bit nmip;
    bit step;
    bit [1:0] prv;
} dcsr_t;

typedef enum logic [1:0] {M = 2'b11, S = 2'b01, U = 2'b00} privilege_t;

typedef struct packed {
    logic haltreq;
    logic resumereq;
    logic hartreset;
    logic ackhavereset;
    logic _27;
    logic hasel; // tie to zero
    logic [25:16] hartsello;
    logic [15:6] hartselhi; // should make all 0 except hartsel[0]
    logic [5:4] _5_4;
    logic setresethaltreq;
    logic clrresethaltreq;
    logic ndmreset;
    logic dmactive;
} dmcontrol_t;

typedef struct packed {
    logic [31:29] _31_29;
    logic [28:24] progbufsize; // hardwire to 0
    logic [23:13] _23_13;
    logic busy;
    logic _11;
    logic [10:8] cmderr;
    logic [7:4] _7_4;
    logic [3:0] datacount; // hard wire to any of 1-12 (I implement 3 registers)
} abstractcs_t;

typedef struct packed {
    logic [31:24] cmdtype;
    logic [23:0] control;
} command_t;

typedef struct packed {
    logic _23;
    logic [22:20] aarsize;
    logic aarpostincrement;
    logic postexec;
    logic transfer;
    logic write;
    logic [15:0] regno;
} access_register_command_control_t;

typedef struct packed {
    logic aamvirtual; // must fail if virtual
    logic [22:20] aamsize;
    logic aampostincrement;
    logic [18:17] _18_17;
    logic write;
    logic [15:14] _target_specific;
    logic [13:0] _13_0;
} access_memory_command_control_t;

typedef struct packed {
    logic [31:29] sbversion; // tie to one
    logic [28:23] _28_23;
    logic sbbusyerror;
    logic sbbusy;
    logic sbreadonaddr;
    logic [19:17] sbaccess;
    logic sbautoincrement;
    logic sbreadondata;
    logic [14:12] sberror;
    logic [11:5] sbasize; // 32
    logic sbaccess128;
    logic sbaccess64;
    logic sbaccess32; // only supported, rest 0s
    logic sbaccess16;
    logic sbaccess8;
} sbcs_t;

typedef struct packed {
    logic [31:23] _31_23;
    logic impebreak;
    logic [21:20] _21_20;
    logic allhavereset;
    logic anyhavereset;
    logic allresumeack;
    logic anyresumeack;
    logic allnonexistent;
    logic anynonexistent;
    logic allunavail;
    logic anyunavail;
    logic allrunning;
    logic anyrunning;
    logic allhalted;
    logic anyhalted;
    logic authenticated;
    logic authbusy;
    logic hasresethaltreq;
    logic confstrptrvalid;
    logic [3:0] version;
} dmstatus_t;

typedef struct packed {
    logic [31:24] _31_24;
    logic [23:20] nscratch;
    logic [19:17] _19_17;
    logic dataaccess;
    logic [15:12] datasize;
    logic [11:0] dataaddr;
} hartinfo_t;

endpackage
