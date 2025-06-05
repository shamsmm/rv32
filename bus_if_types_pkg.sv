package bus_if_types_pkg;

typedef enum logic [1:0] {
    BYTE = 0,
    HALFWORD = 1,
    WORD = 2
} tsize_e;

typedef enum logic {
    READ = 0,
    WRITE = 1
} ttype_e;

typedef struct {
    tsize_e tsize;
    ttype_e ttype;
    logic [31:0] data;
    logic [31:0] rdata;
} transaction;

endpackage
