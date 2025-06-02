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

interface master_bus_if(input bclk, input brst_n);
    logic [31:0] wdata, rdata;
    logic [31:0] addr;
    tsize_e tsize;
    logic berror, bdone, bstart, bgnt, breq;
    
    modport master(
        output wdata, addr, bstart, tsize, breq,
        input rdata, berror, bdone, bgnt, bclk
    );
    
    modport ic(
        input wdata, addr, bstart, tsize, breq,
        output rdata, berror, bdone, bgnt
    );
endinterface

interface slave_bus_if(input bclk, input brst_n);
    logic [31:0] wdata, rdata;
    logic [31:0] addr;
    tsize_e tsize;
    logic berror, bdone, bstart, ss;
    
    modport ic(
        output wdata, addr, bstart, tsize, ss,
        input rdata, berror, bdone
    );
    
    modport slave(
        input wdata, addr, bstart, tsize, ss, bclk,
        output rdata, berror, bdone
    );
endinterface
