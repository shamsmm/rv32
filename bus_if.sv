interface bus_if(input clk, input rst_n);

typedef enum {
    BYTE = 0,
    HALFWORD = 1,
    WORD = 2
} tsize_t; // transaction size

logic [31:0] wdata, rdata;
logic [31:0] addr;
logic berror, bdone, bstart;
tsize_t tsize;

modport master(output wdata, output addr, output bstart, output tsize, input rdata, input berror, input bdone);

endinterface
