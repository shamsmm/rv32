import bus_if_types_pkg::*;

interface master_bus_if(input bclk, input brst_n);
    logic [31:0] wdata, rdata;
    logic [31:0] addr;
    tsize_e tsize;
    ttype_e ttype;
    logic berror, bdone, bstart, bgnt, breq;

    modport master(
        output wdata, addr, bstart, tsize, ttype, breq,
        input rdata, berror, bdone, bgnt, bclk
    );

    modport ic(
        input wdata, addr, bstart, tsize, ttype, breq,
        output rdata, berror, bdone, bgnt
    );
endinterface

interface slave_bus_if(input bclk, input brst_n);
    logic [31:0] wdata, rdata;
    logic [31:0] addr;
    tsize_e tsize;
    ttype_e ttype;
    logic berror, bdone, bstart, ss;

    modport ic(
        output wdata, addr, bstart, tsize, ttype, ss,
        input rdata, berror, bdone
    );

    modport slave(
        input wdata, addr, bstart, tsize, ttype, ss, bclk,
        output rdata, berror, bdone
    );
endinterface