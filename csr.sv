import instructions::*;

module csr(
    input bit clk,
    input bit rst_n,

    input bit wr,
    input bit [11:0] address,
    input bit [31:0] wrdata,
    output bit [31:0] out,

    output mstatus_t o_mstatus,
    output logic [31:0] o_mie, o_mip,
    output mtvec_t o_mtvec,
    output mcause_t o_mcause
);

localparam MVENDORID = 0;
localparam MARCHID = 0;

always_comb begin
    o_mcause = mcause;
    o_mie = mie;
    o_mip = mip;
    o_mstatus = mstatus;
    o_mtvec = mtvec;
end

logic [31:0] mvendorid, marchid, mstatus, mie, mip, mtvec, mcause, mhartid;

always_comb begin
    case(address)
        12'hF11: out = mvendorid;
        12'hF12: out = marchid;
        12'h300: out = mstatus;
        12'h304: out = mie;
        12'h305: out = mtvec;
        default: out = 0; 
    endcase
end

always_ff @(posedge clk, negedge rst_n)
    if (!rst_n) begin
        mvendorid <= MVENDORID;
        marchid <= MARCHID;
    end else if (wr) begin
        case(address)
            12'h300: mstatus <= wrdata;
            12'h304: mie <= wrdata;
            12'h305: mtvec <= wrdata;
        endcase
    end

endmodule