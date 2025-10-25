import instructions::*;

module csr #(parameter int unsigned MHARTID = 0, MVENDORID = 0, MARCHID = 0) (
    input bit clk,
    input bit rst_n,

    input bit wr,
    input bit [11:0] address,
    input bit [31:0] wrdata,
    input [31:0] pc,
    input bit interrupt,

    input logic dbg,
    input logic [8:6] dbg_cause,

    input bit return_from_interrupt,
    input privilege_t privilege,
    input xEIP, xTIP, xSIP,
    output bit [31:0] out,

    output mstatus_t o_mstatus,
    output logic [31:0] o_mie, o_mip,
    output mtvec_t o_mtvec,
    output mcause_t o_mcause,
    output bit [31:0] o_mepc, o_dpc,
    output dcsr_t o_dcsr
);

always_comb begin
    o_mcause = mcause;
    o_mie = mie;
    o_mip = mip;
    o_mstatus = mstatus;
    o_mtvec = mtvec;
    o_mepc = mepc;
    o_dpc = dpc;
end

logic [31:0] mvendorid, marchid, mhartid, mepc, dpc, dscratch0, dscratch1;

mip_t mip;
mie_t mie;
misa_t misa;
mstatus_t mstatus;
mtvec_t mtvec;
mcause_t mcause;
dcsr_t dcsr;

always_comb misa = {2'b01, 4'b0000, 26'b00000000000000000100000000}; // only RV32I implemented

always_comb begin
    case(address)
        12'hF11: out = mvendorid;
        12'hF12: out = marchid;
        12'hF14: out = mhartid;
        12'h300: out = mstatus;
        12'h301: out = misa;
        12'h304: out = mie;
        12'h305: out = mtvec;
        12'h341: out = mepc;
        12'h342: out = mcause;
        12'h344: out = mip;
        12'h7b0: out = dcsr;
        12'h7b1: out = dpc;
        12'h7b2: out = dscratch0;
        12'h7b3: out = dscratch1;
        default: out = 0; 
    endcase
end

always_ff @(posedge clk, negedge rst_n)
    if (!rst_n) begin
        mvendorid <= MVENDORID;
        marchid <= MARCHID;
        mhartid <= MHARTID;
        mepc <= 0;
        mip <= 0;
        mie <= 0;
        mstatus <= 0;
        mtvec <= 0;
        mcause <= 0;
    end else begin
        case(privilege)
            M: begin
                mip.MEIP <= mip.MEIP | xEIP;
                mip.MTIP <= mip.MTIP | xTIP;
                mip.MSIP <= mip.MSIP | xSIP;
            end
        endcase

        if (return_from_interrupt) begin
            // TODO: privilege restore
            mstatus.MIE <= mstatus.MPIE;
        end else if (interrupt) begin
            mepc <= pc;
            mstatus.MPP <= privilege;
            mstatus.MPIE <= mstatus.MIE;
            mstatus.MIE <= 0;
        end else if (dbg) begin
            dpc <= pc;
            dcsr.cause <= dbg_cause;
        end else if (wr) begin
            case(address)
                12'h300: mstatus <= wrdata;
                12'h304: mie <= wrdata;
                12'h305: mtvec <= wrdata;
                12'h341: mepc <= wrdata;
                12'h342: mcause <= wrdata;
                12'h344: mip <= wrdata;
                12'h7b0: dcsr <= wrdata;
                12'h7b1: dpc <= wrdata;
                12'h7b2: dscratch0 <= wrdata;
                12'h7b3: dscratch1 <= wrdata;
            endcase
        end
    end

endmodule