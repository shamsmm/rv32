import instructions::*;

module csr #(parameter int unsigned MHARTID = 0, MVENDORID = 0, MARCHID = 0) (
    input bit clk,
    input bit rst_n,

    input bit wr,
    input bit [11:0] address,
    input bit [31:0] wrdata,
    input [31:0] pc,
    input bit interrupt,
    input bit return_from_interrupt,
    input privilege_t privilege,
    input xEIP, xTIP, xSIP,
    output bit [31:0] out,

    output mstatus_t o_mstatus,
    output logic [31:0] o_mie, o_mip,
    output mtvec_t o_mtvec,
    output mcause_t o_mcause,
    output bit [31:0] o_mepc
);

always_comb begin
    o_mcause = mcause;
    o_mie = mie;
    o_mip = mip;
    o_mstatus = mstatus;
    o_mtvec = mtvec;
    o_mepc = mepc;
end

logic [31:0] mvendorid, marchid, mhartid, mepc;

mip_t mip;
mie_t mie;
mstatus_t mstatus;
mtvec_t mtvec;
mcause_t mcause;

always_comb begin
    case(address)
        12'hF11: out = mvendorid;
        12'hF12: out = marchid;
        12'hF14: out = mhartid;
        12'h300: out = mstatus;
        12'h304: out = mie;
        12'h305: out = mtvec;
        12'h341: out = mepc;
        12'h342: out = mcause;
        12'h344: out = mip;
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
        end else if (wr) begin
            case(address)
                12'h300: mstatus <= wrdata;
                12'h304: mie <= wrdata;
                12'h305: mtvec <= wrdata;
                12'h341: mepc <= wrdata;
                12'h342: mcause <= wrdata;
                12'h344: mip <= wrdata;
            endcase
        end
    end

endmodule