module clint (
    slave_bus_if.slave bus,
    input bit clk,
    input bit rst_n,
    output bit irq_sw = 1'b0,
    output bit irq_timer
);
    
logic [31:0] mtime, mtimecmp;

assign irq_timer = mtime >= mtimecmp;

always_comb begin
    bus.bdone = 1'b1; // all thing take one clock cycle
    bus.rdata = 32'b0;

    case(bus.addr[27:0])
        28'h2004000: bus.rdata = mtimecmp; // TODO: should be 64-bit wide but we violate spec here
        28'h200BFF8: bus.rdata = mtime;
    endcase
end

always_ff @( posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        mtime <= 0;
        mtimecmp <= 0;
    end
    else begin 
        mtime <= mtime + 1; // TODO: make sure synthesis prioritizes last NBA
        
        if (bus.ss && bus.ttype == WRITE) begin
            case(bus.addr[27:0])
                28'h2004000: mtimecmp <= bus.wdata;
                28'h200BFF8: mtime <= bus.wdata;
            endcase
        end
    end
end

endmodule