module rv_core(bus_if.master bus, input clk,);

logic instruction;

logic [31:0] zero_extend = {24'b0, imm};
logic [31:0] sign_extend = imm[11] ? { 24{1'b1}, imm} : {24{0}, imm};

control_unit cu(.*);
register_file rf(.*);
alu alu(.*);

logic [31:0] pc;

logic next_pc;

endmodule
