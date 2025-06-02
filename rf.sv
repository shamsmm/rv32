module rf(
    input logic [19:15] rs1,
    input logic [24:20] rs2,
    input logic [11:7] rd,
    input logic wr,
    input logic [31:0] wrdata,
    input logic clk,
    input logic rst_n,
    output logic [31:0] r1,
    output logic [31:0] r2
);

logic [31:0][31:1] data;

assign r1 = rs1 == 0 ? 0 : data[rs1];
assign r2 = rs2 == 0 ? 0 : data[rs2];

always_ff @(posedge clk or negedge rst_n)
    if (!rst_n)
        for(int i = 1; i < 32; i++)
            data[i] <= 0;
    else
        if (wr && rd != 0)
            data[rd] <= wrdata;

endmodule