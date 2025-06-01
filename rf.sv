module rf(
    input logic [19:15] rs1,
    input logic [24:20] rs2,
    input logic [11:7] rd,
    input logic wr,
    input logic [31:0] wrdata,
    output logic [31:0] r1,
    output logic [31:0] r2
);

logic [31:0][0:31] data;

assign r1 = data[rs1];
assign r2 = data[rs2];

always_ff @(posedge clk or negedge rst_n)
    if (!rst_n)
        for(int i = 0; i < 32; i++)
            data[i] <= 0;
    else
        if (wr)
            data[rd] <= wrdata;

endmodule