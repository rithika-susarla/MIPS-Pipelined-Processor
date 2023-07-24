`timescale 1ns / 1ps

////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer:
//
// Create Date:   12:10:39 03/30/2023
// Design Name:  
// Module Name:   
// Project Name:  
// Target Device:  
// Tool versions:  
// Description: 
//
// Verilog Test Fixture created by ISE for module: insfetch
//
// Dependencies:
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
////////////////////////////////////////////////////////////////////////////////

module PLcpu_tb;

	// Inputs
	reg clk; reg reset; reg [31:0] PCin;

	// Outputs
wire [31:0] instructions;
wire [31:0] ALUout; wire [31:0] if_output; wire [31:0] operand_1; wire [31:0] operand_2; wire [31:0] aluout;
wire [31:0] read_data; wire [31:0] reg4; wire [31:0] reg5; wire [31:0] reg6; 
wire [31:0] mem1; wire [31:0] mem2; wire [31:0] mem3; wire [31:0] pcout;
	// Instantiate the Unit Under Test (UUT)
	PLDataPath uut (
		.clk(clk),
		.PCin(PCin),
		.reset(reset),
		.instruction(instructions),
		.result(ALUout),
		.if_output(if_output),
		.operand_1(operand_1),	
		.operand_2(operand_2),
		.aluout(aluout),
		.read_data(read_data),
		.reg4(reg4),
		.reg5(reg5),
		.reg6(reg6),
		.mem1(mem1),
		.mem2(mem2),
		.mem3(mem3),
		.pcout(pcout)
		
	);
	   

		//
		initial begin
		reset = 1'b1;
		#10 reset = 1'b0;
		#8 reset = 1'b0;
		#10 reset = 1'b0;
		end
		//start PC from first instruction
		initial begin
		PCin = 32'b0;
		end
		
		initial begin
		clk = 1'b0;
		repeat(60) #5 clk = ~clk;
		$finish;
		end

endmodule
