`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 30.03.2023 18:22:42
// Design Name: 
// Module Name: main
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////

module instrmem(pc, instructions);
input [31:0] pc;
output wire [31:0] instructions;
reg [7:0] Mem [128:0];
initial $readmemb("ins.mem",Mem);
assign instructions={Mem[pc], Mem[pc+1], Mem[pc+2], Mem[pc+3]};
endmodule

module logic_right_shift(
    output [31:0]out,
    input [31:0]in,
    input arith,
    input [5:0] s
    );
    wire [31:0]w0,w1,w2,w3,w4;
    wire z;
    assign z = arith & in[31];
    mux_2_1_32b u0(w0,in,{32{z}},s[5]);
    mux_2_1_32b u1(w1,w0,{{16{z}}, w0[31:16]},s[4]);
    mux_2_1_32b u2(w2,w1,{{8{z}}, w1[31:8]},s[3]);
    mux_2_1_32b u3(w3,w2,{{4{z}}, w2[31:4]},s[2]);
    mux_2_1_32b u4(w4,w3,{{2{z}}, w3[31:2]}, s[1]);
    mux_2_1_32b u5(out,w4,{z, w4[31:1]}, s[0]);
endmodule

module logic_left_shift(
    output [31:0]out,
    input [31:0]in,
    input [5:0] s
    );
    
    wire [31:0]w0,w1,w2,w3,w4;
    wire z;
    
    assign z=0;
    
    mux_2_1_32b u0(w0,in,{32{z}},s[5]);
    mux_2_1_32b u1(w1,w0,{in[15:0], {16{z}}},s[4]);
    mux_2_1_32b u2(w2,w1,{w1[23:0],{8{z}}},s[3]);
    mux_2_1_32b u3(w3,w2,{w2[27:0],{4{z}}},s[2]);
    mux_2_1_32b u4(w4,w3,{w3[29:0],{2{z}}},s[1]);
    mux_2_1_32b u5(out,w4,{w4[30:0],z},s[0]);
    
endmodule


module barrel_shifter(
    output [31:0]out0,
    output [31:0]out1,
    output [31:0]out,
    input [31:0]in,
    input arith,
    input [5:0] s,
    input sel
    );
    
    wire [31:0]w1,w2;
    
    logic_right_shift u1(out0,in,arith,s);
    logic_left_shift u2(out1,in,s); 
    mux_2_1_32b u3(out,out0,out1,sel); 
endmodule

module mux_2_1_32b#(parameter N=32)(
    output [N-1 : 0] out,
    input [N-1 : 0] in0,
    input [N-1 : 0] in1,
    input sel
    );
    assign out  = sel ? in1 : in0;
endmodule

 module PLDataPath(
 input clk, input [31:0] PCin,  input reset,// main inputs
 output reg [31:0] result, output wire [31:0] instruction,
 output wire [31:0] if_output, output wire [31:0] operand_1, output wire [31:0] operand_2, output wire [31:0] aluout,
 output wire [31:0] read_data, output wire [31:0] reg4, output wire [31:0] reg5, output wire [31:0] reg6,
 output wire [31:0] mem1, output wire [31:0] mem2, output wire [31:0] mem3,output wire [31:0] pcout); 

reg [3:0] alucontrol; 

reg lr; reg ar; //control signals
reg [1:0] aluop; //reg MemtoReg; reg MemRead;
reg [1:0] PCsrc; 
wire [31:0] pcmodjump; wire [31:0] pcmodbranch;


reg [31:0] aluin2; //output of alusrc mux

reg [7:0] dMem [31:0]; //Data Memory
wire [31:0] instructions; wire [31:0] Lshiftres; wire [31:0] Rshiftres; 
wire [31:0] Bshiftres; wire [31:0] Bshiftres1; wire [31:0] Bshiftres2; //wires for calculating shifter results


initial $readmemb("data.mem",dMem); //read data memory

//reg [5:0] opcode;
//reg [5:0] funct;
//reg [5:0] shamt; 
//reg [4:0] Read_Reg_Num_1;
//reg [4:0] Read_Reg_Num_2;
//reg [4:0] Write_Reg_Num;
//initial Write_Reg_Num<=5'b0;
reg [31:0] extended; //register for sign extended offset
initial extended<=32'b0;// instruction sections


//Pipeline registers
reg [120:0] ifid;
reg [240:0] idex;
reg [200:0] exmem;
reg [200:0] memwb;

initial begin
ifid=120'b0;
idex=240'b0;
exmem=200'b0;
memwb=200'b0;
end

reg [31:0] pc;
reg [31:0] regmem [31:0];

initial pc<=PCin;

// reset function
always @(reset)
begin
if (reset)
begin
 pc<=32'b0;
// jumpAdd<=32'b0;
// BranchAdd<=32'b0;
// jump<=0;
// zero<=0;
// Branch<=0;
// shamt<=6'b0;
 lr<=0;
 ar<=0;
 regmem[0] <= 32'h0; //always zero, do not use for any other computation
 regmem[1] <= 32'h0;//64767000;
 regmem[2] <= 32'h0;//ha4d3a4a3;
 regmem[3] <= 32'h0;//90203898;
 regmem[4] <= 32'h0;//90203898;
 regmem[5] <= 32'h0;//99554407;
 regmem[6] <= 32'h0;
 regmem[7] <= 32'h0;
 regmem[8] <= 32'h0;
 regmem[9] <= 32'h0;
 regmem[10] <= 32'h0;
 regmem[11] <= 32'h0;
 regmem[12] <= 32'h0;
 end
 end



// start of IF stage //
instrmem insr(pc, instructions);

always @(posedge clk)
pc<=pc+3'b100;

always@(posedge clk, PCsrc)
begin
if (PCsrc==2'b01) // for branch
pc[31:0]<=pcmodbranch[31:0];
else if (PCsrc==2'b11) //for jump
pc[31:0]<=pcmodjump[31:0];
end

//now write to If/ID pipeline register
always@(posedge clk) begin
ifid[31:0]<=instructions[31:0];
ifid[63:32]<=pc[31:0];
end
// end of IF stage //





// beginning of ID stage //

//idex components

// idex[31:0]=data1
// idex[63:32]=data2
// idex[95:64]=extended
// idex[100:96]=writereg1
// idex[105:101]=writereg2
// idex[137:106]=pc
// idex[138]=RegDst
// idex[139]=AluSrc
// idex[140]=MemWrite
// idex[142:141]=aluop
// idex[143]=MemtoReg
// idex[144]=MemRead
// idex[145]=jump
// idex[146]=Branch
// idex[147]=RegWrite
// idex[179:148]=jumpadd
//idex[211:180]=branchadd
//idex[217:213]=shamt
//idex[222:218]=regnum for data1 or ifid[25:21]
//idex[227:223]=regnum for data2 or ifid[20:16]

always@(posedge clk)
 begin
 idex[31:0]<=regmem[ifid[25:21]]; //data1
 idex[63:32]<=regmem[ifid[20:16]]; //data2
 idex[222:218]<=ifid[25:21]; //data1 reg number
 idex[227:223]<=ifid[20:16]; //data2 regnumber
 idex[100:96]<=ifid[20:16];
 idex[105:101]<=ifid[15:11];
 idex[137:106]<=ifid[63:32];
end

always @(posedge clk)
begin
idex[79:64]<= ifid [15:0];
idex[217:213]<= ifid[10:6];
idex[175:148]<=ifid[25:0]<<2;
idex[195:182]<=ifid[13:0];
end

always@(posedge clk)
begin
idex[179:176]<=ifid[63:60];
end

//generate control signals
always @(posedge clk)
begin
//opcode<=ifid[31:26];
 case (ifid[31:26])
 6'b000000://r-type
 begin
 idex[138]<=1;
 idex[147]<=1;
 idex[139]<=0;
 idex[140]<=0;
 idex[142:141]<=2'b10;
 idex[143]<=0;
 idex[144]<=0;
 idex[145]<=0;
 idex[146]<=0;
 end
 
 6'b100011://load
 begin
 idex[138]<=0;
 idex[147]<=1;
 idex[139]<=1;
 idex[140]<=0;
 idex[142:141]<=2'b00;
 idex[143]<=1;
 idex[144]<=1;
 idex[145]<=0;
 idex[146]<=0;
 end
 
 6'b101011://store
 begin
 idex[138]<=0;
 idex[147]<=0;
 idex[139]<=1;
 idex[140]<=1;
 idex[142:141]<=2'b00;
 idex[143]<=0;
 idex[144]<=0;
 idex[145]<=0;
 idex[146]<=0;
 end
 
 6'b000010://jump
 begin
 idex[138]<=0;
 idex[147]<=0;
 idex[139]<=0;
 idex[140]<=0;
 idex[142:141]<=2'b00;
 idex[143]<=0;
 idex[144]<=0;
 idex[145]<=1;
 idex[146]<=0;
 end
 
 6'b000100://bne
 begin
 idex[138]<=0;
 idex[147]<=0;
 idex[139]<=0;
 idex[140]<=0;
 idex[142:141]<=2'b01;
 idex[143]<=0;
 idex[144]<=0;
 idex[145]<=0;
 idex[146]<=1;
 end
 
 6'b000101://beq
 begin
 idex[138]<=0;
 idex[147]<=0;
 idex[139]<=0;
 idex[140]<=0;
 idex[142:141]<=2'b11;
 idex[143]<=0;
 idex[144]<=0;
 idex[145]<=0;
 idex[146]<=1;
 end
 
  6'b001000: //addi
 begin
 idex[138]<=0;
 idex[147]<=1;
 idex[139]<=1;
 idex[140]<=0;
 idex[142:141]<=2'b00;
 idex[143]<=0;
 idex[144]<=0;
 idex[145]<=0;
 idex[146]<=0;
 end
 
 6'b001001: //subi
 begin
 idex[138]<=0;
 idex[147]<=1;
 idex[139]<=1;
 idex[140]<=0;
 idex[142:141]<=2'b01;
 idex[143]<=0;
 idex[144]<=0;
 idex[145]<=0;
 idex[146]<=0;
 end
 
 6'b111111: //nop
 begin
 idex[138]<=0;
 idex[147]<=0;
 idex[139]<=0;
 idex[140]<=0;
 idex[142:141]<=2'b00;
 idex[143]<=0;
 idex[144]<=0;
 idex[145]<=0;
 idex[146]<=0;
 end
 
 endcase
end
// end of ID stage //




//start of EX stage //


//exmem components

//exmem[31:0] pcmod for branch         
//exmem[63:32] data2
//exmem[95:64] result
//exmem[96] zero
//exmem[128:97] branchadd
//exmem[129] regwrite
//exmem[130] branch
//exmem[131] memread
//exmem[132] memwrite
//exmem[137:133] writeregnum
//exmem[169:138] pcmod for jump
//exmem[170] jump [170]
//exmem[171] memtoreg idex[143] [171]






always@(posedge clk)begin
exmem[31:0]<=pc+idex[211:180];//idex[137:106]+(idex[211:180]); //final pc for branch
exmem[169:138]<=pc+idex[179:148];//idex[137:106]+(idex[179:148]); //final pc for jump
end
//generate alucontrol
always @(posedge clk, instructions)
begin
case(idex[142:141])
2'b00: alucontrol<=4'b0010;
2'b01: alucontrol<=4'b0100;
2'b11: alucontrol<=4'b0101;
2'b10:
if (idex[69:64]==6'b100000)
    alucontrol<=4'b0010;
else if (idex[69:64]==6'b100010)
    alucontrol<=4'b0110;
else if (idex[69:64]==6'b100100)
    alucontrol<=4'b0000;
else if (idex[69:64]==6'b100101)
    alucontrol<=4'b0001;
else if (idex[69:64]==6'b101010)
    alucontrol<=4'b0111;
else if (idex[69:64]==6'b010100)
    alucontrol<=4'b1000;
else if (idex[69:64]==6'b010101)
    alucontrol<=4'b1001;
else if (idex[69:64]==6'b010111)
    alucontrol<=4'b1010;
endcase
end

assign pcmodjump[31:0]= exmem[170]? exmem[169:138]+3'b100: 32'b0;
assign pcmodbranch[31:0]= (exmem[130]&&exmem[96]) ? exmem[31:0]+3'b100: 32'b0;

//regdst mux

always@(posedge clk)
begin
 if (idex[138])
   exmem[137:133]<=idex[105:101];
 if (idex[138]!=1)
   exmem[137:133]<=idex[100:96];
 end

//beginning of forwarding stage //
reg [31:0] aluout1;
reg [31:0] aluout2;
initial begin
aluout2=0;
aluout1=0;
end
always @(*) begin
if(idex[227:223]!=0)
aluout2[5:0]<=idex[227:223];
if(idex[222:218]!=0)
aluout1[5:0]<=idex[222:218];
end

reg [31:0] idex_input1;
reg [31:0] idex_input2;
initial begin
 idex_input1=0;
 idex_input2=0;
 end

always @(*)begin
    if (memwb[71]) begin //using memwrite from exmem as a condition for forwarding memwb or exmem
        if (aluout2[5:0]==memwb[36:32]!=0) begin
            idex_input2[31:0]<=memwb[68:37];
            idex_input1[31:0]<=idex[31:0];
            end
        else if(aluout1[5:0]==memwb[36:32]!=0) begin
            idex_input1[31:0]<=memwb[68:37];
            idex_input2[31:0]<=idex[63:32];
            end
        else begin
            idex_input1[31:0]<=idex[31:0];
            idex_input2[31:0]<=idex[63:32];
            end
    end
    else
        if (aluout2[5:0]==exmem[137:133]!=0) begin
            idex_input2[31:0]<=exmem[95:64];
            idex_input1[31:0]<=idex[31:0];
            end
        else if(aluout1[5:0]==exmem[137:133]!=0) begin
            idex_input1[31:0]<=exmem[95:64];
            idex_input2[31:0]<=idex[63:32];
            end
        else begin
            idex_input1[31:0]<=idex[31:0];
            idex_input2[31:0]<=idex[63:32];
            end
end

 always@(posedge clk, alucontrol, idex[139], idex_input2[31:0])//, resultemp[31:0], aluin2)
begin
if (idex[139])
aluin2<=idex[95:64];
else
aluin2<=idex_input2[31:0];

end

wire [31:0] Out_2;
assign Out_2=idex_input2[31:0];
logic_left_shift ls(Lshiftres,Out_2, idex[217:213]);
logic_right_shift rs(Rshiftres,Out_2,ar,idex[217:213]);
barrel_shifter bs(Bshiftres1,Bshiftres2,Bshiftres,idex_input2[31:0], ar, idex[217:213], lr); //pre calculate shift values



//alu operations
reg [31:0] resultemp; //temporary register in order to maintain synchronization
always@(posedge clk, alucontrol, idex_input1[31:0], aluin2)
begin
case(alucontrol)
4'b0000:resultemp[31:0]<= idex_input1[31:0]&aluin2;
4'b0001:resultemp[31:0]<= idex_input1[31:0]|aluin2;
4'b0010:resultemp[31:0]<= idex_input1[31:0]+aluin2;
4'b0110:resultemp[31:0]<= idex_input1[31:0]-aluin2;
4'b1000: resultemp[31:0]<=Lshiftres;
4'b1001: 
begin
if(idex_input1[31:0]%2==0)
ar<=1;
else
ar<=0;
resultemp[31:0]<=Rshiftres;
end


4'b1010:
begin
if(idex_input1[31:0]%2==0)
begin
lr<=1;
ar<=1;
end
else
begin
lr<=0;
ar<=0;
resultemp[31:0]<=Bshiftres;
end
end


4'b0100:
begin
resultemp[31:0]<= idex_input1[31:0]-aluin2;
if (resultemp[31:0])
exmem[96]<=0;
else
exmem[96]<=1;
end


4'b0101:
begin
resultemp[31:0]<= idex_input1[31:0]-aluin2;
if (resultemp[31:0])
exmem[96]<=1;
else
exmem[96]<=0;
end

4'b0111:

if (idex_input1[31:0]<aluin2)
resultemp[31:0]<=1;
else
resultemp[31:0]<=0;
endcase
end

always@(posedge clk) begin
exmem[95:64]<=resultemp[31:0];
//forwarded signals from idex register  
exmem[132]<=idex[140]; //Memwrite
exmem[131]<=idex[144]; //Memread
exmem[129]<=idex[147]; //regwrite
exmem[130]<=idex[146]; //Branch
exmem[170]<=idex[145]; //jump
exmem[63:32]<=idex_input2[31:0]; //data2
exmem[171]<=idex[143]; // memtoreg 
//exmem[137:133]<=Write_Reg_Num;
end //used in order to ensure the stages are synchronized
// end of EX stage //



// start of MEM stage //

//memwb addersses
//memwb[31:0] alu result
//memwb[36:32] output of regdst mux, exmem[137:133]
//memwb[68:37] read data
//memwb[69] regwrite, exmem[129] 
//memwb[70] memtoreg exmem[171] 
//memwb[71] memread used as decider for forwarding block

always@(exmem[170], exmem[130], exmem[96])
begin
if (exmem[170])
PCsrc<=2'b11;        
else if (exmem[130] && exmem[96] ==1)
PCsrc<=2'b01;
else
PCsrc<=2'b00;
end

always @(posedge clk)
begin
memwb[71]<=exmem[131];
memwb[69]<=exmem[129];
memwb[70]<=exmem[171];
memwb[36:32]<=exmem[137:133];
memwb[31:0]<=exmem[95:64];
end

always@(posedge clk)//, exmem[132], exmem[131])
begin
if (exmem[132])
{dMem[(4*memwb[31:0])], dMem[(4*memwb[31:0])+1], dMem[(4*memwb[31:0])+2], dMem[(4*memwb[31:0])+3]}<=exmem[63:32]; //write
if (exmem[131])
memwb[68:37]<={dMem[(4*exmem[95:64])], dMem[(4*exmem[95:64])+1], dMem[(4*exmem[95:64])+2], dMem[(4*exmem[95:64])+3]};
end
//end of MEM stage //


//start of WB stage//

//write to registers
always @(posedge clk)//, memwb[70], memwb[31:0], memwb[69])
begin

if (memwb[69])
begin
       if(memwb[70])
        regmem[memwb[36:32]]<=memwb[68:37];
        else
        regmem[memwb[36:32]]<=memwb[31:0];
end
end


 //testing code to view memory and registers in waveforms
assign instruction=instructions;
assign if_output=ifid[31:0];
assign operand_1=idex_input1[31:0];
assign operand_2=aluin2;
assign aluout=resultemp[31:0];//exmem[95:64];//resultemp[31:0];//
assign read_data=memwb[68:37];
assign reg4=regmem[4];
assign reg5=regmem[5];
assign reg6=regmem[6];
assign mem1={dMem[4], dMem[5], dMem[6], dMem[7]};
assign mem2={dMem[8], dMem[9], dMem[10], dMem[11]};
assign mem3={dMem[12], dMem[13], dMem[14], dMem[15]};
assign pcout=pc;
 endmodule
