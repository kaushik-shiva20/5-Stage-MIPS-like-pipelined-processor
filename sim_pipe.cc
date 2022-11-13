#include "sim_pipe.h"
#include <stdlib.h>
#include <iostream>
#include <fstream>
#include <cstring>
#include <string>
#include <iomanip>
#include <map>

//#define DEBUG
#define  IS_OPCODE_BRANCH(instr)    (instr.opcode == BLTZ || instr.opcode == BNEZ || \
                                     instr.opcode == BGTZ || instr.opcode == BEQZ || \
                                     instr.opcode == BGEZ || instr.opcode == BLEZ || \
                                     instr.opcode == JUMP)

#define  IS_OPCODE_ALU(instr)       (instr.opcode == ADD || instr.opcode == SUB || \
                                     instr.opcode == XOR)

#define  IS_OPCODE_ALU_IMM(instr)   (instr.opcode == ADDI || instr.opcode == SUBI)
#define  IS_OPCODE_MEM(instr)       (instr.opcode == LW || instr.opcode == SW)
using namespace std;


unsigned mInstruction_Count=0;
unsigned mClock_Cycles=0;
unsigned mStalls_Count=0;
unsigned is_memory_ongoing = FALSE;
unsigned is_branch_ongoing = FALSE;
unsigned is_branch_calculated = FALSE;
//used for debugging purposes
static const char *reg_names[NUM_SP_REGISTERS] = {"PC", "NPC", "IR", "A", "B", "IMM", "COND", "ALU_OUTPUT", "LMD"};
static const char *stage_names[NUM_STAGES] = {"IF", "ID", "EX", "MEM", "WB"};
static const char *instr_names[NUM_OPCODES] = {"LW", "SW", "ADD", "ADDI", "SUB", "SUBI", "XOR", "BEQZ", "BNEZ", "BLTZ", "BGTZ", "BLEZ", "BGEZ", "JUMP", "EOP", "NOP"};

/* =============================================================

   HELPER FUNCTIONS

   ============================================================= */
void pipe_IF_Handler(sim_pipe* mSimPipe);
void pipe_ID_Handler(sim_pipe* mSimPipe);
void pipe_EXE_Handler(sim_pipe* mSimPipe);
void pipe_MEM_Handler(sim_pipe* mSimPipe);
void pipe_WB_Handler(sim_pipe* mSimPipe);
unsigned alu_compute_cond(opcode_t mOpCode, int mSrc);

/* converts integer into array of unsigned char - little indian */
inline void int2char(unsigned value, unsigned char *buffer){
	memcpy(buffer, &value, sizeof value);
}

/* converts array of char into integer - little indian */
inline unsigned char2int(unsigned char *buffer){
	unsigned d;
	memcpy(&d, buffer, sizeof d);
	return d;
}

/* implements the ALU operations */
unsigned alu(unsigned opcode, unsigned a, unsigned b, unsigned imm, unsigned npc){
	switch(opcode){
			case ADD:
				return (a+b);
			case ADDI:
				return(a+imm);
			case SUB:
				return(a-b);
			case SUBI:
				return(a-imm);
			case XOR:
				return(a ^ b);
			case LW:
			case SW:
				return(a + imm);
			case BEQZ:
			case BNEZ:
			case BGTZ:
			case BGEZ:
			case BLTZ:
			case BLEZ:
			case JUMP:
				return(npc+imm);
			default:	
				return (-1);
	}
}

/* =============================================================

   CODE PROVIDED - NO NEED TO MODIFY FUNCTIONS BELOW

   ============================================================= */

/* loads the assembly program in file "filename" in instruction memory at the specified address */
void sim_pipe::load_program(const char *filename, unsigned base_address){

   /* initializing the base instruction address */
   instr_base_address = base_address;

   /* creating a map with the valid opcodes and with the valid labels */
   map<string, opcode_t> opcodes; //for opcodes
   map<string, unsigned> labels;  //for branches
   for (int i=0; i<NUM_OPCODES; i++)
	 opcodes[string(instr_names[i])]=(opcode_t)i;

   /* opening the assembly file */
   ifstream fin(filename, ios::in | ios::binary);
   if (!fin.is_open()) {
      cerr << "error: open file " << filename << " failed!" << endl;
      exit(-1);
   }

   /* parsing the assembly file line by line */
   string line;
   unsigned instruction_nr = 0;
   while (getline(fin,line)){
	// set the instruction field
	char *str = const_cast<char*>(line.c_str());

  	// tokenize the instruction
	char *token = strtok (str," \t");
	map<string, opcode_t>::iterator search = opcodes.find(token);
        if (search == opcodes.end()){
		// this is a label for a branch - extract it and save it in the labels map
		string label = string(token).substr(0, string(token).length() - 1);
		labels[label]=instruction_nr;
                // move to next token, which must be the instruction opcode
		token = strtok (NULL, " \t");
		search = opcodes.find(token);
		if (search == opcodes.end()) cout << "ERROR: invalid opcode: " << token << " !" << endl;
	}
	instr_memory[instruction_nr].opcode = search->second;

	//reading remaining parameters
	char *par1;
	char *par2;
	char *par3;
	switch(instr_memory[instruction_nr].opcode){
		case ADD:
		case SUB:
		case XOR:
			par1 = strtok (NULL, " \t");
			par2 = strtok (NULL, " \t");
			par3 = strtok (NULL, " \t");
			instr_memory[instruction_nr].dest = atoi(strtok(par1, "R"));
			instr_memory[instruction_nr].src1 = atoi(strtok(par2, "R"));
			instr_memory[instruction_nr].src2 = atoi(strtok(par3, "R"));
			break;
		case ADDI:
		case SUBI:
			par1 = strtok (NULL, " \t");
			par2 = strtok (NULL, " \t");
			par3 = strtok (NULL, " \t");
			instr_memory[instruction_nr].dest = atoi(strtok(par1, "R"));
			instr_memory[instruction_nr].src1 = atoi(strtok(par2, "R"));
			instr_memory[instruction_nr].immediate = strtoul (par3, NULL, 0);
			break;
		case LW:
			par1 = strtok (NULL, " \t");
			par2 = strtok (NULL, " \t");
			instr_memory[instruction_nr].dest = atoi(strtok(par1, "R"));
			instr_memory[instruction_nr].immediate = strtoul(strtok(par2, "()"), NULL, 0);
			instr_memory[instruction_nr].src1 = atoi(strtok(NULL, "R"));
			break;
		case SW:
			par1 = strtok (NULL, " \t");
			par2 = strtok (NULL, " \t");
			instr_memory[instruction_nr].src1 = atoi(strtok(par1, "R"));
			instr_memory[instruction_nr].immediate = strtoul(strtok(par2, "()"), NULL, 0);
			instr_memory[instruction_nr].src2 = atoi(strtok(NULL, "R"));
			break;
		case BEQZ:
		case BNEZ:
		case BLTZ:
		case BGTZ:
		case BLEZ:
		case BGEZ:
			par1 = strtok (NULL, " \t");
			par2 = strtok (NULL, " \t");
			instr_memory[instruction_nr].src1 = atoi(strtok(par1, "R"));
			instr_memory[instruction_nr].label = par2;
			break;
		case JUMP:
			par2 = strtok (NULL, " \t");
			instr_memory[instruction_nr].label = par2;
		default:
			break;

	} 

	/* increment instruction number before moving to next line */
	instruction_nr++;
   }
   //reconstructing the labels of the branch operations
   int i = 0;
   while(true){
   	instruction_t instr = instr_memory[i];
	if (instr.opcode == EOP) break;
	if (instr.opcode == BLTZ || instr.opcode == BNEZ ||
            instr.opcode == BGTZ || instr.opcode == BEQZ ||
            instr.opcode == BGEZ || instr.opcode == BLEZ ||
            instr.opcode == JUMP
	 ){
		instr_memory[i].immediate = (labels[instr.label] - i - 1) << 2;
	}
        i++;
   }
    sim_pipe_pipeline_reg[IF].PC = instr_base_address;

}

/* writes an integer value to data memory at the specified address (use little-endian format: https://en.wikipedia.org/wiki/Endianness) */
void sim_pipe::write_memory(unsigned address, unsigned value){
	int2char(value,data_memory+address);
}

/* prints the content of the data memory within the specified address range */
void sim_pipe::print_memory(unsigned start_address, unsigned end_address){
	cout << "data_memory[0x" << hex << setw(8) << setfill('0') << start_address << ":0x" << hex << setw(8) << setfill('0') <<  end_address << "]" << endl;
	for (unsigned i=start_address; i<end_address; i++){
		if (i%4 == 0) cout << "0x" << hex << setw(8) << setfill('0') << i << ": "; 
		cout << hex << setw(2) << setfill('0') << int(data_memory[i]) << " ";
		if (i%4 == 3) cout << endl;
	} 
}

/* prints the values of the registers */
void sim_pipe::print_registers(){
        cout << "Special purpose registers:" << endl;
        unsigned i, s;
        for (s=0; s<NUM_STAGES; s++){
                cout << "Stage: " << stage_names[s] << endl;
                for (i=0; i< NUM_SP_REGISTERS; i++)
                        if ((sp_register_t)i != IR && (sp_register_t)i != COND && get_sp_register((sp_register_t)i, (stage_t)s)!=UNDEFINED) cout << reg_names[i] << " = " << dec <<  get_sp_register((sp_register_t)i, (stage_t)s) << hex << " / 0x" << get_sp_register((sp_register_t)i, (stage_t)s) << endl;
        }
        cout << "General purpose registers:" << endl;
        for (i=0; i< NUM_GP_REGISTERS; i++)
                if (get_gp_register(i)!=(int)UNDEFINED) cout << "R" << dec << i << " = " << get_gp_register(i) << hex << " / 0x" << get_gp_register(i) << endl;
}

/* initializes the pipeline simulator */
sim_pipe::sim_pipe(unsigned mem_size, unsigned mem_latency){
	data_memory_size = mem_size;
	data_memory_latency = mem_latency;
	data_memory = new unsigned char[data_memory_size];
    memset(data_memory,0xFF,data_memory_size*sizeof(unsigned char));
	reset();
}
	
/* deallocates the pipeline simulator */
sim_pipe::~sim_pipe(){
	delete [] data_memory;
}

/* =============================================================

   CODE TO BE COMPLETED

   ============================================================= */


/* body of the simulator */
void sim_pipe::run(unsigned cycles)
{
    stage_t mCurrStage = WB;
    unsigned j=0u;
    while((j<cycles) || ((cycles == 0u) && (sim_pipe_pipeline_reg[WB].IR.opcode != EOP)))
    {
        mClock_Cycles++;
        for (int i = 0; i < NUM_STAGES; i++)
        {
            switch (mCurrStage)
            {
                case IF:
                    pipe_IF_Handler(this);
                    mCurrStage = WB;
                    break;
                case ID:
                    pipe_ID_Handler(this);
                    mCurrStage = IF;
                    break;
                case EXE:
                    pipe_EXE_Handler(this);
                    mCurrStage = ID;
                    break;
                case MEM:
                    pipe_MEM_Handler(this);
                    mCurrStage = EXE;
                    break;
                case WB:
                    pipe_WB_Handler(this);
                    mCurrStage = MEM;
                    break;
                default:
                    cout << "error: run incorrect mCurrStage";
                    break;
            }
        }
        j++;
    }
    /*
    if(sim_pipe_pipeline_reg[WB].IR.opcode == EOP) {
        sim_pipe_pipeline_reg[IF].PC -=4;
        sim_pipe_pipeline_reg[ID].NPC -=4;
    }
    */
}
	
/* reset the state of the pipeline simulator */
void sim_pipe::reset(){
    
    /** Added Code Start **/
    /** Reset register file **/
    sim_pipe_reg_file[0].regVal = 0;
    sim_pipe_reg_file[0].isDestination = FALSE;
    for(int i=1;i<REGISTER_FILE_SIZE;i++)
    {
        sim_pipe_reg_file[i].regVal = UNDEFINED;
        sim_pipe_reg_file[i].isDestination = FALSE;
    }
    for(int i=0;i<NUM_STAGES;i++)
    {
        sim_pipe_pipeline_reg[i].PC = UNDEFINED;
        sim_pipe_pipeline_reg[i].NPC = UNDEFINED;
        sim_pipe_pipeline_reg[i].IR.opcode = NOP;
        sim_pipe_pipeline_reg[i].Rd = UNDEFINED;
        sim_pipe_pipeline_reg[i].Imm = UNDEFINED;
        sim_pipe_pipeline_reg[i].A = UNDEFINED;
        sim_pipe_pipeline_reg[i].B = UNDEFINED;
        sim_pipe_pipeline_reg[i].ALU_Output = UNDEFINED;
        sim_pipe_pipeline_reg[i].Cond = UNDEFINED;
        sim_pipe_pipeline_reg[i].LMD = UNDEFINED;
        sim_pipe_pipeline_reg[i].isAvailable = FALSE;
    }
    sim_pipe_pipeline_reg[IF].isAvailable = TRUE;
    /** Added Code End**/
}

//return value of special purpose register
unsigned sim_pipe::get_sp_register(sp_register_t reg, stage_t s){
    unsigned mRetVal=UNDEFINED;
    switch (reg) {
        case PC:
        {
            mRetVal = sim_pipe_pipeline_reg[s].PC;
            break;
        }

        case NPC:
        {
            mRetVal = sim_pipe_pipeline_reg[s].NPC;
            break;
        }

        case IR:
        {
            mRetVal = sim_pipe_pipeline_reg[s].IR.opcode;
            break;
        }

        case A:
        {
            mRetVal = sim_pipe_pipeline_reg[s].A;
            break;
        }

        case B:
        {
            mRetVal = sim_pipe_pipeline_reg[s].B;
            break;
        }

        case IMM:
        {
            mRetVal = sim_pipe_pipeline_reg[s].Imm;
            break;
        }

        case COND:
        {
            mRetVal = sim_pipe_pipeline_reg[s].Cond;
            break;
        }

        case ALU_OUTPUT:
        {
            mRetVal = sim_pipe_pipeline_reg[s].ALU_Output;
            break;
        }

        case LMD:
        {
            mRetVal = sim_pipe_pipeline_reg[s].LMD;
            break;
        }
        default:
            cout << "Error: get_sp_register invalid params";
            break;

    }
	return mRetVal; //please modify
}

//returns value of general purpose register
int sim_pipe::get_gp_register(unsigned reg){
    unsigned mRetVal;
    mRetVal = sim_pipe_reg_file[reg].regVal;
	return mRetVal; //please modify
}

void sim_pipe::set_gp_register(unsigned reg, int value){
    if(reg < REGISTER_FILE_SIZE)
    {
        sim_pipe_reg_file[reg].regVal = value;
    }else
    {
        //TODO: Error Handling
    }
}

float sim_pipe::get_IPC(){
        return ((float)mInstruction_Count/(float)(mInstruction_Count + mStalls_Count + 4)); //please modify
}

unsigned sim_pipe::get_instructions_executed(){
        return mInstruction_Count; //please modify
}

unsigned sim_pipe::get_stalls(){
        return mStalls_Count; //please modify
}

unsigned sim_pipe::get_clock_cycles(){
        return (mInstruction_Count + mStalls_Count + 4); //please modify
}

void pipe_IF_Handler(sim_pipe* mSimPipe)
{
    //TODO: Recheck this implementation
    if((mSimPipe->sim_pipe_pipeline_reg[IF].isAvailable == TRUE) )
    {
        if ((IS_OPCODE_BRANCH(mSimPipe->sim_pipe_pipeline_reg[ID].IR)) &&
            (mSimPipe->sim_pipe_pipeline_reg[MEM].Cond == 1))
        {
            mSimPipe->sim_pipe_pipeline_reg[MEM].Cond = 0;
            mSimPipe->sim_pipe_pipeline_reg[IF].PC = mSimPipe->sim_pipe_pipeline_reg[MEM].ALU_Output;
        }
        mSimPipe->sim_pipe_pipeline_reg[ID].IR = mSimPipe->instr_memory[(mSimPipe->sim_pipe_pipeline_reg[IF].PC - mSimPipe->instr_base_address)/4];
        mSimPipe->sim_pipe_pipeline_reg[ID].isAvailable = TRUE;
    }

    if((mSimPipe->sim_pipe_pipeline_reg[IF].isAvailable == TRUE) && (mSimPipe->sim_pipe_pipeline_reg[ID].IR.opcode != EOP))
    {
        mSimPipe->sim_pipe_pipeline_reg[IF].PC += 4;
        mSimPipe->sim_pipe_pipeline_reg[ID].NPC = mSimPipe->sim_pipe_pipeline_reg[IF].PC;
    }

    //Undef all unused pipeline registers TODO:Remove these as these aren't modified after reset
    /*
    mSimPipe->sim_pipe_pipeline_reg[ID].PC = UNDEFINED;
    mSimPipe->sim_pipe_pipeline_reg[ID].Rd = UNDEFINED;
    mSimPipe->sim_pipe_pipeline_reg[ID].Imm = UNDEFINED;
    mSimPipe->sim_pipe_pipeline_reg[ID].A = UNDEFINED;
    mSimPipe->sim_pipe_pipeline_reg[ID].B = UNDEFINED;
    mSimPipe->sim_pipe_pipeline_reg[ID].ALU_Output = UNDEFINED;
    mSimPipe->sim_pipe_pipeline_reg[ID].Cond = UNDEFINED;
    mSimPipe->sim_pipe_pipeline_reg[ID].LMD = UNDEFINED;
    */
}

void pipe_ID_Handler(sim_pipe* mSimPipe)
{
    unsigned temp;
    unsigned SW_Swap;
    unsigned tempSrc1;
    unsigned tempSrc2;
    static unsigned mControlDelay=0;

    /*Check any RAW hazards if not NOP and EOP instruction*/
    if((is_memory_ongoing == FALSE) && (mSimPipe->sim_pipe_pipeline_reg[ID].IR.opcode != EOP) && (mSimPipe->sim_pipe_pipeline_reg[ID].IR.opcode != NOP))
    {
        tempSrc1 = mSimPipe->sim_pipe_pipeline_reg[ID].IR.src1;
        tempSrc2 = mSimPipe->sim_pipe_pipeline_reg[ID].IR.src2;
        if ((tempSrc1 < REGISTER_FILE_SIZE) && (tempSrc2 < REGISTER_FILE_SIZE)) {
            if ((mSimPipe->sim_pipe_reg_file[tempSrc1].isDestination == TRUE) ||
                (mSimPipe->sim_pipe_reg_file[tempSrc2].isDestination == TRUE)) {
                /*RAW - issue stall*/
                mStalls_Count++;
                mSimPipe->sim_pipe_pipeline_reg[EXE].IR.opcode = NOP;
                mSimPipe->sim_pipe_pipeline_reg[ID].isAvailable = FALSE;
                mSimPipe->sim_pipe_pipeline_reg[IF].isAvailable = FALSE;
                mSimPipe->sim_pipe_pipeline_reg[EXE].isAvailable = TRUE;
            } else {
                mSimPipe->sim_pipe_pipeline_reg[ID].isAvailable = TRUE;
                if(IS_OPCODE_BRANCH(mSimPipe->sim_pipe_pipeline_reg[ID].IR))
                {
                    mControlDelay++;
                    if(mControlDelay==1)
                    {
                        mStalls_Count++;
                        mSimPipe->sim_pipe_pipeline_reg[IF].isAvailable = FALSE;
                        is_branch_ongoing = TRUE;
                        is_branch_calculated = FALSE;

                    }else if(is_branch_calculated == TRUE)//(mSimPipe->sim_pipe_pipeline_reg[EXE].isAvailable == FALSE)
                    {
                        mControlDelay = 0;
                        //mStalls_Count++;
                        mSimPipe->sim_pipe_pipeline_reg[ID].isAvailable = FALSE;
                        mSimPipe->sim_pipe_pipeline_reg[IF].isAvailable = TRUE;
                        is_branch_ongoing = FALSE;
                        is_branch_calculated = FALSE;
                    }else
                    {
                        mStalls_Count++;
                        mSimPipe->sim_pipe_pipeline_reg[ID].isAvailable = FALSE;
                        mSimPipe->sim_pipe_pipeline_reg[IF].isAvailable = FALSE;
                    }

                }else
                {
                    mSimPipe->sim_pipe_pipeline_reg[IF].isAvailable = TRUE;
                }
            }
        } else {
            //TODO: Error Handling
        }
    }
    if(mSimPipe->sim_pipe_pipeline_reg[ID].isAvailable == TRUE)
    {
        mSimPipe->sim_pipe_pipeline_reg[EXE].IR = mSimPipe->sim_pipe_pipeline_reg[ID].IR;
        mSimPipe->sim_pipe_pipeline_reg[EXE].isAvailable = TRUE;
    }
    if((mSimPipe->sim_pipe_pipeline_reg[ID].isAvailable == TRUE) && (mSimPipe->sim_pipe_pipeline_reg[ID].IR.opcode != NOP) && (mSimPipe->sim_pipe_pipeline_reg[ID].IR.opcode != EOP))
    {
        //mSimPipe->sim_pipe_pipeline_reg[EXE].IR = mSimPipe->sim_pipe_pipeline_reg[ID].IR;
        temp = mSimPipe->sim_pipe_pipeline_reg[ID].IR.src1;
        if(temp < REGISTER_FILE_SIZE)
        {
            mSimPipe->sim_pipe_pipeline_reg[EXE].A = mSimPipe->sim_pipe_reg_file[temp].regVal;
        }else
        {
            //TODO: Error handling
            mSimPipe->sim_pipe_pipeline_reg[EXE].A =UNDEFINED;
        }
        temp = mSimPipe->sim_pipe_pipeline_reg[ID].IR.src2;
        if(temp < REGISTER_FILE_SIZE)
        {
            mSimPipe->sim_pipe_pipeline_reg[EXE].B = mSimPipe->sim_pipe_reg_file[temp].regVal;
        }else
        {
            //TODO: Error handling
            mSimPipe->sim_pipe_pipeline_reg[EXE].B =UNDEFINED;
        }

        if(mSimPipe->sim_pipe_pipeline_reg[ID].IR.opcode == SW)
        {
            SW_Swap = mSimPipe->sim_pipe_pipeline_reg[EXE].A;
            mSimPipe->sim_pipe_pipeline_reg[EXE].A = mSimPipe->sim_pipe_pipeline_reg[EXE].B;
            mSimPipe->sim_pipe_pipeline_reg[EXE].B = SW_Swap;
        }

        mSimPipe->sim_pipe_pipeline_reg[EXE].Imm = mSimPipe->sim_pipe_pipeline_reg[ID].IR.immediate;
        temp = mSimPipe->sim_pipe_pipeline_reg[ID].IR.dest;
        if((temp < REGISTER_FILE_SIZE) && (IS_OPCODE_ALU(mSimPipe->sim_pipe_pipeline_reg[ID].IR) || IS_OPCODE_ALU_IMM(mSimPipe->sim_pipe_pipeline_reg[ID].IR) || (mSimPipe->sim_pipe_pipeline_reg[ID].IR.opcode == LW)) )
        {
            mSimPipe->sim_pipe_pipeline_reg[EXE].Rd = temp;
            mSimPipe->sim_pipe_reg_file[temp].isDestination = TRUE;
        }else
        {
            //TODO: Error handling
        }
        mSimPipe->sim_pipe_pipeline_reg[EXE].NPC = mSimPipe->sim_pipe_pipeline_reg[ID].NPC;
        //mSimPipe->sim_pipe_pipeline_reg[ID].IR.opcode = NOP;
        mSimPipe->sim_pipe_pipeline_reg[ID].isAvailable = FALSE;
        mSimPipe->sim_pipe_pipeline_reg[EXE].isAvailable = TRUE;

        //Undef all unused pipeline registers TODO:Remove these as these aren't modified after reset
       /*
        mSimPipe->sim_pipe_pipeline_reg[EXE].PC = UNDEFINED;
        mSimPipe->sim_pipe_pipeline_reg[EXE].ALU_Output = UNDEFINED;
        mSimPipe->sim_pipe_pipeline_reg[EXE].Cond = UNDEFINED;
        mSimPipe->sim_pipe_pipeline_reg[EXE].LMD = UNDEFINED;
        */
    }
    if(mSimPipe->sim_pipe_pipeline_reg[EXE].IR.opcode == EOP)
    {
        mSimPipe->sim_pipe_pipeline_reg[EXE].A = UNDEFINED;
        mSimPipe->sim_pipe_pipeline_reg[EXE].B = UNDEFINED;
        mSimPipe->sim_pipe_pipeline_reg[EXE].Rd = UNDEFINED;
        mSimPipe->sim_pipe_pipeline_reg[EXE].Imm = UNDEFINED;
    }
}

void pipe_EXE_Handler(sim_pipe* mSimPipe)
{

    if(mSimPipe->sim_pipe_pipeline_reg[EXE].isAvailable == TRUE)
    {
        mSimPipe->sim_pipe_pipeline_reg[MEM].IR = mSimPipe->sim_pipe_pipeline_reg[EXE].IR;
        mSimPipe->sim_pipe_pipeline_reg[MEM].isAvailable = TRUE;
    }
    if((mSimPipe->sim_pipe_pipeline_reg[EXE].isAvailable == TRUE) && (mSimPipe->sim_pipe_pipeline_reg[EXE].IR.opcode != NOP) && (mSimPipe->sim_pipe_pipeline_reg[EXE].IR.opcode != EOP))
    {
        //mSimPipe->sim_pipe_pipeline_reg[MEM].IR = mSimPipe->sim_pipe_pipeline_reg[EXE].IR;
        mSimPipe->sim_pipe_pipeline_reg[MEM].ALU_Output = alu(mSimPipe->sim_pipe_pipeline_reg[EXE].IR.opcode,
                                                              mSimPipe->sim_pipe_pipeline_reg[EXE].A,
                                                              mSimPipe->sim_pipe_pipeline_reg[EXE].B,
                                                              mSimPipe->sim_pipe_pipeline_reg[EXE].Imm,
                                                              mSimPipe->sim_pipe_pipeline_reg[EXE].NPC);
        mSimPipe->sim_pipe_pipeline_reg[MEM].B = mSimPipe->sim_pipe_pipeline_reg[EXE].B;
        /*if (IS_OPCODE_MEM(mSimPipe->sim_pipe_pipeline_reg[EXE].IR))
        {
            mSimPipe->sim_pipe_pipeline_reg[MEM].B = mSimPipe->sim_pipe_pipeline_reg[EXE].B;
        }else
        {
            mSimPipe->sim_pipe_pipeline_reg[MEM].B = UNDEFINED;
        }*/
        if (IS_OPCODE_BRANCH(mSimPipe->sim_pipe_pipeline_reg[EXE].IR))
        {
            mSimPipe->sim_pipe_pipeline_reg[MEM].Cond = alu_compute_cond(mSimPipe->sim_pipe_pipeline_reg[EXE].IR.opcode,mSimPipe->sim_pipe_pipeline_reg[EXE].A);
        }else
        {
            mSimPipe->sim_pipe_pipeline_reg[MEM].Cond = UNDEFINED;
        }
        mSimPipe->sim_pipe_pipeline_reg[MEM].Rd = mSimPipe->sim_pipe_pipeline_reg[EXE].Rd;
        unsigned temp;
        temp = mSimPipe->sim_pipe_pipeline_reg[MEM].Rd;
        if((temp < REGISTER_FILE_SIZE) && (IS_OPCODE_ALU(mSimPipe->sim_pipe_pipeline_reg[MEM].IR) || IS_OPCODE_ALU_IMM(mSimPipe->sim_pipe_pipeline_reg[MEM].IR) || (mSimPipe->sim_pipe_pipeline_reg[MEM].IR.opcode == LW)) )
        {
            mSimPipe->sim_pipe_reg_file[temp].isDestination = TRUE;
        }else
        {
            //TODO: Error handling
        }


        //mSimPipe->sim_pipe_pipeline_reg[EXE].IR.opcode = NOP;
        mSimPipe->sim_pipe_pipeline_reg[EXE].isAvailable = FALSE;
        mSimPipe->sim_pipe_pipeline_reg[MEM].isAvailable = TRUE;

        //Undef all unused pipeline registers TODO:Remove these as these aren't modified after reset
        /*
        mSimPipe->sim_pipe_pipeline_reg[MEM].PC = UNDEFINED;
        mSimPipe->sim_pipe_pipeline_reg[MEM].NPC = UNDEFINED;
        mSimPipe->sim_pipe_pipeline_reg[MEM].Imm = UNDEFINED;
        mSimPipe->sim_pipe_pipeline_reg[MEM].A = UNDEFINED;
        mSimPipe->sim_pipe_pipeline_reg[MEM].LMD = UNDEFINED;
         */
    }
    if(mSimPipe->sim_pipe_pipeline_reg[MEM].IR.opcode == EOP)
    {
        mSimPipe->sim_pipe_pipeline_reg[MEM].B = UNDEFINED;
        mSimPipe->sim_pipe_pipeline_reg[MEM].Rd = UNDEFINED;
        mSimPipe->sim_pipe_pipeline_reg[MEM].ALU_Output = UNDEFINED;
        mSimPipe->sim_pipe_pipeline_reg[MEM].Cond = UNDEFINED;
    }
}

void pipe_MEM_Handler(sim_pipe* mSimPipe)
{
    static unsigned mMemDelay = 0;

    if(IS_OPCODE_BRANCH(mSimPipe->sim_pipe_pipeline_reg[MEM].IR) && (is_branch_ongoing == TRUE))
    {
        is_branch_calculated = TRUE;
    }
    if((IS_OPCODE_MEM(mSimPipe->sim_pipe_pipeline_reg[MEM].IR)) && (is_memory_ongoing == FALSE))
    {
        mMemDelay = mSimPipe->data_memory_latency + 1;
        is_memory_ongoing = TRUE;
        mSimPipe->sim_pipe_pipeline_reg[MEM].isAvailable = FALSE;
        mSimPipe->sim_pipe_pipeline_reg[EXE].isAvailable = FALSE;
        mSimPipe->sim_pipe_pipeline_reg[ID].isAvailable = FALSE;
        mSimPipe->sim_pipe_pipeline_reg[IF].isAvailable = FALSE;
    }
    if(is_memory_ongoing == TRUE)
    {
        if(mMemDelay <= 1)
        {
            is_memory_ongoing = FALSE;
            mSimPipe->sim_pipe_pipeline_reg[MEM].isAvailable = TRUE;
            mSimPipe->sim_pipe_pipeline_reg[EXE].isAvailable = TRUE;
            mSimPipe->sim_pipe_pipeline_reg[ID].isAvailable = TRUE;
            mSimPipe->sim_pipe_pipeline_reg[IF].isAvailable = TRUE;
        }else
        {
            mStalls_Count++;
            mMemDelay--;
        }
    }
    if(mSimPipe->sim_pipe_pipeline_reg[MEM].isAvailable == TRUE)
    {
        mSimPipe->sim_pipe_pipeline_reg[WB].IR = mSimPipe->sim_pipe_pipeline_reg[MEM].IR;
        mSimPipe->sim_pipe_pipeline_reg[WB].isAvailable = TRUE;
    }
    if((mSimPipe->sim_pipe_pipeline_reg[MEM].isAvailable == TRUE) && (mSimPipe->sim_pipe_pipeline_reg[MEM].IR.opcode != NOP) && (mSimPipe->sim_pipe_pipeline_reg[MEM].IR.opcode != EOP))
    {
        //mSimPipe->sim_pipe_pipeline_reg[WB].IR = mSimPipe->sim_pipe_pipeline_reg[MEM].IR;
        mSimPipe->sim_pipe_pipeline_reg[WB].Rd = mSimPipe->sim_pipe_pipeline_reg[MEM].Rd;

        unsigned temp;
        temp = mSimPipe->sim_pipe_pipeline_reg[WB].Rd;
        if((temp < REGISTER_FILE_SIZE) && (IS_OPCODE_ALU(mSimPipe->sim_pipe_pipeline_reg[WB].IR) || IS_OPCODE_ALU_IMM(mSimPipe->sim_pipe_pipeline_reg[WB].IR) || (mSimPipe->sim_pipe_pipeline_reg[WB].IR.opcode == LW)) )
        {
            mSimPipe->sim_pipe_reg_file[temp].isDestination = TRUE;
        }else
        {
            //TODO: Error handling
        }

        if ((IS_OPCODE_ALU(mSimPipe->sim_pipe_pipeline_reg[MEM].IR)) ||
            (IS_OPCODE_ALU_IMM(mSimPipe->sim_pipe_pipeline_reg[MEM].IR)))
        {
            mSimPipe->sim_pipe_pipeline_reg[WB].ALU_Output = mSimPipe->sim_pipe_pipeline_reg[MEM].ALU_Output;
        }else
        {
            mSimPipe->sim_pipe_pipeline_reg[WB].ALU_Output = UNDEFINED;
        }
        if (mSimPipe->sim_pipe_pipeline_reg[MEM].IR.opcode == LW)
        {
            //TODO: MEM/WB.LMD <-- Mem[EX/MEM.ALUOutput]; or Mem[EX/MEM.ALUOutput] <-- EX/MEM.B;
            unsigned temp;
            //TODO: check this address check
            temp = mSimPipe->sim_pipe_pipeline_reg[MEM].ALU_Output;
            if(temp < mSimPipe->data_memory_size)
            {
                mSimPipe->sim_pipe_pipeline_reg[WB].LMD = char2int(&mSimPipe->data_memory[temp]);
            }
        }else
        {
            mSimPipe->sim_pipe_pipeline_reg[WB].LMD = UNDEFINED;
        }
        if (mSimPipe->sim_pipe_pipeline_reg[MEM].IR.opcode == SW)
        {
            //TODO: Check if write address is valid
            mSimPipe->write_memory(mSimPipe->sim_pipe_pipeline_reg[MEM].ALU_Output,
                                   mSimPipe->sim_pipe_pipeline_reg[MEM].B);
        } else
        {
            //TODO: Do Nothing, opcode doesn't require MEM stage handling
        }
        //mSimPipe->sim_pipe_pipeline_reg[MEM].IR.opcode = NOP;
        mSimPipe->sim_pipe_pipeline_reg[MEM].isAvailable = FALSE;
        mSimPipe->sim_pipe_pipeline_reg[WB].isAvailable = TRUE;

        //Undef all unused pipeline registers TODO:Remove these as these aren't modified after reset
        /*
        mSimPipe->sim_pipe_pipeline_reg[WB].PC = UNDEFINED;
        mSimPipe->sim_pipe_pipeline_reg[WB].NPC = UNDEFINED;
        mSimPipe->sim_pipe_pipeline_reg[WB].Imm = UNDEFINED;
        mSimPipe->sim_pipe_pipeline_reg[WB].A = UNDEFINED;
        mSimPipe->sim_pipe_pipeline_reg[WB].B = UNDEFINED;
        mSimPipe->sim_pipe_pipeline_reg[WB].Cond = UNDEFINED;
        */
    }
    if(mSimPipe->sim_pipe_pipeline_reg[WB].IR.opcode == EOP)
    {

        mSimPipe->sim_pipe_pipeline_reg[WB].LMD = UNDEFINED;
        mSimPipe->sim_pipe_pipeline_reg[WB].ALU_Output = UNDEFINED;
    }
}

void pipe_WB_Handler(sim_pipe* mSimPipe)
{
    unsigned tempRd;
    if(mSimPipe->sim_pipe_pipeline_reg[WB].isAvailable == TRUE)
    {
        tempRd = mSimPipe->sim_pipe_pipeline_reg[WB].Rd;
    }
    if((mSimPipe->sim_pipe_pipeline_reg[WB].isAvailable == TRUE) && (mSimPipe->sim_pipe_pipeline_reg[WB].IR.opcode != NOP) && (mSimPipe->sim_pipe_pipeline_reg[WB].IR.opcode != EOP))
    {
        mInstruction_Count++;
        if (tempRd < REGISTER_FILE_SIZE)
        {
            if ((IS_OPCODE_ALU(mSimPipe->sim_pipe_pipeline_reg[WB].IR)) ||
                (IS_OPCODE_ALU_IMM(mSimPipe->sim_pipe_pipeline_reg[WB].IR)))
            {
                mSimPipe->sim_pipe_reg_file[tempRd].regVal = mSimPipe->sim_pipe_pipeline_reg[WB].ALU_Output;
                mSimPipe->sim_pipe_reg_file[tempRd].isDestination = FALSE;
            } else if (mSimPipe->sim_pipe_pipeline_reg[WB].IR.opcode == LW)
            {
                mSimPipe->sim_pipe_reg_file[tempRd].regVal = mSimPipe->sim_pipe_pipeline_reg[WB].LMD;
                mSimPipe->sim_pipe_reg_file[tempRd].isDestination = FALSE;
            } else
            {
                //Nothing to be done in WB
            }
        } else {
            //TODO: error handling;
        }
        //mSimPipe->sim_pipe_pipeline_reg[WB].IR.opcode = NOP;
        mSimPipe->sim_pipe_pipeline_reg[WB].isAvailable = FALSE;
    }

}

unsigned alu_compute_cond(opcode_t mOpCode, int mSrc)
{
    unsigned mRetVal=0;
    switch (mOpCode)
    {
        case BEQZ:
        {
            mRetVal = (unsigned)(mSrc == 0);
            break;
        }
        case BNEZ:
        {
            mRetVal = (unsigned)(mSrc != 0);
            break;
        }
        case BLTZ:
        {
            mRetVal = (unsigned)(mSrc < 0);
            break;
        }
        case BGTZ:
        {
            mRetVal = (unsigned)(mSrc > 0);
            break;
        }
        case BLEZ:
        {
            mRetVal = (unsigned)(mSrc <= 0);
            break;
        }
        case BGEZ:
        {
            mRetVal = (unsigned)(mSrc >= 0);
            break;
        }
        case JUMP:
        {
            mRetVal = 1;
            break;
        }
        default:
            //TODO: Erro Handling
            break;
    }
    return mRetVal;
}