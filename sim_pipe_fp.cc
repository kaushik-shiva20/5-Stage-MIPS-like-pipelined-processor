#include "sim_pipe_fp.h"
#include <stdlib.h>
#include <iostream>
#include <fstream>
#include <cstring>
#include <string>
#include <iomanip>
#include <map>

//NOTE: structural hazards on MEM/WB stage not handled
//====================================================

//#define DEBUG
//#define DEBUG_MEMORY


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
static const char *instr_names[NUM_OPCODES] = {"LW", "SW", "ADD", "ADDI", "SUB", "SUBI", "XOR", "BEQZ", "BNEZ", "BLTZ", "BGTZ", "BLEZ", "BGEZ", "JUMP", "EOP", "NOP", "LWS", "SWS", "ADDS", "SUBS", "MULTS", "DIVS"};
static const char *unit_names[4]={"INTEGER", "ADDER", "MULTIPLIER", "DIVIDER"};

/* =============================================================

   HELPER FUNCTIONS

   ============================================================= */

void pipe_IF_Handler(sim_pipe_fp* mSimPipe);
void pipe_ID_Handler(sim_pipe_fp* mSimPipe);
void pipe_EXE_Handler(sim_pipe_fp* mSimPipe);
void pipe_MEM_Handler(sim_pipe_fp* mSimPipe);
void pipe_WB_Handler(sim_pipe_fp* mSimPipe);
unsigned alu_compute_cond(opcode_t mOpCode, int mSrc);
unsigned isOpCodeFpType(opcode_t mOpCode);

/* convert a float into an unsigned */
inline unsigned float2unsigned(float value){
	unsigned result;
	memcpy(&result, &value, sizeof value);
	return result;
}

/* convert an unsigned into a float */
inline float unsigned2float(unsigned value){
	float result;
	memcpy(&result, &value, sizeof value);
	return result;
}

/* convert integer into array of unsigned char - little indian */
inline void unsigned2char(unsigned value, unsigned char *buffer){
        buffer[0] = value & 0xFF;
        buffer[1] = (value >> 8) & 0xFF;
        buffer[2] = (value >> 16) & 0xFF;
        buffer[3] = (value >> 24) & 0xFF;
}

/* convert array of char into integer - little indian */
inline unsigned char2unsigned(unsigned char *buffer){
       return buffer[0] + (buffer[1] << 8) + (buffer[2] << 16) + (buffer[3] << 24);
}

/* the following functions return the kind of the considered opcode */

bool is_branch(opcode_t opcode){
	return (opcode == BEQZ || opcode == BNEZ || opcode == BLTZ || opcode == BLEZ || opcode == BGTZ || opcode == BGEZ || opcode == JUMP);
}

bool is_memory(opcode_t opcode){
        return (opcode == LW || opcode == SW || opcode == LWS || opcode == SWS);
}

bool is_int_r(opcode_t opcode){
        return (opcode == ADD || opcode == SUB || opcode == XOR);
}

bool is_int_imm(opcode_t opcode){
        return (opcode == ADDI || opcode == SUBI);
}

bool is_int_alu(opcode_t opcode){
        return (is_int_r(opcode) || is_int_imm(opcode));
}

bool is_fp_alu(opcode_t opcode){
        return (opcode == ADDS || opcode == SUBS || opcode == MULTS || opcode == DIVS);
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
			case LWS:
			case SWS:
				return(a + imm);
			case BEQZ:
			case BNEZ:
			case BGTZ:
			case BGEZ:
			case BLTZ:
			case BLEZ:
			case JUMP:
				return(npc+imm);
			case ADDS:
				return(float2unsigned(unsigned2float(a)+unsigned2float(b)));
				break;
			case SUBS:
				return(float2unsigned(unsigned2float(a)-unsigned2float(b)));
				break;
			case MULTS:
				return(float2unsigned(unsigned2float(a)*unsigned2float(b)));
				break;
			case DIVS:
				return(float2unsigned(unsigned2float(a)/unsigned2float(b)));
				break;
			default:
				return (-1);
	}
}

/* =============================================================

   CODE PROVIDED - NO NEED TO MODIFY FUNCTIONS BELOW

   ============================================================= */

/* ============== primitives to allocate/free the simulator ================== */

sim_pipe_fp::sim_pipe_fp(unsigned mem_size, unsigned mem_latency){
	data_memory_size = mem_size;
	data_memory_latency = mem_latency;
	data_memory = new unsigned char[data_memory_size];
	num_units = 0;
	reset();
}

sim_pipe_fp::~sim_pipe_fp(){
	delete [] data_memory;
}

/* =============   primitives to print out the content of the memory & registers and for writing to memory ============== */

void sim_pipe_fp::print_memory(unsigned start_address, unsigned end_address){
	cout << "data_memory[0x" << hex << setw(8) << setfill('0') << start_address << ":0x" << hex << setw(8) << setfill('0') <<  end_address << "]" << endl;
	for (unsigned i=start_address; i<end_address; i++){
		if (i%4 == 0) cout << "0x" << hex << setw(8) << setfill('0') << i << ": ";
		cout << hex << setw(2) << setfill('0') << int(data_memory[i]) << " ";
		if (i%4 == 3){
#ifdef DEBUG_MEMORY
			unsigned u = char2unsigned(&data_memory[i-3]);
			cout << " - unsigned=" << u << " - float=" << unsigned2float(u);
#endif
			cout << endl;
		}
	}
}

void sim_pipe_fp::write_memory(unsigned address, unsigned value){
	unsigned2char(value,data_memory+address);
}


void sim_pipe_fp::print_registers(){
        cout << "Special purpose registers:" << endl;
        unsigned i, s;
        for (s=0; s<NUM_STAGES; s++){
                cout << "Stage: " << stage_names[s] << endl;
                for (i=0; i< NUM_SP_REGISTERS; i++)
                        if ((sp_register_t)i != IR && (sp_register_t)i != COND && get_sp_register((sp_register_t)i, (stage_t)s)!=UNDEFINED) cout << reg_names[i] << " = " << dec <<  get_sp_register((sp_register_t)i, (stage_t)s) << hex << " / 0x" << get_sp_register((sp_register_t)i, (stage_t)s) << endl;
        }
        cout << "General purpose registers:" << endl;
        for (i=0; i< NUM_GP_REGISTERS; i++)
                if (get_int_register(i)!=(int)UNDEFINED) cout << "R" << dec << i << " = " << get_int_register(i) << hex << " / 0x" << get_int_register(i) << endl;
        for (i=0; i< NUM_GP_REGISTERS; i++)
                if (float2unsigned(get_fp_register(i))!=UNDEFINED) cout << "F" << dec << i << " = " << get_fp_register(i) << hex << " / 0x" << float2unsigned(get_fp_register(i)) << endl;
}


/* =============   primitives related to the functional units ============== */

/* initializes an execution unit */
void sim_pipe_fp::init_exec_unit(exe_unit_t exec_unit, unsigned latency, unsigned instances){
	for (unsigned i=0; i<instances; i++){
		exec_units[num_units].type = exec_unit;
		exec_units[num_units].latency = latency+1;
		exec_units[num_units].busy = 0;
		exec_units[num_units].instruction.opcode = NOP;

        sim_pipe_pipeline_reg_EXE[num_units].PC = UNDEFINED;
        sim_pipe_pipeline_reg_EXE[num_units].NPC = UNDEFINED;
        sim_pipe_pipeline_reg_EXE[num_units].IR.opcode = NOP;
        sim_pipe_pipeline_reg_EXE[num_units].Rd = UNDEFINED;
        sim_pipe_pipeline_reg_EXE[num_units].Imm = UNDEFINED;
        sim_pipe_pipeline_reg_EXE[num_units].A = UNDEFINED;
        sim_pipe_pipeline_reg_EXE[num_units].B = UNDEFINED;
        sim_pipe_pipeline_reg_EXE[num_units].ALU_Output = UNDEFINED;
        sim_pipe_pipeline_reg_EXE[num_units].Cond = UNDEFINED;
        sim_pipe_pipeline_reg_EXE[num_units].LMD = UNDEFINED;
        sim_pipe_pipeline_reg_EXE[num_units].isAvailable = FALSE;

		num_units++;
	}
}

/* returns a free unit for that particular operation or UNDEFINED if no unit is currently available */
unsigned sim_pipe_fp::get_free_unit(opcode_t opcode){
	if (num_units == 0){
		cout << "ERROR:: simulator does not have any execution units!\n";
		exit(-1);
	}
	for (unsigned u=0; u<num_units; u++){
		switch(opcode){
			//Integer unit
			case LW:
			case SW:
			case ADD:
			case ADDI:
			case SUB:
			case SUBI:
			case XOR:
			case BEQZ:
			case BNEZ:
			case BLTZ:
			case BGTZ:
			case BLEZ:
			case BGEZ:
			case JUMP:
			case LWS:
			case SWS:
				if (exec_units[u].type==INTEGER && exec_units[u].busy==0) return u;
				break;
			// FP adder
			case ADDS:
			case SUBS:
				if (exec_units[u].type==ADDER && exec_units[u].busy==0) return u;
				break;
			// Multiplier
			case MULTS:
				if (exec_units[u].type==MULTIPLIER && exec_units[u].busy==0) return u;
				break;
			// Divider
			case DIVS:
				if (exec_units[u].type==DIVIDER && exec_units[u].busy==0) return u;
				break;
			default:
				cout << "ERROR:: operations not requiring exec unit!\n";
				exit(-1);
		}
	}
	return UNDEFINED;
}

/* decrease the amount of clock cycles during which the functional unit will be busy - to be called at each clock cycle  */
void sim_pipe_fp::decrement_units_busy_time(){
	for (unsigned u=0; u<num_units; u++){
		if (exec_units[u].busy > 0) exec_units[u].busy --;
	}
}


/* prints out the status of the functional units */
void sim_pipe_fp::debug_units(){
	for (unsigned u=0; u<num_units; u++){
		cout << " -- unit " << unit_names[exec_units[u].type] << " latency=" << exec_units[u].latency << " busy=" << exec_units[u].busy <<
			" instruction=" << instr_names[exec_units[u].instruction.opcode] << endl;
	}
}

/* ========= end primitives related to functional units ===============*/


/* ========================parser ==================================== */

void sim_pipe_fp::load_program(const char *filename, unsigned base_address){

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
		case ADDS:
		case SUBS:
		case MULTS:
		case DIVS:
			par1 = strtok (NULL, " \t");
			par2 = strtok (NULL, " \t");
			par3 = strtok (NULL, " \t");
			instr_memory[instruction_nr].dest = atoi(strtok(par1, "RF"));
			instr_memory[instruction_nr].src1 = atoi(strtok(par2, "RF"));
			instr_memory[instruction_nr].src2 = atoi(strtok(par3, "RF"));
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
		case LWS:
			par1 = strtok (NULL, " \t");
			par2 = strtok (NULL, " \t");
			instr_memory[instruction_nr].dest = atoi(strtok(par1, "RF"));
			instr_memory[instruction_nr].immediate = strtoul(strtok(par2, "()"), NULL, 0);
			instr_memory[instruction_nr].src1 = atoi(strtok(NULL, "R"));
			break;
		case SW:
		case SWS:
			par1 = strtok (NULL, " \t");
			par2 = strtok (NULL, " \t");
			instr_memory[instruction_nr].src1 = atoi(strtok(par1, "RF"));
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

/* =============================================================

   CODE TO BE COMPLETED

   ============================================================= */

/* simulator */
void sim_pipe_fp::run(unsigned cycles)
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
}

//reset the state of the sim_pipe_fpulator
void sim_pipe_fp::reset(){
	// init data memory
	for (unsigned i=0; i<data_memory_size; i++) data_memory[i]=0xFF;
	// init instruction memory
	for (int i=0; i<PROGRAM_SIZE;i++){
		instr_memory[i].opcode=(opcode_t)NOP;
		instr_memory[i].src1=UNDEFINED;
		instr_memory[i].src2=UNDEFINED;
		instr_memory[i].dest=UNDEFINED;
		instr_memory[i].immediate=UNDEFINED;
	}

	/* complete the reset function here */

    /** Added Code Start **/
    /** Reset register file **/
    //sim_pipe_reg_file[0].regVal = 0;
    //sim_pipe_reg_file[0].isDestination = FALSE;
    for(int i=0;i<REGISTER_FILE_SIZE;i++)
    {
        sim_pipe_reg_file[i].regVal = UNDEFINED;
        sim_pipe_reg_file[i].isDestination = FALSE;
        sim_pipe_reg_file_fp[i].regVal = UNDEFINED;
        sim_pipe_reg_file_fp[i].isDestination = FALSE;
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
unsigned sim_pipe_fp::get_sp_register(sp_register_t reg, stage_t s){
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
    return mRetVal; //please modify // please modify
}

int sim_pipe_fp::get_int_register(unsigned reg){
	return sim_pipe_reg_file[reg].regVal; // please modify
}

void sim_pipe_fp::set_int_register(unsigned reg, int value)
{
    sim_pipe_reg_file[reg].regVal = value;
}

float sim_pipe_fp::get_fp_register(unsigned reg){
	return unsigned2float(sim_pipe_reg_file_fp[reg].regVal); // please modify
}

void sim_pipe_fp::set_fp_register(unsigned reg, float value)
{
    sim_pipe_reg_file_fp[reg].regVal = float2unsigned(value);
}


float sim_pipe_fp::get_IPC(){
	return ((float)mInstruction_Count/(float)mClock_Cycles); // please modify
}

unsigned sim_pipe_fp::get_instructions_executed(){
	return mInstruction_Count; // please modify
}

unsigned sim_pipe_fp::get_clock_cycles(){
	return mClock_Cycles; // please modify
}

unsigned sim_pipe_fp::get_stalls(){
	return mStalls_Count;//(mClock_Cycles-mInstruction_Count-4); // please modify
}
void pipe_IF_Handler(sim_pipe_fp* mSimPipe)
{
    //TODO: Recheck this implementation
    if((mSimPipe->sim_pipe_pipeline_reg[IF].isAvailable == TRUE) )
    {
        /*
        if ((is_branch(mSimPipe->sim_pipe_pipeline_reg[ID].IR.opcode)) &&
            (mSimPipe->sim_pipe_pipeline_reg[MEM].Cond == 1)&& (is_branch_calculated==TRUE))
        {
            mSimPipe->sim_pipe_pipeline_reg[MEM].Cond = 0;
            mSimPipe->sim_pipe_pipeline_reg[IF].PC = mSimPipe->sim_pipe_pipeline_reg[MEM].ALU_Output;
        }*/
        mSimPipe->sim_pipe_pipeline_reg[ID].IR = mSimPipe->instr_memory[(mSimPipe->sim_pipe_pipeline_reg[IF].PC - mSimPipe->instr_base_address) / 4];
        mSimPipe->sim_pipe_pipeline_reg[ID].isAvailable = TRUE;

        if ((mSimPipe->sim_pipe_pipeline_reg[ID].IR.opcode != EOP))
        {
            mSimPipe->sim_pipe_pipeline_reg[IF].PC += 4;
            mSimPipe->sim_pipe_pipeline_reg[ID].NPC = mSimPipe->sim_pipe_pipeline_reg[IF].PC;
        }

    }

}
void pipe_ID_Handler(sim_pipe_fp* mSimPipe)
{
    unsigned temp;
    unsigned SW_Swap;
    unsigned tempSrc1;
    unsigned tempSrc2;
    unsigned tempDest;
    unsigned tempUnit = UNDEFINED;
    opcode_t  tempOpCode;
    static unsigned mControlDelay=0;

    tempOpCode = mSimPipe->sim_pipe_pipeline_reg[ID].IR.opcode;

    if((tempOpCode != NOP) && (tempOpCode != EOP))
    {
        tempUnit = mSimPipe->get_free_unit(tempOpCode);
    }else
    {
        if(tempOpCode == EOP)
        {
            unsigned isEXEEmpty = TRUE;
            for(int i=0;i<mSimPipe->num_units;i++)
            {
                if(mSimPipe->exec_units[i].busy != 0)
                {
                    isEXEEmpty = FALSE;
                }
            }
            if(isEXEEmpty == TRUE)
            {
                mSimPipe->sim_pipe_pipeline_reg[EXE].IR.opcode = EOP;
            }
        }
        //mSimPipe->sim_pipe_pipeline_reg[EXE].IR.opcode = tempOpCode;
        mSimPipe->sim_pipe_pipeline_reg[ID].isAvailable = FALSE;
        //mSimPipe->sim_pipe_pipeline_reg[IF].isAvailable = FALSE;
    }
    if(tempUnit != UNDEFINED)
    {
        tempSrc1 = mSimPipe->sim_pipe_pipeline_reg[ID].IR.src1;
        tempSrc2 = mSimPipe->sim_pipe_pipeline_reg[ID].IR.src2;
        tempDest = mSimPipe->sim_pipe_pipeline_reg[ID].IR.dest;
        if ((tempOpCode == JUMP) || (tempSrc1 < REGISTER_FILE_SIZE) || (tempSrc2 < REGISTER_FILE_SIZE))
        {
            /*Check any RAW hazards if not NOP and EOP instruction*/
            unsigned isRAWPresent = FALSE;
            unsigned isWAWPresent = FALSE;
            if(tempSrc1 < REGISTER_FILE_SIZE)
            {
                if(is_memory(tempOpCode))
                {
                    if (mSimPipe->sim_pipe_reg_file[tempSrc1].isDestination == TRUE)
                    {
                        isRAWPresent = TRUE;
                    }
                }
                else if(isOpCodeFpType(tempOpCode) == TRUE)
                {
                    if (mSimPipe->sim_pipe_reg_file_fp[tempSrc1].isDestination == TRUE)
                    {
                        isRAWPresent = TRUE;
                    }

                } else
                {
                    if (mSimPipe->sim_pipe_reg_file[tempSrc1].isDestination == TRUE)
                    {
                        isRAWPresent = TRUE;
                    }
                }
            }
            if(tempSrc2 < REGISTER_FILE_SIZE)
            {
                if (isOpCodeFpType(tempOpCode) == TRUE)
                {
                    if (mSimPipe->sim_pipe_reg_file_fp[tempSrc2].isDestination == TRUE)
                    {
                        isRAWPresent = TRUE;
                    }
                } else
                {
                    if (mSimPipe->sim_pipe_reg_file[tempSrc2].isDestination == TRUE)
                    {
                        isRAWPresent = TRUE;
                    }
                }
            }

            if(tempDest < REGISTER_FILE_SIZE)
            {
                unsigned tempExeDest;
                for(int i=0;i<mSimPipe->num_units;i++)
                {
                    tempExeDest = mSimPipe->sim_pipe_pipeline_reg_EXE[i].Rd;
                    if(mSimPipe->sim_pipe_pipeline_reg_EXE[i].IR.opcode!= NOP && tempExeDest < REGISTER_FILE_SIZE) {
                        if (tempExeDest == tempDest) {
                            if (mSimPipe->exec_units[i].busy >= mSimPipe->exec_units[tempUnit].latency) {
                                isWAWPresent = TRUE;
                            }
                        }
                    }
                }
            }
            if (isRAWPresent == TRUE)
            {
                /*RAW - issue stall*/
                mStalls_Count++;
                // mSimPipe->sim_pipe_pipeline_reg[EXE].IR.opcode = NOP;
                mSimPipe->sim_pipe_pipeline_reg[ID].isAvailable = FALSE;
                mSimPipe->sim_pipe_pipeline_reg[IF].isAvailable = FALSE;
                //  mSimPipe->sim_pipe_pipeline_reg[EXE].isAvailable = TRUE;
            }else if (isWAWPresent == TRUE)
            {
                /*RAW - issue stall*/
                mStalls_Count++;
                // mSimPipe->sim_pipe_pipeline_reg[EXE].IR.opcode = NOP;
                mSimPipe->sim_pipe_pipeline_reg[ID].isAvailable = FALSE;
                mSimPipe->sim_pipe_pipeline_reg[IF].isAvailable = FALSE;
                //  mSimPipe->sim_pipe_pipeline_reg[EXE].isAvailable = TRUE;
            } else
            {
                mSimPipe->sim_pipe_pipeline_reg[ID].isAvailable = TRUE;
                if (is_branch(mSimPipe->sim_pipe_pipeline_reg[ID].IR.opcode))
                {
                    //TODO: remove the redundant check
                    //Check if all EXE units are done with processing before scheduling branch instr
                    unsigned areAllExeUnitsProcessed = TRUE;
                    if(mControlDelay == 0)
                    {
                        for (int i = 0; i < mSimPipe->num_units; i++)
                        {
                            if (mSimPipe->exec_units[i].busy != 0)
                            {
                               // areAllExeUnitsProcessed = FALSE;
                            }
                        }
                    }
                    if(areAllExeUnitsProcessed == TRUE)
                    {
                        mControlDelay++;
                        if (mControlDelay == 1)
                        {
                            mStalls_Count++;
                            mSimPipe->sim_pipe_pipeline_reg[IF].isAvailable = FALSE;
                            is_branch_ongoing = TRUE;
                            is_branch_calculated = FALSE;

                        } else if (is_branch_calculated == TRUE)
                        {
                            mControlDelay = 0;
                            //mStalls_Count++;
                            mSimPipe->sim_pipe_pipeline_reg[ID].isAvailable = FALSE;
                            mSimPipe->sim_pipe_pipeline_reg[IF].isAvailable = TRUE;
                            is_branch_ongoing = FALSE;
                            is_branch_calculated = FALSE;
                        } else
                        {
                            mStalls_Count++;
                            mSimPipe->sim_pipe_pipeline_reg[ID].isAvailable = FALSE;
                            mSimPipe->sim_pipe_pipeline_reg[IF].isAvailable = FALSE;
                        }
                    } else
                    {
                        //Branch instr is stalled because other exe units have to complete execution before branch
                        mStalls_Count++;
                        mSimPipe->sim_pipe_pipeline_reg[ID].isAvailable = FALSE;
                        mSimPipe->sim_pipe_pipeline_reg[IF].isAvailable = FALSE;
                    }

                } else
                {
                    mSimPipe->sim_pipe_pipeline_reg[IF].isAvailable = TRUE;
                }
            }
        } else
        {
            //TODO: Error Handling
        }

    }else if((tempOpCode != NOP) && (tempOpCode != EOP))
    {
        mStalls_Count++;
        //Required Exe unit is not available do nothing in ID and don't fetch next instr
        mSimPipe->sim_pipe_pipeline_reg[ID].isAvailable = FALSE;
        mSimPipe->sim_pipe_pipeline_reg[IF].isAvailable = FALSE;
    }
    //Tests to check if ID stage to be executed or not done. Now execute the ID stage
    /*if(mSimPipe->sim_pipe_pipeline_reg[ID].isAvailable == TRUE)
    {
        mSimPipe->sim_pipe_pipeline_reg_EXE[tempUnit].IR = mSimPipe->sim_pipe_pipeline_reg[ID].IR;
        mSimPipe->exec_units[tempUnit].instruction = mSimPipe->sim_pipe_pipeline_reg[ID].IR;
        if((tempOpCode != NOP) && (tempOpCode != EOP))
        {
            mSimPipe->exec_units[tempUnit].busy = mSimPipe->exec_units[tempUnit].latency;
        }
    }*/
    if(mSimPipe->sim_pipe_pipeline_reg[ID].isAvailable == TRUE)
    {
        if((tempOpCode == SW) || (tempOpCode == SWS))
        {
            SW_Swap = mSimPipe->sim_pipe_pipeline_reg[ID].IR.src1;
            mSimPipe->sim_pipe_pipeline_reg[ID].IR.src1 = mSimPipe->sim_pipe_pipeline_reg[ID].IR.src2;
            mSimPipe->sim_pipe_pipeline_reg[ID].IR.src2 = SW_Swap;
        }
        mSimPipe->sim_pipe_pipeline_reg_EXE[tempUnit].IR = mSimPipe->sim_pipe_pipeline_reg[ID].IR;
        mSimPipe->exec_units[tempUnit].instruction = mSimPipe->sim_pipe_pipeline_reg[ID].IR;
        mSimPipe->exec_units[tempUnit].busy = mSimPipe->exec_units[tempUnit].latency;
        //mSimPipe->sim_pipe_pipeline_reg[EXE].IR = mSimPipe->sim_pipe_pipeline_reg[ID].IR;
        temp = mSimPipe->sim_pipe_pipeline_reg[ID].IR.src1;
        if(temp < REGISTER_FILE_SIZE)
        {
            if(is_memory(tempOpCode))
            {
                mSimPipe->sim_pipe_pipeline_reg_EXE[tempUnit].A = mSimPipe->sim_pipe_reg_file[temp].regVal;
            }else if(isOpCodeFpType(tempOpCode) == TRUE)
            {
                mSimPipe->sim_pipe_pipeline_reg_EXE[tempUnit].A = mSimPipe->sim_pipe_reg_file_fp[temp].regVal;
            }else
            {
                mSimPipe->sim_pipe_pipeline_reg_EXE[tempUnit].A = mSimPipe->sim_pipe_reg_file[temp].regVal;
            }
        }else
        {
            //TODO: Error handling
            mSimPipe->sim_pipe_pipeline_reg_EXE[tempUnit].A =UNDEFINED;
        }
        temp = mSimPipe->sim_pipe_pipeline_reg[ID].IR.src2;
        if(temp < REGISTER_FILE_SIZE)
        {
            if(isOpCodeFpType(tempOpCode) == TRUE)
            {
                mSimPipe->sim_pipe_pipeline_reg_EXE[tempUnit].B = mSimPipe->sim_pipe_reg_file_fp[temp].regVal;
            }else
            {
                mSimPipe->sim_pipe_pipeline_reg_EXE[tempUnit].B = mSimPipe->sim_pipe_reg_file[temp].regVal;
            }
        }else
        {
            //TODO: Error handling
            mSimPipe->sim_pipe_pipeline_reg_EXE[tempUnit].B =UNDEFINED;
        }

        if(is_int_imm(tempOpCode) || is_branch(tempOpCode) || is_memory(tempOpCode))
        {
            mSimPipe->sim_pipe_pipeline_reg_EXE[tempUnit].Imm = mSimPipe->sim_pipe_pipeline_reg_EXE[tempUnit].IR.immediate;
        }else
        {
            mSimPipe->sim_pipe_pipeline_reg_EXE[tempUnit].Imm = UNDEFINED;
        }
        temp = mSimPipe->sim_pipe_pipeline_reg[ID].IR.dest;
        if(temp < REGISTER_FILE_SIZE)
        {
            //once inside this IF => has a destination
            mSimPipe->sim_pipe_pipeline_reg_EXE[tempUnit].Rd = temp;
            if(isOpCodeFpType(tempOpCode))
            {
                mSimPipe->sim_pipe_reg_file_fp[temp].isDestination = TRUE;
            }else
            {
                mSimPipe->sim_pipe_reg_file[temp].isDestination = TRUE;
            }
        }else
        {
            //TODO: Error handling
            mSimPipe->sim_pipe_pipeline_reg_EXE[tempUnit].Rd = UNDEFINED;
        }

        mSimPipe->sim_pipe_pipeline_reg_EXE[tempUnit].NPC = mSimPipe->sim_pipe_pipeline_reg[ID].NPC;
        //mSimPipe->sim_pipe_pipeline_reg[ID].IR.opcode = NOP;
        mSimPipe->sim_pipe_pipeline_reg_EXE[tempUnit].isAvailable = TRUE;

    }
}

void pipe_EXE_Handler(sim_pipe_fp* mSimPipe)
{
    if(mSimPipe->sim_pipe_pipeline_reg[EXE].IR.opcode != EOP)
    {
        for (int i = mSimPipe->num_units-1; i >=0; i--) {
            if (mSimPipe->exec_units[i].busy != 0) {
                mSimPipe->exec_units[i].busy--;
            }
            if ((mSimPipe->exec_units[i].busy == 0) && (mSimPipe->sim_pipe_pipeline_reg_EXE[i].isAvailable == TRUE) &&
                (mSimPipe->exec_units[i].instruction.opcode != NOP) &&
                (mSimPipe->exec_units[i].instruction.opcode != EOP)) {
                //Process Unit
                unsigned temp;
                opcode_t tempOpCode;
                temp = mSimPipe->sim_pipe_pipeline_reg_EXE[i].Rd;
                tempOpCode = mSimPipe->sim_pipe_pipeline_reg_EXE[i].IR.opcode;
                if (temp < REGISTER_FILE_SIZE) {
                    if ((is_int_alu(tempOpCode)) || (tempOpCode == LW)) {
                        mSimPipe->sim_pipe_reg_file[temp].isDestination = TRUE;
                    } else if ((is_fp_alu(tempOpCode)) || (tempOpCode == LWS)) {
                        mSimPipe->sim_pipe_reg_file_fp[temp].isDestination = TRUE;
                    }
                } else {
                    //TODO: Error handling
                }
                if ((is_memory_ongoing == FALSE) && (mSimPipe->sim_pipe_pipeline_reg[MEM].isAvailable == FALSE))
                {
                    //If mem stage is free transfer the instr from exe to mem and mark mem as busy
                    mSimPipe->sim_pipe_pipeline_reg[MEM].IR = mSimPipe->sim_pipe_pipeline_reg_EXE[i].IR;
                    mSimPipe->sim_pipe_pipeline_reg[MEM].ALU_Output = alu(mSimPipe->sim_pipe_pipeline_reg_EXE[i].IR.opcode,
                                                                              mSimPipe->sim_pipe_pipeline_reg_EXE[i].A,
                                                                              mSimPipe->sim_pipe_pipeline_reg_EXE[i].B,
                                                                               mSimPipe->sim_pipe_pipeline_reg_EXE[i].Imm,
                                                                              mSimPipe->sim_pipe_pipeline_reg_EXE[i].NPC);
                    if (is_branch(mSimPipe->sim_pipe_pipeline_reg_EXE[i].IR.opcode)) {
                        mSimPipe->sim_pipe_pipeline_reg[MEM].Cond = alu_compute_cond(
                                mSimPipe->sim_pipe_pipeline_reg_EXE[i].IR.opcode,
                                mSimPipe->sim_pipe_pipeline_reg_EXE[i].A);
                    } else {
                        mSimPipe->sim_pipe_pipeline_reg[MEM].Cond = UNDEFINED;
                    }
                    mSimPipe->sim_pipe_pipeline_reg[MEM].B = mSimPipe->sim_pipe_pipeline_reg_EXE[i].B;
                    mSimPipe->sim_pipe_pipeline_reg[MEM].Rd = mSimPipe->sim_pipe_pipeline_reg_EXE[i].Rd;
                   /* unsigned temp;
                    opcode_t tempOpCode;
                    temp = mSimPipe->sim_pipe_pipeline_reg[MEM].Rd;
                    tempOpCode = mSimPipe->sim_pipe_pipeline_reg_EXE[i].IR.opcode;
                    if (temp < REGISTER_FILE_SIZE) {
                        if ((is_int_alu(tempOpCode)) || (tempOpCode == LW)) {
                            mSimPipe->sim_pipe_reg_file[temp].isDestination = TRUE;
                        } else if ((is_fp_alu(tempOpCode)) || (tempOpCode == LWS)) {
                            mSimPipe->sim_pipe_reg_file_fp[temp].isDestination = TRUE;
                        }
                    } else {
                        //TODO: Error handling
                    }*/
                    mSimPipe->sim_pipe_pipeline_reg[MEM].isAvailable = TRUE;
                    mSimPipe->sim_pipe_pipeline_reg_EXE[i].isAvailable = FALSE;
                    mSimPipe->sim_pipe_pipeline_reg_EXE[i].IR.opcode = NOP;
                    mSimPipe->exec_units[i].instruction.opcode = NOP;
                } else {
                    //Exe has processed instr but mem is busy so retry next cycle
                    mSimPipe->exec_units[i].busy++;
                    //mStalls_Count++;
                }
            }
        }
    }else
    {
        if ((is_memory_ongoing == FALSE) && (mSimPipe->sim_pipe_pipeline_reg[MEM].isAvailable == FALSE)) {
            mSimPipe->sim_pipe_pipeline_reg[MEM].IR.opcode = EOP;
            mSimPipe->sim_pipe_pipeline_reg[MEM].isAvailable = TRUE;
        }
    }
    if(mSimPipe->sim_pipe_pipeline_reg[MEM].IR.opcode == EOP)
    {
        mSimPipe->sim_pipe_pipeline_reg[MEM].B = UNDEFINED;
        mSimPipe->sim_pipe_pipeline_reg[MEM].Rd = UNDEFINED;
        mSimPipe->sim_pipe_pipeline_reg[MEM].ALU_Output = UNDEFINED;
        mSimPipe->sim_pipe_pipeline_reg[MEM].Cond = UNDEFINED;
    }
}

void pipe_MEM_Handler(sim_pipe_fp* mSimPipe)
{
    static unsigned mMemDelay = 0;

    if(is_branch(mSimPipe->sim_pipe_pipeline_reg[MEM].IR.opcode) && (is_branch_ongoing == TRUE))
    {
        is_branch_calculated = TRUE;
        if(mSimPipe->sim_pipe_pipeline_reg[MEM].Cond == 1)
        {
            mSimPipe->sim_pipe_pipeline_reg[MEM].Cond = 0;
            mSimPipe->sim_pipe_pipeline_reg[IF].PC = mSimPipe->sim_pipe_pipeline_reg[MEM].ALU_Output;
        }
    }
    if((is_memory(mSimPipe->sim_pipe_pipeline_reg[MEM].IR.opcode)) && (is_memory_ongoing == FALSE))
    {
        mMemDelay = mSimPipe->data_memory_latency + 1;
        is_memory_ongoing = TRUE;
        mSimPipe->sim_pipe_pipeline_reg[MEM].isAvailable = FALSE;
    }
    if(is_memory_ongoing == TRUE)
    {
        if(mMemDelay <= 1)
        {
            is_memory_ongoing = FALSE;
            mSimPipe->sim_pipe_pipeline_reg[MEM].isAvailable = TRUE;
        }else
        {
           // mStalls_Count++;
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
        opcode_t tempOpCode;
        temp = mSimPipe->sim_pipe_pipeline_reg[MEM].Rd;
        tempOpCode = mSimPipe->sim_pipe_pipeline_reg[MEM].IR.opcode;
        if(temp < REGISTER_FILE_SIZE)
        {
            if((is_int_alu(tempOpCode)) || (tempOpCode == LW))
            {
                mSimPipe->sim_pipe_reg_file[temp].isDestination = TRUE;
            }else if((is_fp_alu(tempOpCode)) || (tempOpCode == LWS))
            {
                mSimPipe->sim_pipe_reg_file_fp[temp].isDestination = TRUE;
            }
        }else
        {
            //TODO: Error handling
        }

        if ((is_int_alu(tempOpCode)) || (is_fp_alu(mSimPipe->sim_pipe_pipeline_reg[MEM].IR.opcode)))
        {
            mSimPipe->sim_pipe_pipeline_reg[WB].ALU_Output = mSimPipe->sim_pipe_pipeline_reg[MEM].ALU_Output;
        }else
        {
            mSimPipe->sim_pipe_pipeline_reg[WB].ALU_Output = UNDEFINED;
        }
        if ((tempOpCode == LW) || (tempOpCode == LWS))
        {
            temp = mSimPipe->sim_pipe_pipeline_reg[MEM].ALU_Output;
            if(temp < mSimPipe->data_memory_size)
            {
                mSimPipe->sim_pipe_pipeline_reg[WB].LMD = char2unsigned(&mSimPipe->data_memory[temp]);
            }else
            {
                //TODO: error handling
                cout << "LW out of bound memory" << endl;
            }
        }else
        {
            mSimPipe->sim_pipe_pipeline_reg[WB].LMD = UNDEFINED;
        }
        if ((tempOpCode == SW) || (tempOpCode == SWS))
        {
            //TODO: Check if write address is valid
            temp = mSimPipe->sim_pipe_pipeline_reg[MEM].ALU_Output;
            if(temp < mSimPipe->data_memory_size)
            {
                mSimPipe->write_memory(mSimPipe->sim_pipe_pipeline_reg[MEM].ALU_Output,
                                       mSimPipe->sim_pipe_pipeline_reg[MEM].B);
            }else
            {
                //TODO: error handling
                cout << "SW(S) out of bound memory" << endl;
            }

        } else
        {
            //TODO: Do Nothing, opcode doesn't require MEM stage handling
        }
        mSimPipe->sim_pipe_pipeline_reg[MEM].IR.opcode = NOP;
        mSimPipe->sim_pipe_pipeline_reg[MEM].isAvailable = FALSE;
        mSimPipe->sim_pipe_pipeline_reg[WB].isAvailable = TRUE;
    }
    if(mSimPipe->sim_pipe_pipeline_reg[WB].IR.opcode == EOP)
    {
        mSimPipe->sim_pipe_pipeline_reg[WB].LMD = UNDEFINED;
        mSimPipe->sim_pipe_pipeline_reg[WB].ALU_Output = UNDEFINED;
    }
}

void pipe_WB_Handler(sim_pipe_fp* mSimPipe)
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
            if (is_int_alu(mSimPipe->sim_pipe_pipeline_reg[WB].IR.opcode))
            {
                mSimPipe->sim_pipe_reg_file[tempRd].regVal = mSimPipe->sim_pipe_pipeline_reg[WB].ALU_Output;
                mSimPipe->sim_pipe_reg_file[tempRd].isDestination = FALSE;
            }else if (is_fp_alu(mSimPipe->sim_pipe_pipeline_reg[WB].IR.opcode))
            {
                mSimPipe->sim_pipe_reg_file_fp[tempRd].regVal = mSimPipe->sim_pipe_pipeline_reg[WB].ALU_Output;
                mSimPipe->sim_pipe_reg_file_fp[tempRd].isDestination = FALSE;
            }else if (mSimPipe->sim_pipe_pipeline_reg[WB].IR.opcode == LW)
            {
                mSimPipe->sim_pipe_reg_file[tempRd].regVal = mSimPipe->sim_pipe_pipeline_reg[WB].LMD;
                mSimPipe->sim_pipe_reg_file[tempRd].isDestination = FALSE;
            }else if (mSimPipe->sim_pipe_pipeline_reg[WB].IR.opcode == LWS)
            {
                mSimPipe->sim_pipe_reg_file_fp[tempRd].regVal = mSimPipe->sim_pipe_pipeline_reg[WB].LMD;
                mSimPipe->sim_pipe_reg_file_fp[tempRd].isDestination = FALSE;
            }else
            {
                //Nothing to be done in WB
            }
        } else {
            //TODO: error handling;
        }
        mSimPipe->sim_pipe_pipeline_reg[WB].IR.opcode = NOP;
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
            //TODO: Error Handling
            break;
    }
    return mRetVal;
}

unsigned isOpCodeFpType(opcode_t mOpCode)
{
    unsigned mRetVal=FALSE;
    if(is_fp_alu(mOpCode) || mOpCode == LWS || mOpCode == SWS)
    {
        mRetVal=TRUE;
    }
    return mRetVal;
}