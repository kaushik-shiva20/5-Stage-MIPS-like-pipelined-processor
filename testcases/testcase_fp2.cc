#include "sim_pipe_fp.h"
#include <iostream>
#include <cstring>
#include <stdlib.h>

using namespace std;

/* Test case for pipelined simuator */
/* DO NOT MODIFY */

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


int main(int argc, char **argv){

	unsigned i, j;

	// instantiates the simulator with a 1MB data memory
	sim_pipe_fp *mips = new sim_pipe_fp(1024*1024, 0);

	mips->init_exec_unit(INTEGER, 0, 1);
	mips->init_exec_unit(ADDER, 4, 1);
	mips->init_exec_unit(MULTIPLIER, 9, 2);
	mips->init_exec_unit(DIVIDER, 19, 1);

	//loads program in instruction memory at address 0x10000000
	mips->load_program("asm/codefp0.asm", 0x10000000);

	//initialize data memory and prints its content (for the specified address ranges)
	for (i = 0xA000, j=1; i<0xA010; i+=4, j+=1) mips->write_memory(i,float2unsigned((float)j*10));

	//initialize register
	mips->set_int_register(0,0);
	mips->set_int_register(1,0xA000);
	for (i=0; i<10; i++) mips->set_fp_register(i, (float)i);
	
	cout << "\nBEFORE PROGRAM EXECUTION..." << endl;
	cout << "======================================================================" << endl << endl;
	
	//prints the value of the memory and registers
	mips->print_registers();
	mips->print_memory(0xA000, 0xA010);

	// executes the program	
	cout << "\n*****************************" << endl;
	cout << "STARTING THE PROGRAM..." << endl;
	cout << "*****************************" << endl << endl;

	// first 20 clock cycles
	cout << "First 20 clock cycles: inspecting the registers at each clock cycle..." << endl;
	cout << "======================================================================" << endl << endl;

	for (i=0; i<20; i++){
		cout << "CLOCK CYCLE #" << dec << i << endl;
		mips->run(1);
		mips->print_registers();
		cout << endl;
	}

	// runs program to completion
	cout << "EXECUTING PROGRAM TO COMPLETION..." << endl << endl;
	mips->run(); 

	cout << "PROGRAM TERMINATED\n";
	cout << "===================" << endl << endl;

	//prints the value of registers and data memory
	mips->print_registers();
	mips->print_memory(0xA000, 0xA010);
	
	cout << endl;

	// prints the number of instructions executed and IPC
	cout << "Instruction executed = " << dec << mips->get_instructions_executed() << endl;
	cout << "Clock cycles = " << dec << mips->get_clock_cycles() << endl;
	cout << "Stall inserted = " << dec  << mips->get_stalls() << endl;
	cout << "IPC = " << dec << mips->get_IPC() << endl;

	delete mips;
}
