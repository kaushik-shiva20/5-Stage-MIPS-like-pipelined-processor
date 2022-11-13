#include "sim_pipe.h"
#include <iostream>
#include <stdlib.h>

using namespace std;

/* Test case for pipelined simuator */
/* DO NOT MODIFY */

int main(int argc, char **argv){

	unsigned i, j;

	// instantiates the simulator with a 1MB data memory
	sim_pipe *mips = new sim_pipe(1024*1024, 4);

	//loads program in instruction memory at address 0x10000000
	mips->load_program("asm/code.asm", 0x10000000);

	//initialize data memory and prints its content (for the specified address ranges)
	for (i = 0xA000, j=1; i<0xA020; i+=4, j+=1) mips->write_memory(i,j);
	
	cout << "\nBEFORE PROGRAM EXECUTION..." << endl;
	cout << "======================================================================" << endl << endl;
	
//prints the value of the memory and registers
	mips->print_registers();
	mips->print_memory(0xA000, 0xA028);
	mips->print_memory(0xB000, 0xB028);

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

	// instructions 5-14
	cout << "Instructions 5-14: inspecting the registers after each instruction..." << endl;
	cout << "======================================================================" << endl << endl;

	for (i=5; i < 15; i++){
		cout << "INSTRUCTION #" << dec << i << endl;
		mips->run(5);
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
	mips->print_memory(0xA000, 0xA028);
	mips->print_memory(0xB000, 0xB028);
	
	cout << endl;

	// prints the number of instructions executed and IPC
	cout << "Instruction executed = " << dec << mips->get_instructions_executed() << endl;
	cout << "Clock cycles = " << dec << mips->get_clock_cycles() << endl;
	cout << "Stall inserted = " << dec  << mips->get_stalls() << endl;
	cout << "IPC = " << dec << mips->get_IPC() << endl;

	delete mips;
}
