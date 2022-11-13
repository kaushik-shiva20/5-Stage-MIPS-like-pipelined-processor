#include "sim_pipe.h"
#include <iostream>
#include <stdlib.h>

using namespace std;

/* Test case for pipelined simuator */ 
/* DO NOT MODIFY */

int main(int argc, char **argv){

	unsigned i, j;

	// instantiates the sim_pipe with a 1MB data memory
	sim_pipe *mips = new sim_pipe(1024*1024, 0);

	//loads program in instruction memory at address 0x10000000
	mips->load_program("asm/no_dep.asm", 0x10000000);

	//initialize general purpose registers
	for (i=0; i<7; i++) mips->set_gp_register(i,i);

	//initialize data memory and prints its content (for the specified address ranges)
	for (i = 0x0, j=10; i<0x20; i+=4, j+=10) mips->write_memory(i,j);
	
	cout << "\nBEFORE PROGRAM EXECUTION..." << endl;
	cout << "======================================================================" << endl << endl;
	
	//prints the value of the memory and registers
	mips->print_registers();
	mips->print_memory(0x0, 0x20);

	// executes the program	
	cout << "\n*****************************" << endl;
	cout << "STARTING THE PROGRAM..." << endl;
	cout << "*****************************" << endl << endl;

	// first 8 clock cycles
	cout << "First 8 clock cycles: inspecting the registers at each clock cycle..." << endl;
	cout << "======================================================================" << endl << endl;

	for (i=0; i<8; i++){
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
	mips->print_memory(0x0, 0x20);
	
	cout << endl;

	// prints the number of instructions executed and IPC
	cout << "Instruction executed = " << dec << mips->get_instructions_executed() << endl;
	cout << "Clock cycles = " << dec << mips->get_clock_cycles() << endl;
	cout << "Stall inserted = " << dec  << mips->get_stalls() << endl;
	cout << "IPC = " << dec << mips->get_IPC() << endl;

	delete mips;
}
