CC = g++
OPT = -g
WARN = -Wall
CFLAGS = $(OPT) $(WARN) 

# List corresponding compiled object files here (.o files)
SIM_OBJ = sim_pipe.o 
SIM_OBJ_FP = sim_pipe_fp.o 

TESTCASES = testcase1 testcase2 testcase3 testcase4 testcase5 testcase6 testcase_fp0 testcase_fp1 testcase_fp2 testcase_fp3 testcase_fp4 testcase_fp5
 
#################################

# default rule
all:	$(TESTCASES)

# generic rule for converting any .cc file to any .o file
.cc.o:
	$(CC) $(CFLAGS) -c *.cc

#rule for creating the object files for all the testcases in the "testcases" folder
testcase: 
	$(MAKE) -C testcases

# rules for making testcases
testcase1: .cc.o testcase 
	$(CC) -o bin/testcase1 $(CFLAGS) $(SIM_OBJ) testcases/testcase1.o

testcase2: .cc.o testcase
	$(CC) -o bin/testcase2 $(CFLAGS) $(SIM_OBJ) testcases/testcase2.o

testcase3: .cc.o testcase 
	$(CC) -o bin/testcase3 $(CFLAGS) $(SIM_OBJ) testcases/testcase3.o

testcase4: .cc.o testcase
	$(CC) -o bin/testcase4 $(CFLAGS) $(SIM_OBJ) testcases/testcase4.o

testcase5: .cc.o testcase 
	$(CC) -o bin/testcase5 $(CFLAGS) $(SIM_OBJ) testcases/testcase5.o

testcase6: .cc.o testcase
	$(CC) -o bin/testcase6 $(CFLAGS) $(SIM_OBJ) testcases/testcase6.o

testcase_fp0: .cc.o testcase 
	$(CC) -o bin/testcase_fp0 $(CFLAGS) $(SIM_OBJ_FP) testcases/testcase_fp0.o

testcase_fp1: .cc.o testcase
	$(CC) -o bin/testcase_fp1 $(CFLAGS) $(SIM_OBJ_FP) testcases/testcase_fp1.o

testcase_fp2: .cc.o testcase 
	$(CC) -o bin/testcase_fp2 $(CFLAGS) $(SIM_OBJ_FP) testcases/testcase_fp2.o

testcase_fp3: .cc.o testcase
	$(CC) -o bin/testcase_fp3 $(CFLAGS) $(SIM_OBJ_FP) testcases/testcase_fp3.o

testcase_fp4: .cc.o testcase
	$(CC) -o bin/testcase_fp4 $(CFLAGS) $(SIM_OBJ_FP) testcases/testcase_fp4.o

testcase_fp5: .cc.o testcase
	$(CC) -o bin/testcase_fp5 $(CFLAGS) $(SIM_OBJ_FP) testcases/testcase_fp5.o

# type "make clean" to remove all .o files plus the sim binary
clean:
	rm -f testcases/*.o
	rm -f *.o 
	rm -f bin/*
