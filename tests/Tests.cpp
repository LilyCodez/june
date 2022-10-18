#include "Compiler.h"

#include "Util.h"

#include <cstring>
#include <iostream>

#include <llvm/Support/raw_ostream.h>

template<typename T>
bool CheckEQ(T Expected, T Found) {
	june::SetTerminalColor(june::TerminalColorYellow);
	llvm::outs() << "CheckEqual(e/f): ";
	june::SetTerminalColor(june::TerminalColorDefault);
	llvm::outs() << Expected << " == " << Found;
	bool tof = Expected == Found;
	if (tof) {
		june::SetTerminalColor(june::TerminalColorGreen);
		llvm::outs() << " (SUCCESS)";
	} else {
		june::SetTerminalColor(june::TerminalColorRed);
		llvm::outs() << " (FAIL)";
	}
	june::SetTerminalColor(june::TerminalColorDefault);
	llvm::outs() << '\n';
	return tof;
}

#define SRC(x) JUNE_COMPILER_TEST_SOURCE_DIR x
#define LIB_SRC(x) JUNE_COMPILER_TEST_SOURCE_DIR "libtest/" x

u32 Failed = 0;
u32 Succeeded = 0;
llvm::SmallVector<const c8*, 4> FailedTests;

void RunTest(const c8* TestDirectoryPath, int TestErrorCode) {

#ifdef __unix__
	assert(!"Cannot properly run tests on unix because error code range is 0-255");
#endif

	llvm::outs() << "Testing: \"" << TestDirectoryPath << "\"\n";
	llvm::outs() << "----------------------------\n";

	llvm::SmallVector<const c8*, 1> SourceDirectories;
	SourceDirectories.push_back(TestDirectoryPath);

	june::Compiler Compiler;
	Compiler.StandAlone = true;
	//Compiler.PathToStandardLibrary = JUNE_COMPILER_STDLIB_SOURCE_DIR;
	//Compiler.EmitDebugInfo = true;
	//Compiler.Verbose = true;
	//Compiler.DisplayLLVMIR = true;
	Compiler.DisplayAST = true;
	Compiler.Compile(SourceDirectories);

	if (!Compiler.FoundCompileError) {
		int ErrorCode = system("program");
		if (CheckEQ(TestErrorCode, ErrorCode)) {
			++Succeeded;
		} else {
			++Failed;
			FailedTests.push_back(TestDirectoryPath);
		}
	} else {
		FailedTests.push_back(TestDirectoryPath);
		++Failed;
	}

	llvm::outs() << "\n\n";
}

void RunStdLibTest(const c8* TestDirectoryPath) {
	
	llvm::SmallVector<const c8*, 1> SourceDirectories;
	SourceDirectories.push_back(TestDirectoryPath);

	june::Compiler Compiler;
	//Compiler.DisplayLLVMIR = true;
	//Compiler.EmitDebugInfo = true;
	Compiler.PathToStandardLibrary = JUNE_COMPILER_STDLIB_SOURCE_DIR;
	Compiler.DisplayTimes = true;
	Compiler.Compile(SourceDirectories);

	if (!Compiler.FoundCompileError) {
		system("program");
	}

	llvm::outs() << "\n\n";
}

int main() {

	//RunStdLibTest(LIB_SRC("guessing"));
	
	RunTest(SRC("main/Main1.june"), 0);
	RunTest(SRC("main/Main2.june"), 55);
	RunTest(SRC("exprs/Exprs1.june"), 214 + 41 / 2 - 663 * 3);
	RunTest(SRC("exprs/Exprs2.june"), []() {
		s32 b = 22;
		s32 sum = 44 * 3 + 55 - 421 * b;
		s32 g = 4;
		sum /= g + 1;
		sum *= 3 - 1;
		sum = sum * sum;
		return sum;
		}());
	RunTest(SRC("exprs/Exprs3.june"), []() {
		s32 a = 22;
		s32 b = a << 6;
		s32 c = b % 20;
		return c + (312312 >> 3) ^ 7;
		}());
	RunTest(SRC("exprs/Exprs4.june"), []() {
		s32 g = 0;
		++g;
		--g;
		++g;
		g++;
		g = g--;
		g = g++;
		g = g++;
		return g;
		}());
	RunTest(SRC("functioncall/FunctionCall1.june"), 523);
	RunTest(SRC("functioncall/FunctionCall2.june"), 425 + 22 + 41 + 53);
	RunTest(SRC("loops/Loops1.june"), 10);
	RunTest(SRC("loops/Loops2.june"), 10);
	RunTest(SRC("loops/Loops3.june"), 10);
	RunTest(SRC("loops/Loops4.june"), 15);
	RunTest(SRC("loops/Loops5.june"), []() {
		s32 sum = 0;
		for (s32 i = 0; ; i++) {
			if (i > 50) {
				break;
			}
			if (i % 2 == 0) {
				continue;
			}
			sum += i;
		}
		return sum;
		}());
	RunTest(SRC("loops/Loops6.june"), 124 + 346 + 22 + 15 + 77);
	RunTest(SRC("loops/Loops7.june"), 214 + 22 + 55 + 21 + 553 + 2 + 52 + 14);
	RunTest(SRC("fixedarrays/FixedArrays1.june"), 21 + 55 + 11 + 56 + 3);
	RunTest(SRC("fixedarrays/FixedArrays2.june"), 412 + 21 + 5 + 6 + 4);
	RunTest(SRC("fixedarrays/FixedArrays3.june"), 41 + 36 + 412 + 121 + 45 + 56);
	RunTest(SRC("fixedarrays/FixedArrays4.june"), 214 + 452 + 12 + 32 + 11);
	RunTest(SRC("fixedarrays/FixedArrays5.june"), 253 + 23 + 13);
	RunTest(SRC("fixedarrays/FixedArrays6.june"), 5 * 8);
	RunTest(SRC("fixedarrays/FixedArrays7.june"), 1 + 2 + 3 + 4 + 5);
	RunTest(SRC("fixedarrays/FixedArrays8.june"), 12 + 465 + 5437 + 12 + 61);
	RunTest(SRC("multifiles"), 65 + 4);
	RunTest(SRC("records/Records1.june"), 14 + 15);
	RunTest(SRC("records/Records2.june"), 1415 + 156 + 76534);
	RunTest(SRC("records/Records3.june"), 124 + 66 + 25);
	RunTest(SRC("records/records4"), 56 + 14);
	RunTest(SRC("records/Records5.june"), 325 + 15 + 325 + 15);
	RunTest(SRC("records/Records6.june"), 5 * 5 * (25 + 55));
	RunTest(SRC("records/Records7.june"), 55);
	RunTest(SRC("records/Records8.june"), 138);
	RunTest(SRC("othertests/Sizeof.june"), 4 + 1 + 4 + 4 + 8 + 8);
	RunTest(SRC("othertests/This.june"), 252);
	RunTest(SRC("othertests/InferedTypes.june"), 11 + 11 + 365 + 214 + 14 + 65 + 11);
	RunTest(SRC("globals/Globals1.june"), 44);
	RunTest(SRC("globals/Globals2.june"), 32 + 154 + 32);
	RunTest(SRC("globals/Globals3.june"), 22 + 1111 + 34 + 66);
	RunTest(SRC("globals/Globals4.june"), 154 + 154 + 11 + 11 + 11);
	RunTest(SRC("varfunccall/VarFuncCall1.june"), 11);
	RunTest(SRC("varfunccall/VarFuncCall2.june"), 15323);
	RunTest(SRC("varfunccall/VarFuncCall3.june"), 6578 + 12);
	RunTest(SRC("varfunccall/VarFuncCall4.june"), 1241 + 778);
	RunTest(SRC("generics/Generics1.june"), 16 + 6);
	RunTest(SRC("generics/Generics2.june"), 558);
	//RunTest(SRC("playground"), 0);

	if (Succeeded + Failed > 0) {
		llvm::outs() << "Passed/Tested (" << Succeeded << "/" << (Succeeded + Failed) << ")\n";
		if (Failed) {
			llvm::outs() << "Failed Tests\n";
			for (const c8* Test : FailedTests) {
				llvm::outs() << "\"" << Test << "\"" << '\n';
			}
		}
	}

	return 0;
}