#include "Compiler.h"

#include "Util.h"
#include "TestProcessUtil.h"

#include <cstring>
#include <iostream>


#include <llvm/Support/raw_ostream.h>

#define SRC(x) JUNE_COMPILER_TEST_SOURCE_DIR x
#define LIB_SRC(x) JUNE_COMPILER_TEST_SOURCE_DIR "libtest/" x

u32 Failed = 0;
u32 Succeeded = 0;
llvm::SmallVector<const c8*, 4> FailedTests;

void RunTest(const c8* TestDirectoryPath, const std::string& ExpectedOutput) {

	llvm::outs() << "Testing: \"" << TestDirectoryPath << "\"\n";
	llvm::outs() << "----------------------------\n";

	llvm::SmallVector<const c8*, 1> SourceDirectories;
	SourceDirectories.push_back(TestDirectoryPath);
	SourceDirectories.push_back(SRC("Tests.june"));

	june::Compiler Compiler;
	Compiler.StandAlone = true;
	//Compiler.PathToStandardLibrary = JUNE_COMPILER_STDLIB_SOURCE_DIR;
	//Compiler.EmitDebugInfo = true;
	//Compiler.Verbose = true;
	//Compiler.DisplayLLVMIR = true;
	//Compiler.DisplayAST = true;
	Compiler.Compile(SourceDirectories);

	if (!Compiler.FoundCompileError) {

		auto [StdOutResult, NoErrors] = RunProcess("program");
		if (!NoErrors) {
			llvm::outs() << "Failed to run the compiled program\n";
			FailedTests.push_back(TestDirectoryPath);
			++Failed;
			return;
		}

		if (StdOutResult == ExpectedOutput) {
			llvm::outs() << "Status:";
			june::SetTerminalColor(june::TerminalColorGreen);
			llvm::outs() << " (SUCCESS)";
			june::SetTerminalColor(june::TerminalColorDefault);
			llvm::outs() << '\n';
			llvm::outs() << "Program Standard Output: \"";
			llvm::outs() << StdOutResult << "\"\n";
			++Succeeded;
		} else {
			llvm::outs() << "Status:";
			june::SetTerminalColor(june::TerminalColorRed);
			llvm::outs() << " (FAIL)";
			june::SetTerminalColor(june::TerminalColorDefault);
			llvm::outs() << '\n';
			llvm::outs() << "Program Standard Output:  \"";
			llvm::outs() << StdOutResult << "\"\n";
			llvm::outs() << "Expected Standard Output: \"";
			llvm::outs() << ExpectedOutput << "\"\n";
			FailedTests.push_back(TestDirectoryPath);
			++Failed;
		}
	} else {
		FailedTests.push_back(TestDirectoryPath);
		++Failed;
	}

	llvm::outs() << "\n\n";
}

void RunTest(const c8* TestDirectoryPath, s32 Value) {
	RunTest(TestDirectoryPath, std::to_string(Value));
}

int main() {

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
		std::string Res = "";
		for (s32 i = 0; ; i++) {
			if (i > 50) {
				break;
			}
			if (i % 2 == 0) {
				continue;
			}
			Res += std::to_string(i) + " ";
		}
		return Res;
		}());
	RunTest(SRC("loops/Loops6.june"), "124 346 22 15 77 ");
	RunTest(SRC("loops/Loops7.june"), "214 22 55 21 553 0 2 52 14 ");
	RunTest(SRC("fixedarrays/FixedArrays1.june"), "21 55 11 56 3 ");
	RunTest(SRC("fixedarrays/FixedArrays2.june"), "412 21 5 6 4 0 ");
	RunTest(SRC("fixedarrays/FixedArrays3.june"), "412 77 121 45 56 ");
	RunTest(SRC("fixedarrays/FixedArrays4.june"), "214 452 12 32 11 ");
	RunTest(SRC("fixedarrays/FixedArrays5.june"), "253 23 0 13 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 ");
	RunTest(SRC("fixedarrays/FixedArrays6.june"), "5 5 5 5 5 5 5 5 ");
	RunTest(SRC("fixedarrays/FixedArrays7.june"), "1 2 3 4 5 ");
	RunTest(SRC("fixedarrays/FixedArrays8.june"), "12 465 5437 12 61 ");
	RunTest(SRC("records/Records1.june"), "14 15");
	RunTest(SRC("records/Records2.june"), "1415 156 76534");
	RunTest(SRC("records/Records3.june"), "124 66 25");
	RunTest(SRC("records/records4"), "14 56");
	RunTest(SRC("records/Records5.june"), "15 325");
	RunTest(SRC("records/Records6.june"), "25 55 25 55 25 55 25 55 25 55 25 55 25 55 25 55 25 55 25 55 25 55 25 55 25 55 25 55 25 55 25 55 25 55 25 55 25 55 25 55 25 55 25 55 25 55 25 55 25 55 ");
	RunTest(SRC("records/Records7.june"), "55");
	RunTest(SRC("records/Records8.june"), "14 124");
	RunTest(SRC("othertests/Sizeof.june"), "4 1 16 8");
	RunTest(SRC("othertests/This.june"), "252");
	RunTest(SRC("othertests/InferedTypes.june"), "214 11 376 14 65 11");
	RunTest(SRC("globals/Globals1.june"), "44");
	RunTest(SRC("globals/Globals2.june"), "32 186");
	RunTest(SRC("globals/Globals3.june"), "22 1111 34 66");
	RunTest(SRC("globals/Globals4.june"), "154 154 11 11 11");
	RunTest(SRC("varfunccall/VarFuncCall1.june"), "11");
	RunTest(SRC("varfunccall/VarFuncCall2.june"), "15323");
	RunTest(SRC("varfunccall/VarFuncCall3.june"), 6578 + 12);
	RunTest(SRC("varfunccall/VarFuncCall4.june"), "1241 778");
	RunTest(SRC("generics/Generics1.june"), "16 6");
	RunTest(SRC("generics/Generics2.june"), "156 402");
	RunTest(SRC("tuples/Tuples1.june"), "343 11");
	RunTest(SRC("tuples/Tuples2.june"), "1 2 3 4");
	RunTest(SRC("tuples/Tuples3.june"), "14 888 99 3");
	RunTest(SRC("tuples/Tuples4.june"), "66 11 43");
	
	if (Succeeded + Failed > 0) {
		llvm::outs() << "Passed/Tested (" << Succeeded << "/" << (Succeeded + Failed) << ")\n";
		if (Failed) {
			llvm::outs() << "Failed Tests\n";
			for (const c8* Test : FailedTests) {
				llvm::outs() << "\"" << Test << "\"" << '\n';
			}
			return 1;
		}
	}

	return 0;
}