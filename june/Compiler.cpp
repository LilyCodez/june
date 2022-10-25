#include "Compiler.h"
#include "Parser.h"
#include "Analysis.h"
#include "Logger.h"
#include "Util.h"
#include "AstPrinter.h"
#include "JuneContext.h"
#include "IRGen.h"
#include "CodeGen.h"
#include "TypeBinding.h"

#include <llvm/Support/raw_ostream.h>
#include <iostream>
#include <llvm/IR/Verifier.h>

// Creating a global instance because for some reason LLVM
// does not clean up target machines properly when deleting
// them
static llvm::TargetMachine* LLMachineTarget = nullptr;

june::Compiler::Compiler()
	: Context(*new JuneContext) {
}

june::Compiler::~Compiler() {
	delete &Context;
}

void june::Compiler::Compile(llvm::SmallVector<const c8*, 1>& SourceDirectories) {

	u64 ParseTimeBegin = GetTimeInMilliseconds();

	Context.Init(EmitDebugInfo);
	Context.CompileAsStandAlone = StandAlone;

	// Initializing the llvm machine early so that system
	// dependent information can be used parsing/code-generating.
	if (!InitLLVMNativeTarget()) {
		FoundCompileError = true;
		return;
	}

	if (!LLMachineTarget) {
		LLMachineTarget = CreateLLVMTargetMache();
	}

	SetTargetToModule(Context.LLJuneModule, LLMachineTarget);

	if (!StandAlone) {
		if (const c8* StdLibPath = GetStdLibPath()) {
			SourceDirectories.push_back(StdLibPath);
		} else {
			Logger::GlobalError(llvm::errs(),
				"Environment variable missing for june's standard library. Please set variable 'JuneStdLibPath' to point towards the standard library");
			FoundCompileError = true;
			return;
		}
	}

	// Creating FileUnits for the .june files
	for (const c8* SourceDirectory : SourceDirectories) {
		std::filesystem::path DirectoryPath = std::filesystem::path(SourceDirectory);
		if (!std::filesystem::exists(DirectoryPath)) {
			Logger::GlobalError(llvm::errs(),
				"Source directory \"%s\" does not exist", SourceDirectory);
			FoundCompileError = true;
			return;
		}
		// TODO: Check permissions?
		
		if (std::filesystem::is_directory(DirectoryPath)) {
			std::string Path = DirectoryPath.generic_string();
			CollectDirectoryFiles(DirectoryPath, Path.length() + (Path.back() == '/' ? 0 : 1));
		} else {
			// The user specified an absolute path to a file.
			if (DirectoryPath.extension() != ".june") {
				Logger::GlobalError(llvm::errs(),
					"Expected source file with extension type .june for file: \"%s\"", SourceDirectory);
				return;
			}
			AddFileUnit(DirectoryPath.filename().generic_string(),
				        std::filesystem::absolute(DirectoryPath).generic_string());
		}
	}

	if (FoundCompileError) {
		return;
	}

	if (!StandAlone) {

		// Ensuring that the standard library isn't missing any essential dependencies
		if (!Context.StringFU) {
			Logger::GlobalError(llvm::errs(), "Standard library missing 'String' file");
			FoundCompileError = true;
			return;
		}

		if (!Context.SysFU) {
			Logger::GlobalError(llvm::errs(), "Standard library missing 'Sys' file");
			FoundCompileError = true;
			return;
		}

		// Parsing the String class early since it has a high dependency
		auto it = FilesNeedingParsing.find(Context.StringFU->FL.PathKey);
		ParseFiles(it->second);
	}

	// Parsing all .june files
	while (!FilesNeedingParsing.empty()) {
		ParseNextFiles();
	}

	// Checking to make sure a main entry point was found
	if (Context.MainEntryFunc) {
		Context.RequestGen(Context.MainEntryFunc);
	} else {
		FoundCompileError = true;
		Logger::GlobalError(llvm::errs(), "Could not find entry point function");
		return;
	}

	if (!StandAlone) {
		auto it = Context.SysFU->GlobalFuncs.find(Identifier("initialize"));
		if (it == Context.SysFU->GlobalFuncs.end()) {
			Logger::GlobalError(llvm::errs(), "Standard library missing 'initialize' function from 'Sys' file");
			FoundCompileError = true;
			return;
		}
		Context.RequestGen(it->second[0]);
	}

	// Computing compile time values.
	ComptimeGen Comptime(Context);
	while (!Context.ComptimeValues.empty()) {
		ComptimeValue CV = Context.ComptimeValues.front();
		Context.ComptimeValues.pop();
		if (CV.Log.HasError) continue;
		Comptime.Compute(CV);
		
		if (CV.Log.HasError) {
			FoundCompileError = true;
		}
	}

	// Create a debug compilation unit for each FileUnit
	if (EmitDebugInfo) {
		for (auto FUItr = Context.FileUnits.begin(),
			FUEnd = Context.FileUnits.end();
			FUItr != FUEnd; FUItr++
			) {
			FUItr->second->DIEmitter->EmitCompilationUnit(FUItr->second);
		}
	}

	// Checking and generating code
	while (!Context.QuededDeclsToGen.empty()) {
		JuneContext::DeclGen DGen = Context.QuededDeclsToGen.front();
		Decl* D = DGen.D;
		Context.QuededDeclsToGen.pop();

		if (D->FU->Log.HasError) {
			FoundCompileError = true;
			continue;
		}

		Analysis A(Context, D->FU->Log, true);
		if (D->is(AstKind::FUNC_DECL)) {
			A.CheckFuncDecl(ocast<FuncDecl*>(D));
		} else if (D->is(AstKind::GENERIC_FUNC_DECL)) {
			A.CheckGenericFuncDecl(ocast<GenericFuncDecl*>(D), DGen.TypeBindingId);
		} // else if VAR_DECL  : should already have been checked.
		
		if (D->FU->Log.HasError) {
			FoundCompileError = true;
			continue;
		}

		// Only generating code if there are absolutely no errors
		if (!FoundCompileError) {
			IRGen Gen(Context, EmitDebugInfo, DisplayLLVMIR | Verbose);
			if (D->is(AstKind::FUNC_DECL)) {
				Gen.GenFunc(ocast<FuncDecl*>(D));
			} else if (D->is(AstKind::GENERIC_FUNC_DECL)) {
				Gen.GenGenericFunc(ocast<GenericFuncDecl*>(D), DGen.TypeBindingId);
			} else {
				Gen.GenGlobalVar(ocast<VarDecl*>(D));
			}
		}
	}

	// Checking any code that was not generated
	while (!Context.UncheckedDecls.empty()) {
		auto it = Context.UncheckedDecls.begin();
		Decl* D = *it;

		if (D->FU->Log.HasError) {
			// TODO: would like to distinguish between parser
			// generated error vs. non-parser generated error
			// so that it will still check as long as it was
			// not a parser error.
			Context.UncheckedDecls.erase(it);
			continue;
		} 

		Analysis A(Context, D->FU->Log, false);
		if (D->is(AstKind::FUNC_DECL)) {
			A.CheckFuncDecl(ocast<FuncDecl*>(D));
		} else if (D->is(AstKind::VAR_DECL)) {
			A.CheckVarDecl(ocast<VarDecl*>(D));
		} else if (D->is(AstKind::VAR_DECL_LIST)) {
			A.CheckVarDeclList(ocast<VarDeclList*>(D));
		} else {
			assert(!"Failed to implement check");
		}

		if (D->FU->Log.HasError) {
			FoundCompileError = true;
		}
	}

	if (FoundCompileError) {
		return;
	}

	IRGen Gen(Context, EmitDebugInfo, DisplayLLVMIR | Verbose);
	Gen.GenGlobalInitFunc();
	Gen.GenGlobalDestroyFunc();

	if (EmitDebugInfo) {
		Context.LLJuneModule.addModuleFlag(llvm::Module::Warning, "CodeView", 1);
		Context.LLJuneModule.addModuleFlag(llvm::Module::Warning, "Debug Info Version", llvm::DEBUG_METADATA_VERSION);
		llvm::NamedMDNode* LLVMIdentMD = Context.LLJuneModule.getOrInsertNamedMetadata("llvm.ident");
		LLVMIdentMD->addOperand(llvm::MDNode::get(Context.LLContext, { llvm::MDString::get(Context.LLContext, "June Compiler") }));
	}
	
	// Finalizing all the debug compilation units.
	if (EmitDebugInfo) {
		for (auto FUItr = Context.FileUnits.begin(),
			FUEnd = Context.FileUnits.end();
			FUItr != FUEnd; FUItr++
			) {
			FUItr->second->DIEmitter->Finalize();
		}
	}

	// -- DEBUG
	// llvm::verifyModule(Context.LLJuneModule);

	if (Verbose) {
		// TODO: Not found on linux? Context.LLJuneModule.dump();
	}
	
	u64 ParsedIn = (GetTimeInMilliseconds() - ParseTimeBegin);

	// Emitting code
	u64 EmiteMachineCodeTimeBegin = GetTimeInMilliseconds();

	std::string ObjFileName = OutputName + ".o";

	if (!WriteObjFile(ObjFileName.c_str(), Context.LLJuneModule, LLMachineTarget)) {
		FoundCompileError = true;
		return;
	}

	u64 EmiteMachineCodeTime = (GetTimeInMilliseconds() - EmiteMachineCodeTimeBegin);

	u64 LinkTimeStart = GetTimeInMilliseconds();
	
	// Linking the program
	std::string Libs = "";
	for (const c8* Lib : Libraries) {
		Libs += std::string("-l") + std::string(Lib) + " ";
	}
	std::string LibPaths = "";
	for (const c8* LibPath : LibarySearchPaths) {
		Libs += std::string("-L") + std::string(LibPath) + " ";
	}

#ifdef _WIN32
	OutputName += ".exe";
#endif

	std::string ClangCommand = "clang ";
	if (EmitDebugInfo)
		ClangCommand += " -g ";
	ClangCommand += LibPaths + Libs + ObjFileName;
	ClangCommand += " -o ";
	ClangCommand += OutputName;
	//ClangCommand += " -Xlinker /SUBSYSTEM:CONSOLE";

	llvm::outs() << ClangCommand << "\n";
	system(ClangCommand.c_str());

	u32 LinkedIn = (GetTimeInMilliseconds() - LinkTimeStart);

	if (DisplayTimes) {
		std::cout << "\n";
		std::cout << "Total Lines Parsed: " << TotalLinesParsed << '\n';
		std::cout << '\n';
		std::cout << "Parsed/IRGen Time: " << std::fixed << std::setprecision(4) << (ParsedIn / 1000.0) << " seconds." << '\n';
		std::cout << "Code Emit Time:    " << std::fixed << std::setprecision(4) << (EmiteMachineCodeTime / 1000.0) << " seconds." << '\n';
		std::cout << "Link Time:         " << std::fixed << std::setprecision(4) << (LinkedIn / 1000.0) << " seconds." << '\n';
		std::cout << "----------------------------------" << '\n';
		u32 TotalTime = ParsedIn + EmiteMachineCodeTime + LinkedIn;
		std::cout << "Total time:        " << std::fixed << std::setprecision(4) << (TotalTime / 1000.0) << " seconds." << '\n';
		std::cout << '\n';
	}


	llvm::outs() << "Wrote program to: "
		         << std::filesystem::absolute(std::filesystem::current_path()).generic_string().c_str()
		         << '/' << OutputName << '\n';
	
	if (RunProgram) {
#ifdef OS_WINDOWS
		system(OutputName.c_str());
#elif defined(__unix__)
		std::string RunProgramCmd = "./" + OutputName;
		system(RunProgramCmd.c_str());
#endif
	}
}

void june::Compiler::CollectDirectoryFiles(const std::filesystem::path& DirectoryPath, u64 PrimaryPathLen) {
	namespace fs = std::filesystem;
	for (const auto& entry : fs::directory_iterator(DirectoryPath)) {
		if (entry.is_regular_file()) {
			const std::string& path = entry.path().generic_string();
			if (path.substr(path.find_last_of('.') + 1) == "june") {
				
				const std::string& RelativePath = path.substr(PrimaryPathLen);
				const std::string& AbsolutePath = fs::absolute(entry.path()).generic_string();

				AddFileUnit(RelativePath, AbsolutePath);

			}
		} else if (entry.is_directory()) {
			CollectDirectoryFiles(entry.path(), PrimaryPathLen);
		}
	}
}

void june::Compiler::AddFileUnit(const std::string& RelativePath, const std::string& AbsolutePath) {
	
	FileUnit* FU = new FileUnit(llvm::errs(), RelativePath);
	if (EmitDebugInfo) {
		FU->DIEmitter = new DebugInfoEmitter(Context);
	}

	std::string& PathKey = FU->FL.PathKey;
	PathKey = std::move(RelativePath.substr(0, RelativePath.size() - 5));
	std::replace(PathKey.begin(), PathKey.end(), '/', '.');
	FU->FL.FullPath = AbsolutePath;

	if (Verbose) {
		Logger::CompileInfo(llvm::outs(),
			"FileUnit Paths: { key=\"%s\", full-path=\"%s\" }",
			FU->FL.PathKey, FU->FL.FullPath);
	}

	if (!StandAlone) {
		// TODO: make more efficient
		if (FU->FL.PathKey == "std.lang.String") {
			Context.StringFU = FU;
		} else if (FU->FL.PathKey == "std.Sys") {
			Context.SysFU = FU;
		}
	}

	if (FilesNeedingParsing.find(FU->FL.PathKey) != FilesNeedingParsing.end()) {
		Logger::GlobalError(llvm::errs(), "Duplicate path-key found: %s", FU->FL.PathKey);
	}
	FilesNeedingParsing.insert({ FU->FL.PathKey, FU });
	Context.FileUnits.insert({ FU->FL.PathKey, FU });
}

void june::Compiler::ParseNextFiles() {
	auto it = FilesNeedingParsing.begin();
	ParseFiles(it->second);
}

void june::Compiler::ParseFiles(FileUnit* FU) {
	if (FU->HasBeenParsed) return;
	FU->HasBeenParsed = true;

	FilesNeedingParsing.erase(FU->FL.PathKey);

	if (Verbose) {
		Logger::CompileInfo(llvm::outs(), "Parsing file: %s", FU->FL.FullPath);
	}

	if (!ReadFile(FU->FL.FullPath, FU->SBuf.Memory, FU->SBuf.Length)) {
		Logger::GlobalError(llvm::errs(), "Failed to read file: %s", FU->FL.FullPath);
		return;
	}

	Parser P(Context, FU, FU->Log);
	P.Parse();

	TotalLinesParsed += P.GetLinesParsed();

	// Parsing dependencies
	for (auto [PathKey, DepFU] : FU->Imports) {
		ParseFiles(DepFU);
		if (DepFU->Log.HasError) {
			FU->Log.HasError = true;
		}
	}
	for (FileUnit* DepFU : FU->GlobalUsingImports) {
		ParseFiles(DepFU);
		if (DepFU->Log.HasError) {
			FU->Log.HasError = true;
		}
	}

	if (FU->Log.HasError) {
		FoundCompileError = true;
		return;
	}

	Analysis::ReportInvalidFUStmts(FU);
	Analysis::ResolveRecordTypes(Context, FU);
	if (FU->Log.HasError) {
		FoundCompileError = true;
		return;
	}

	Analysis::CheckRecords(Context, FU);

	if (FU->Log.HasError) {
		FoundCompileError = true;
		return;
	}

	if (DisplayAST | Verbose) {
		PrintFileUnit(Context, FU);
		llvm::outs() << "\n\n";
	}
}

const c8* june::Compiler::GetStdLibPath() {
	if (PathToStandardLibrary) {
		return PathToStandardLibrary;
	} else {
		return std::getenv("JuneStdLibPath");
	}
}

