#ifndef JUNE_COMPILER_H
#define JUNE_COMPILER_H

#include "Prolog.h"

#include <llvm/ADT/SmallVector.h>
#include <filesystem>
#include <llvm/ADT/StringMap.h>

namespace june {

	struct FileUnit;
	class JuneContext;

	class Compiler {
	public:
		bool FoundCompileError = false;
		bool Verbose           = false;
		bool DisplayLLVMIR     = false;
		bool DisplayAST        = false;
		bool DisplayTimes      = false;
		// When true, it does not compile with
		// the standard library.
		bool StandAlone        = false;
		bool EmitDebugInfo     = false;
		bool RunProgram        = false;
		const c8* PathToStandardLibrary = nullptr;
		
		Compiler();
		
		~Compiler();

		void Compile(llvm::SmallVector<const c8*, 1>& SourceDirectories);

		void AddLib(const c8* LibName) { Libraries.push_back(LibName); }
		void AddLibPath(const c8* LibPath) { LibarySearchPaths.push_back(LibPath); }

		void SetOutputName(const std::string& Name) { OutputName = Name; }

	private:
		llvm::StringMap<FileUnit*> FilesNeedingParsing;
		JuneContext&               Context;
		u32                        TotalLinesParsed = 0;
		
		
		std::string OutputName = "program";

		llvm::SmallVector<const c8*, 8> Libraries;
		llvm::SmallVector<const c8*, 8> LibarySearchPaths;

		void CollectDirectoryFiles(const std::filesystem::path& DirectoryPath, u64 PrimaryPathLen);
		void AddFileUnit(const std::string& RelativePath, const std::string& AbsolutePath);

		void ParseNextFiles();

		void ParseFiles(FileUnit* FU);

		const c8* GetStdLibPath();

	};
}

#endif // JUNE_COMPILER_H
