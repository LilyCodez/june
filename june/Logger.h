#ifndef JUNE_LOGGER_H
#define JUNE_LOGGER_H

#include <llvm/ADT/StringRef.h>
#include <llvm/Support/raw_ostream.h>
#include <functional>

#include "Source.h"

namespace llvm {
	class raw_ostream;
}

namespace june {

	extern u32 TOTAL_ACC_ERRORS;

	class Logger {
	public:
		bool HasError = false;
		u32  NumErrors = 0;

		Logger(const SourceBuf& buf, llvm::raw_ostream& os, const std::string& filePath);

		void BeginError(SourceLoc Loc, const c8* Msg) {
			PrimaryErrLoc = Loc;
			InternalErrorHeader(Loc, [&]() { OS << Msg; });
		}

		template<typename... Targs>
		void BeginError(SourceLoc Loc, const c8* Fmt, Targs&&... Args) {
			PrimaryErrLoc = Loc;
			InternalErrorHeader(Loc, [&]() { 
				ForwardFmt(OS, Fmt, std::forward<Targs>(Args)...);
				});
		}

		void AddMarkErrorMsg(SourceLoc Loc, const std::string& Msg);

		void AddMarkErrorMsg(const std::string& FilePath, SourceLoc Loc, const std::string& Msg);

		void EndError();

		static void GlobalError(llvm::raw_ostream& OS, const c8* Msg) {
			GlobalError(OS, [&]() { OS << Msg; });
		}

		template<typename... Targs>
		static void GlobalError(llvm::raw_ostream& OS, const c8* Fmt, Targs&&... Args) {
			GlobalError(OS, [&]() {
				ForwardFmt(OS, Fmt, std::forward<Targs>(Args)...);
				});
		}

		Logger& Note(const c8* Msg) {
			return Note([&]() { OS << Msg; });
		}

		template<typename... Targs>
		Logger& Note(const c8* Fmt, Targs&&... Args) {
			return Note([&]() {
				ForwardFmt(OS, Fmt, std::forward<Targs>(Args)...);
				});
		}

		Logger& NoteLn(const c8* Msg) {
			return NoteLn([&]() { OS << Msg; });
		}

		template<typename... Targs>
		Logger& NoteLn(const c8* Fmt, Targs&&... Args) {
			return NoteLn([&]() {
				ForwardFmt(OS, Fmt, std::forward<Targs>(Args)...);
				});
		}

		void EndNote();

		template<typename... Targs>
		static void CompileInfo(llvm::raw_ostream& OS, const c8* Fmt, Targs&&... Args) {
			CompileInfo(OS, [&]() {
				ForwardFmt(OS, Fmt, std::forward<Targs>(Args)...);
				});
		}

		static void CompileInfo(llvm::raw_ostream& OS, const c8* Msg) {
			CompileInfo(OS, [&]() { OS << Msg; });
		}

	private:
		const SourceBuf&   Buf;
		llvm::raw_ostream& OS;
		const std::string  FilePath;

		std::string        LNPad;
		u32                LargestLineNum = 0;

		struct MarkMsg {
			std::string FilePath;
			SourceLoc   Loc;
			std::string Message;
		};

		SourceLoc PrimaryErrLoc;
		llvm::SmallVector<MarkMsg> MarkMsgs;

		void InternalErrorHeader(SourceLoc Loc, const std::function<void()>& Printer);

		void DisplayMarkError(MarkMsg& Msg);

		void DisplayPrimaryError(const std::vector<std::string>& BetweenLines, bool BetweenTooBig);

		static void GlobalError(llvm::raw_ostream& OS, const std::function<void()>& Printer);

		Logger& Note(const std::function<void()>& Printer);

		Logger& NoteLn(const std::function<void()>& Printer);

		static void CompileInfo(llvm::raw_ostream& OS, const std::function<void()>& Printer);

		template<typename T>
		static void ForwardFmt(llvm::raw_ostream& OS, const c8* Fmt, T&& Val) {
			for (; *Fmt != '\0'; Fmt++) {
				if (*Fmt == '%' && *(Fmt + 1) == 's') {
					OS << std::forward<T>(Val);
					++Fmt;
					continue;
				}
				OS << *Fmt;
			}
		}

		template<typename T, typename... Targs>
		static void ForwardFmt(llvm::raw_ostream& OS, const c8* Fmt, T&& Val, Targs&&... Args) {
			for (; *Fmt != '\0'; Fmt++) {
				if (*Fmt == '%' && *(Fmt + 1) == 's') {
					OS << std::forward<T>(Val);
					ForwardFmt(OS, Fmt + 2, std::forward<Targs>(Args)...);
					return;
				}
				OS << *Fmt;
			}
		}

		llvm::StringRef RangeFromWindow(const c8* Loc, s32 Direction);

	};
}

#endif // JUNE_LOGGER_H