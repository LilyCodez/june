#include "Logger.h"

#include "Util.h"

constexpr u32 TOTAL_ALLOWED_ERRORS = 100;
u32 june::TOTAL_ACC_ERRORS = 0;

std::string ReplaceTabsWithSpaces(llvm::StringRef sr) {
	std::string s = sr.str();
	std::string NoTabs;
	for (c8& c : s) {
		if (c != '\t') {
			NoTabs += c;
		} else {
			NoTabs += "    ";
		}
	}
	return NoTabs;
}

june::Logger::Logger(const SourceBuf& buf, llvm::raw_ostream& os, const std::string& filePath)
	: Buf(buf), OS(os), FilePath(filePath) {
}

void june::Logger::Error(SourceLoc Loc, const std::function<void()>& Printer) {

	// Forward error message

	std::string LineNumber = std::to_string(Loc.LineNumber);
	u32 ColumnNumber = 0;
	const c8* MemPtr = Loc.Text.begin();
	while (*MemPtr != '\n' && MemPtr != Buf.Memory) {
		--MemPtr;
		++ColumnNumber;
	}
	if (ColumnNumber > 0)
		--ColumnNumber;

	OS << FilePath.c_str();
	OS << ":" << LineNumber << ":" << std::to_string(ColumnNumber) << ":";
	SetTerminalColor(TerminalColorRed);
	OS << " Error: ";
	SetTerminalColor(TerminalColorDefault);

	// Printing the message
	Printer();
	OS << '.';

	LNPad = std::string(LineNumber.size(), ' ');

	// Displaying where the error occured
	OS << "\n";
	OS << LNPad << "  |\n";
	OS << LNPad << "  |\n";
	std::string Between   = ReplaceTabsWithSpaces(Loc.Text);
	std::string Backwards = ReplaceTabsWithSpaces(RangeFromWindow(Loc.Text.begin(), -40));
	std::string Forwards  = ReplaceTabsWithSpaces(RangeFromWindow(Loc.Text.begin() + Loc.Text.size() - 1, +40));
	
	if (Between == "\n") {
		Between = "";
	}

	assert(Between.find('\n', 0)   == std::string::npos && "New Line in display!");
	assert(Backwards.find('\n', 0) == std::string::npos && "New Line in display!");
	assert(Forwards.find('\n', 0)  == std::string::npos && "New Line in display!");

	OS << ' ' << LineNumber << " | ";
	OS << Backwards << Between << Forwards << '\n';

	std::string spaces = std::string(Backwards.size(), ' ');
	//      | ~~~
	OS << LNPad << "  | ";
	SetTerminalColor(TerminalColorRed);
	OS << spaces << std::string(Between.size(), '~') << '\n';
	SetTerminalColor(TerminalColorDefault);

	//      | ^
	OS << LNPad << "  | ";
	SetTerminalColor(TerminalColorRed);
	OS << spaces << "^" << '\n';
	SetTerminalColor(TerminalColorDefault);

	OS << '\n';

	HasError = true;

	++TOTAL_ACC_ERRORS;
	++NumErrors;
	if (TOTAL_ACC_ERRORS == TOTAL_ALLOWED_ERRORS) {
		SetTerminalColor(TerminalColorLightBlue);
		OS << ">>";
		SetTerminalColor(TerminalColorDefault);
		OS << " Exceeded the maximum allowed error messages. Exiting.\n";
		exit(1);
	}
}

void june::Logger::GlobalError(llvm::raw_ostream& OS, const std::function<void()>& Printer) {
	// Forward error message
	SetTerminalColor(TerminalColorRed);
	OS << "Error: ";
	SetTerminalColor(TerminalColorDefault);

	// Printing the message
	Printer();

	OS << '\n';
}

june::Logger& june::Logger::Note(const std::function<void()>& Printer) {
	SetTerminalColor(TerminalColorYellow);
	OS << LNPad << "  Note: ";
	SetTerminalColor(TerminalColorDefault);
	Printer();
	OS << '\n';
	return *this;
}

june::Logger& june::Logger::NoteLn(const std::function<void()>& Printer) {
	OS << LNPad << "         ";
	Printer();
	OS << '\n';
	return *this;
}

void june::Logger::EndNote() {
	OS << '\n';
	SetTerminalColor(TerminalColorDefault);
}

void june::Logger::CompileInfo(llvm::raw_ostream& OS, const std::function<void()>& Printer) {
	llvm::outs() << " -- ";
	Printer();
	llvm::outs() << '\n';
}

llvm::StringRef june::Logger::RangeFromWindow(const c8* Loc, s32 Direction) {
	const c8* MemPtr = Loc; // Pointing to character start.
	s32 Moved = 0;
	while (true) {
		if (*MemPtr == '\n') {
			// Pointer is at a new line.
			if (Direction < 0) ++MemPtr; // Moving in the negative direction so move forward one
			else               --MemPtr; // Moving in the forward direction so move backwards one
			break; // New line so end loop.
		} else if (*MemPtr == '\r' && Direction > 0) {

			// Direction > 0 because running into \r in while
			// moving backwards would mean it is a random \r
			// in the file not a new line.
			if (*(MemPtr + 1) == '\n') {
				--MemPtr;
				break;
			} // else \r in middle of memory for some reason
		}

		++Moved;
	
		if (MemPtr == Buf.Memory || MemPtr == Buf.Memory + Buf.Length - 1) {
			// Hit one end of the buffer so there is nothing more to do
			break;
		}

		if (Moved == abs(Direction)) {
			// Moved enough.
			break;
		}

		// Move to the next character
		if (Direction < 0) --MemPtr;
		else               ++MemPtr;
	}
	
	if (Moved == 0) return llvm::StringRef("");
	if (Direction < 0) {
		//    abcd
		//    ^ <-- moved 3 but length is 4
		return llvm::StringRef(MemPtr, Moved-1);
	} else {
		return llvm::StringRef(Loc+1, Moved-1);
	}
}