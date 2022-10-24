#include "Logger.h"

#include "Util.h"

#include <sstream>

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

	u32 LineNumber = Loc.LineNumber;
	u32 ColumnNumber = 0;
	const c8* MemPtr = Loc.Text.begin();
	while (*MemPtr != '\n' && MemPtr != Buf.Memory) {
		--MemPtr;
		++ColumnNumber;
	}
	if (ColumnNumber > 0)
		--ColumnNumber;

	std::string Between   = ReplaceTabsWithSpaces(Loc.Text);
	std::string Backwards = ReplaceTabsWithSpaces(RangeFromWindow(Loc.Text.begin(), -40));
	std::string Forwards  = ReplaceTabsWithSpaces(RangeFromWindow(Loc.Text.begin() + Loc.Text.size() - 1, +40));

	if (Between == "\n") {
		Between = "";
	}

	bool BetweenTooBig = false;
	if (Between.size() > 100) {
		Between = Between.substr(0, 100);
		if (Between[Between.size() - 1] == '\n' || Between[Between.size() - 1] == '\r') {
			Between = Between.substr(Between.size() - 1);
		} else if (Between[Between.size() - 2] == '\r') {
			Between = Between.substr(Between.size() - 2);
		}
		BetweenTooBig = true;
	}

	assert(Backwards.find('\n', 0) == std::string::npos && "New Line in display!");
	assert(Forwards.find('\n', 0) == std::string::npos && "New Line in display!");

	std::string BetweenLine;
	std::vector<std::string> BetweenLines;
	const c8* BPtr = Between.c_str();
	while (*BPtr) {
		if (*BPtr == '\n') {
			BetweenLines.push_back(BetweenLine);
			BetweenLine = "";
		} else if (*BPtr == '\r') {			
			BetweenLines.push_back(BetweenLine);
			BetweenLine = "";
			if (*(BPtr+1) == '\n') {
				++BPtr;
			}
		} else {
			BetweenLine.push_back(*BPtr);
		}
		++BPtr;
	}
	if (!BetweenLine.empty())
		BetweenLines.push_back(BetweenLine);

	OS << FilePath.c_str();
	OS << ":" << LineNumber << ":" << ColumnNumber << ":";
	SetTerminalColor(TerminalColorRed);
	OS << " Error: ";
	SetTerminalColor(TerminalColorDefault);

	// Printing the message
	Printer();
	OS << '.';

	u32 LargestLineNum = LineNumber + BetweenLines.size() - 1;
	LNPad = std::string(std::to_string(LargestLineNum).size(), ' ');

	// Displaying where the error occured
	OS << "\n";
	OS << LNPad << "  |\n";

	std::string spaces = std::string(Backwards.size(), ' ');

	u32 LargestRedUnderscore = 0;
	for (const std::string& BetweenLine : BetweenLines) {
		if (BetweenLine.size() > LargestRedUnderscore) {
			LargestRedUnderscore = BetweenLine.size();
		}
	}

	for (u32 i = 0; i < BetweenLines.size(); i++) {
		const std::string& BetweenLine = BetweenLines[i];
		bool IsLast = i + 1 == BetweenLines.size();

		auto FirstNonSpaceIt = BetweenLine.find_first_not_of(' ');
		if (FirstNonSpaceIt != std::string::npos) {
			OS << ' ' << (LineNumber + i);
			OS << std::string(std::to_string(LargestLineNum).size() - std::to_string(LineNumber + i).size(), ' ');
			OS << " | ";
			if (i == 0)
				OS << Backwards;
		} else {
			OS << LNPad << "  | ";
			SetTerminalColor(TerminalColorRed);
			OS << std::string(LargestRedUnderscore + 1 + 3 + Backwards.size(), ' ');
			OS << "|";
			if (i == 1) {
				OS << " New Lines";
			}
			SetTerminalColor(TerminalColorDefault);
			OS << '\n';
			continue;
		}

		std::string NonTrailingWhitespaceStr = BetweenLine.substr(FirstNonSpaceIt);

		OS << BetweenLine;
		if (BetweenTooBig && IsLast) {
			SetTerminalColor(TerminalColorLightBlue);
			OS << " ... ";
			SetTerminalColor(TerminalColorDefault);
		}

		if (BetweenLines.size() == 1) {
			OS << Forwards;
		}

		SetTerminalColor(TerminalColorRed);
		if (i != 0) {
			u32 Indent = LargestRedUnderscore - BetweenLine.size() + Backwards.size();
			if (BetweenTooBig && IsLast) {
				Indent -= 5;
			}
			OS << std::string(Indent, ' ');
			OS << "    |";
			if (i == 1) {
				OS << " New Lines";
			}
		}
		SetTerminalColor(TerminalColorDefault);
		OS << '\n';
		
		//      | ~~~
		OS << LNPad << "  | ";
		SetTerminalColor(TerminalColorRed);
		if (i == 0) {
			OS << spaces;
		}
		OS << std::string(BetweenLine.size() - NonTrailingWhitespaceStr.size(), ' ')
		   << std::string(NonTrailingWhitespaceStr.size(), '~');
		if (BetweenLines.size() > 1) {
			if (i == 0 || IsLast) {
				OS << ' ';
				if (i != 0) {
					OS << std::string(LargestRedUnderscore - BetweenLine.size() + Backwards.size(), '-');
				} else {
					OS << std::string(LargestRedUnderscore - BetweenLine.size(), '-');
				}
				OS << "---";
			} else {
				OS << std::string(LargestRedUnderscore - BetweenLine.size() + 1 + 3 + Backwards.size(), ' ');
			}
			
			if (IsLast) {
				OS << '/';
			} else if (i != 0) {
				OS << '|';
			} else {
				OS << "\\";
			}
		}
		
		OS << '\n';
		SetTerminalColor(TerminalColorDefault);
		
	}

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
	OS << LNPad << "        ";
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