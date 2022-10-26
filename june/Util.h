#ifndef JUNE_UTIL_H
#define JUNE_UTIL_H

#include "Prolog.h"
#include <string>

namespace june {
	
	constexpr u32 TerminalColorDefault   = 0x7;
	constexpr u32 TerminalColorRed       = 0xC;
	constexpr u32 TerminalColorGreen     = 0x2;
	constexpr u32 TerminalColorYellow    = 0x6;
	constexpr u32 TerminalColorLightBlue = 0x9;
	constexpr u32 TerminalColorCyan      = 0xB;

	void SetTerminalColor(u32 ColorId);

	// Get the operating system's running current time
	// in milliseconds (time since epoch)
	u64 GetTimeInMilliseconds();

	bool ReadFile(const std::string& Path, c8*& Buffer, u64& Size);

	std::string FormatDateTime(const c8* Format, u32 TimeStamp);

}

#endif // JUNE_UTIL_H