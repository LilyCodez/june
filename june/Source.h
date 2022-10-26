#ifndef JUNE_SOURCE_H
#define JUNE_SOURCE_H

#include <llvm/ADT/StringRef.h>

#include "Prolog.h"
#include <string>

namespace june {
	struct SourceBuf {
		c8* Memory;
		u64 Length;
	};

	struct SourceLoc {
		llvm::StringRef Text;
		u32             LineNumber;
	};

	// Is the character a base-10 digit
	inline bool IsDigit(c8 C) { return C >= '0' && C <= '9'; }

	// Is the character an alphanumeric character
	inline bool IsAlpha(c8 C) {
		return ('a' <= C && C <= 'z') || ('A' <= C && C <= 'Z');
	}

	struct HexLUT {
		bool LUT[256];
		constexpr HexLUT();

		constexpr bool operator[](u64 i) { return LUT[i]; }
	};

	extern HexLUT HEX_LUT;

	inline bool IsHex(c8 C) {
		return HEX_LUT[C];
	}

	struct FileLocation {
		// Full path on the symstem.
		std::string FullPath;
		// The path relative to the source directory
		// and is what is used by the client to
		// import files.
		//
		// Pattern: (ident '.')* ident
		std::string PathKey;
		// The path used for displaying error messages.
		std::string ErrorPathKey;
	};
}

#endif // JUNE_SOURCE_H