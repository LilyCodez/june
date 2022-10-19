#ifndef JUNE_TOKENS_H
#define JUNE_TOKENS_H

#include "Source.h"

#include <llvm/ADT/StringRef.h>
#include <string>

namespace june {

	class JuneContext;

	enum TokenKind {
		
		/* Ascii Characters reserved < 257 */

		// === Keywords === \\

		__TK_KEYWORD_START__ = 257,

		// Types

			KW_TYPE_I8,
			KW_TYPE_I16,
			KW_TYPE_I32,
			KW_TYPE_I64,
			KW_TYPE_U8,
			KW_TYPE_U16,
			KW_TYPE_U32,
			KW_TYPE_U64,
			KW_TYPE_OSINT,
			KW_TYPE_OSUINT,
			KW_TYPE_C8,
			KW_TYPE_C16,
			KW_TYPE_C32,
			KW_TYPE_F32,
			KW_TYPE_F64,
			KW_TYPE_BOOL,
			KW_TYPE_VOID,

		// Control Flow

			KW_RETURN,
			KW_LOOP,
			KW_IF,
			KW_ELSE,
			KW_CONTINUE,
			KW_BREAK,

		// Other
			
			KW_IN,
			KW_THIS,
			KW_NEW,
			KW_CAST,
			KW_SIZEOF,
			KW_RECORD,
			KW_TRUE,
			KW_FALSE,
			KW_IMPORT,
			KW_NULL,
			KW_COMPTIME,
			KW_NATIVE,


		__TK_KEYWORD_END__ = KW_NATIVE,

		// === Symbols === \\

		PLUS_PLUS,   // ++
		MINUS_MINUS, // --
		// Not really a token but used for
		// distingishing between post/pre
		// ++, --
		POST_PLUS_PLUS,
		POST_MINUS_MINUS,

		PLUS_EQ,     // +=
		MINUS_EQ,    // -=
		SLASH_EQ,    // /=
		STAR_EQ,     // *=
		MOD_EQ,      // %=
		AMP_EQ,      // &=
		BAR_EQ,      // |=
		CRT_EQ,      // ^=
		LT_LT,       // <<
		GT_GT,       // >>
		LT_LT_EQ,    // <<=
		GT_GT_EQ,    // >>=
		LT_EQ,       // <=
		GT_EQ,       // >=
		AMP_AMP,     // &&
		BAR_BAR,     // ||
		EQ_EQ,       // ==
		EXL_EQ,      // !=
		COL_COL,     // ::
		MINUS_GT,    // ->
		BAR_GT,      // |>

		// === Extra === \\

		IDENT,
		INT_LITERAL,
		HEX_LITERAL,
		BIN_LITERAL,
		FLOAT_LITERAL,
		STRING_LITERAL,
		CHAR_LITERAL,

		// End of File
		TK_EOF,

	};

	std::string GetTokenKindPresentation(u16 Kind, const JuneContext& Context);

	// Basic lexical presentation of
	// a range of text within a file.
	struct Token {
		// Value that represents a TokenKind.
		// Tells the sort of token this token is.
		// 
		// Stored as an integer to allow for character
		// comparisons.
		u32 Kind;

		// Location information. Also contains
		// the text for the given location.
		SourceLoc Loc;
	
		Token() : Kind(0) {}

		Token(u16 kind, SourceLoc loc)
			: Kind(kind), Loc(loc) {}

		llvm::StringRef GetText() const { return Loc.Text; }

		// Checks if the token is of the given kind.
		bool is(u16 kind) const { return Kind == kind; }

		// Checks if the token is not of the given kind.
		bool isNot(u16 kind) const { return Kind != kind; }

		// Retrieves a lexical presentation of the form
		// (kind, text).
		std::string GetLexicalPresentation(const JuneContext& Context);

	};
}

#endif // JUNE_TOKENS_H