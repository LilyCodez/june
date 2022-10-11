#include "Lexer.h"

#include "JuneContext.h"

june::Lexer::Lexer(const JuneContext& context, const SourceBuf& buf, Logger& log)
	: Context(context), Buf(buf), CurPtr(buf.Memory), Log(log) {
}

june::Token june::Lexer::NextToken() {

	// When skipping tokens this jumps back
	// to the start to try again
restartLex:

	// Start of the token in the text
	const c8* TokStart = CurPtr;

	switch (*CurPtr++) {
	// Whitespace
	case ' ':
	case '\t':
	case '\v':
	case '\f':
		goto restartLex;
	case '\n':
		++LineNumber;
		goto restartLex;
	case '\r':
		if (*CurPtr == '\n') {
			++LineNumber;
			++CurPtr;
		}
		goto restartLex;
	case '0': case '1': case '2': case '3': case '4':
	case '5': case '6': case '7': case '8': case '9':
		return NextNumber();
	case 'a': case 'b': case 'c': case 'd': case 'e':
	case 'f': case 'g': case 'h': case 'i': case 'j':
	case 'k': case 'l': case 'm': case 'n': case 'o':
	case 'p': case 'q': case 'r': case 's': case 't':
	case 'u': case 'v': case 'w': case 'x': case 'y':
	case 'z':
	case 'A': case 'B': case 'C': case 'D': case 'E':
	case 'F': case 'G': case 'H': case 'I': case 'J':
	case 'K': case 'L': case 'M': case 'N': case 'O':
	case 'P': case 'Q': case 'R': case 'S': case 'T':
	case 'U': case 'V': case 'W': case 'X': case 'Y':
	case 'Z':
	case '_': // Have to support it for library dependencies
		return NextWord();
	case '"':
		return NextString();
	case '\'':
		return NextChar();
	case '{': return CreateToken('{', TokStart);
	case '}': return CreateToken('}', TokStart);
	case '[': return CreateToken('[', TokStart);
	case ']': return CreateToken(']', TokStart);
	case '(': return CreateToken('(', TokStart);
	case ')': return CreateToken(')', TokStart);
	case ',': return CreateToken(',', TokStart);
	case '.': return CreateToken('.', TokStart);
	case ':':
		if (*CurPtr == ':') return CreateTokenAndEat(TokenKind::COL_COL, TokStart);
		else                return CreateToken(':', TokStart);
	case ';': return CreateToken(';', TokStart);
	case '+':
		if (*CurPtr == '+')      return CreateTokenAndEat(TokenKind::PLUS_PLUS, TokStart);
		else if (*CurPtr == '=') return CreateTokenAndEat(TokenKind::PLUS_EQ, TokStart);
		else                     return CreateToken('+', TokStart);
	case '-':
		if (*CurPtr == '-')      return CreateTokenAndEat(TokenKind::MINUS_MINUS, TokStart);
		else if (*CurPtr == '>') return CreateTokenAndEat(TokenKind::MINUS_GT, TokStart);
		else if (*CurPtr == '=') return CreateTokenAndEat(TokenKind::MINUS_EQ, TokStart);
		else                     return CreateToken('-', TokStart);
	case '*':
		if (*CurPtr == '=') return CreateTokenAndEat(TokenKind::STAR_EQ, TokStart);
		else                return CreateToken('*', TokStart);
	case '%':
		if (*CurPtr == '=') return CreateTokenAndEat(TokenKind::MOD_EQ, TokStart);
		else                return CreateToken('%', TokStart);
	case '^':
		if (*CurPtr == '=') return CreateTokenAndEat(TokenKind::CRT_EQ, TokStart);
		else                return CreateToken('^', TokStart);
	case '|':
		if (*CurPtr == '=')      return CreateTokenAndEat(TokenKind::BAR_EQ, TokStart);
		else if (*CurPtr == '|') return CreateTokenAndEat(TokenKind::BAR_BAR, TokStart);
		else                     return CreateToken('|', TokStart);
	case '&':
		if (*CurPtr == '=')      return CreateTokenAndEat(TokenKind::AMP_EQ, TokStart);
		else if (*CurPtr == '&') return CreateTokenAndEat(TokenKind::AMP_AMP, TokStart);
		else                     return CreateToken('&', TokStart);
	case '<':
		if (*CurPtr == '<') {
			++CurPtr;
			if (*CurPtr == '=') return CreateTokenAndEat(TokenKind::LT_LT_EQ, TokStart);
			else                return CreateToken(TokenKind::LT_LT, TokStart);
		} else if (*CurPtr == '=') return CreateTokenAndEat(TokenKind::LT_EQ, TokStart);
		else                       return CreateToken('<', TokStart);
	case '>':
		if (*CurPtr == '>') {
			++CurPtr;
			if (*CurPtr == '=') return CreateTokenAndEat(TokenKind::GT_GT_EQ, TokStart);
			else                return CreateToken(TokenKind::GT_GT, TokStart);
		} else if (*CurPtr == '=') return CreateTokenAndEat(TokenKind::GT_EQ, TokStart);
		else return CreateToken('>', TokStart);
	case '=':
		if (*CurPtr == '=') return CreateTokenAndEat(TokenKind::EQ_EQ, TokStart);
		else                return CreateToken('=', TokStart);
	case '!':
		if (*CurPtr == '=') return CreateTokenAndEat(TokenKind::EXL_EQ, TokStart);
		else                return CreateToken('!', TokStart);
	case '/':
		if (*CurPtr == '/') {
			SkipSlashSlashComment();
			goto restartLex;
		} else if (*CurPtr == '*') {
			SkipMultilineComment();
			goto restartLex;
		} else if (*CurPtr == '=') return CreateTokenAndEat(TokenKind::SLASH_EQ, TokStart);	
		else                       return CreateToken('/', TokStart);
	// End of file.
	case 0:
		
		if (TokStart != Buf.Memory + Buf.Length) {
			Error(CurPtr - 1, "Null character found in middle of file");
			goto restartLex;
		}

		--CurPtr; // In case the token is requested more than once.
		return CreateToken(TokenKind::TK_EOF, TokStart);
	default:
		Error(CurPtr - 1, "Unknown character: '%s'", llvm::StringRef(CurPtr - 1, 1).str());
		goto restartLex;
	}
}

void june::Lexer::SkipSlashSlashComment() {
	// Keeps eating characters until the new line
	while (true) {
		switch (*CurPtr) {
		case '\n':
			return;
		case '\r':
			if (*(CurPtr + 1) == '\n')
				return;
			++CurPtr; // TODO: Report that there is a \r in the middle of a comment?
			break;
		case '\0':
			return; // EOF
		default:
			// Just advance
			++CurPtr;
			break;
		}
	}
}

void june::Lexer::SkipMultilineComment() {
	++CurPtr; // Consuming '*' character
	while (true) {
		switch (*CurPtr) {
		case '\0': {
			// TODO: report error about an unclosed comment
			return;
		case '\n':
			++LineNumber;
			++CurPtr;
			break;
		case '\r':
			if (*(++CurPtr) == '\n') {
				++LineNumber;
				++CurPtr;
			}
			break;
		case '*':
			if (*(++CurPtr) == '/') {
				++CurPtr; // Eating '/' character
				// End of multiline comment
				return;
			}
			break;
		default:
			// Just advance
			++CurPtr;
			break;
		}
		}
	}
}

june::Token june::Lexer::NextWord() {
	const c8* TokStart = CurPtr - 1;

	while (IsAlpha(*CurPtr) || IsDigit(*CurPtr) || *CurPtr == '_')
		++CurPtr;

	llvm::StringRef Text = MakeText(TokStart);
	if (u16 KwKind = Context.GetKeywordKind(Text))
		return CreateToken(KwKind, Text);

	return CreateToken(TokenKind::IDENT, Text);
}

june::Token june::Lexer::NextNumber() {
	const c8* TokStart = CurPtr - 1;
	assert(IsDigit(*TokStart) && "Numbers must begin with a digit");

	if (*TokStart == '0') {
		if (*CurPtr == 'x') {
			++CurPtr; // Eating 'x'
			while (IsHex(*CurPtr) || *CurPtr == '\'') {
				++CurPtr;
			}
			return FinishInt(TokStart, TokenKind::HEX_LITERAL);
		} else if (*CurPtr == 'b') {
			++CurPtr; // Eating 'b'
			while (*CurPtr == '0' || *CurPtr == '1' || *CurPtr == '\'') {
				++CurPtr;
			}
			return FinishInt(TokStart, TokenKind::BIN_LITERAL);
		}
	}

	// Leading whole digits [0-9]+
	while (IsDigit(*CurPtr) || *CurPtr == '\'')
		++CurPtr;

	bool isFloating = false;
	if (*CurPtr == '.' || *CurPtr == 'E') {
		// Floating
		isFloating = true;

		if (*CurPtr == '.') {
			++CurPtr; // Eating '.'
			// Decimal digits [0-9]+
			while (IsDigit(*CurPtr))
				++CurPtr;
		}

		if (*CurPtr == 'E') {
			++CurPtr; // Eating 'E'

			// Possible sign
			if (*CurPtr == '+' || *CurPtr == '-')
				++CurPtr;

			// Eating exponent digits [0-9]+
			while (IsDigit(*CurPtr))
				++CurPtr;
		}
	}

	if (isFloating) {
		if (*CurPtr == 'f') {
			++CurPtr; // Consuming the type sign
		}
		return CreateToken(TokenKind::FLOAT_LITERAL, TokStart);
	} else {
		return FinishInt(TokStart, TokenKind::INT_LITERAL);
	}
}

june::Token june::Lexer::FinishInt(const c8* TokStart, u16 Kind) {
	switch (*CurPtr) {
	case 'B': case 'b':
	case 'S': case 's':
	case 'I': case 'i':
	case 'L': case 'l':
		++CurPtr;
		break;
	case 'u':
		++CurPtr;
		switch (*CurPtr) {
		case 'B': case 'b':
		case 'S': case 's':
		case 'I': case 'i':
		case 'L': case 'l':
			++CurPtr;
			break;
		}
		break;
	}
	return CreateToken(Kind, TokStart);
}

june::Token june::Lexer::NextString() {
	const c8* TokStart = CurPtr - 1;
	while (true) {
		switch (*CurPtr) {
		case '"':
		case 0:    // EOF.
		case '\n':
			goto finishedParsingString;
		case '\r':
			if (*(++CurPtr) == '\n')
				goto finishedParsingString;
			break; // random \r?
		case '\\':
			// TODO:
			// want to check for unicode so the parser can
			// preallocate the correct type of string and then
			// simple parse the characters of that sort.
			if (*(++CurPtr) == '"')
				++CurPtr;
			break;
		default:
			++CurPtr;
			break;
		}
	}
finishedParsingString:

	if (*CurPtr != '"') {
		Error(CurPtr, "Expected closing quotation for string literal");
	} else {
		++CurPtr;
	}

	return CreateToken(TokenKind::STRING_LITERAL, TokStart);
}

june::Token june::Lexer::NextChar() {
	const c8* TokStart = CurPtr - 1;
	if (*CurPtr == '\\') {
		// TODO: Add support for unicode characters
		++CurPtr;
		++CurPtr;
	} else {
		++CurPtr; // Eating the character inside ''
	}

	if (*CurPtr == '\'') {
		++CurPtr; // Eating closing '
	} else {
		Error(CurPtr, "Expected closing quote for character");
	}

	return CreateToken(TokenKind::CHAR_LITERAL, TokStart);
}
