#ifndef JUNE_LEXER_H
#define JUNE_LEXER_H

#include "Tokens.h"
#include "Logger.h"

#include <stack>

namespace june {

	class JuneContext;

	class Lexer {
	public:

		explicit Lexer(const JuneContext& context, const SourceBuf& buf, Logger& log);


		// Retrieves the next token in the
		// buffer ignoring comments and white space.
		Token NextToken();

		u32 GetLinesLexed() const { return LineNumber; }

	private:
		const c8*          CurPtr;
		const JuneContext& Context;
		u32                LineNumber = 1;
		const SourceBuf&   Buf;
		Logger&            Log;

		std::stack<u32> EncounteredIfPreprocessorStack;

		// Continues eating characters until a new line.
		void EatTillEndOfLine();
		void EatLine();

		void EatWhitespaceOrComments();

		// Comments of the form:
		// '/* This may span
		//     multiple lines
		//  */'
		void SkipMultilineComment();

		// Next token is either a keyword
		// or an identifier.
		// 
		// [a-zA-Z][a-zA-Z0-9_]*
		Token NextWord();

		// Next token is a number.
		Token NextNumber();
		Token FinishInt(const c8* TokStart, u16 Kind);

		// String literals
		Token NextString();

		// Char literals
		Token NextChar();

		void HandlePredirectiveStart();
		llvm::StringRef GetPredirective();
		void HandlePredirectiveIf();
		bool ParsePredirectiveCond();
		void FinishPredirective();
		void SkipFalsePredirectiveIf(u32 StartStackSize);

		inline Token CreateTokenAndEat(u16 Kind, const c8* TokStart) {
			++CurPtr;
			return CreateToken(Kind, TokStart);
		}

		inline Token CreateToken(u16 Kind, const c8* TokStart) const {
			return Token(Kind, SourceLoc{ MakeText(TokStart), LineNumber });
		}

		inline Token CreateToken(u16 Kind, llvm::StringRef Text) const {
			return Token(Kind, SourceLoc{ Text, LineNumber });
		}

		inline llvm::StringRef MakeText(const c8* TokStart) const {
			return llvm::StringRef(TokStart, CurPtr - TokStart);
		}

		void Error(const c8* CharPos, const c8* Msg) {
			Log.Error(SourceLoc{ llvm::StringRef(CharPos, 1), LineNumber }, Msg);
		}

		template<typename... Targs>
		void Error(const c8* CharPos, const c8* Fmt, Targs&&... Args) {
			Log.Error(SourceLoc{ llvm::StringRef(CharPos, 1), LineNumber },
				Fmt, std::forward<Targs>(Args)...);
		}
	};
}

#endif // JUNE_LEXER_H