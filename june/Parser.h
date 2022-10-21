#ifndef JUNE_PARSER_H
#define JUNE_PARSER_H

#include <stack>
#include <queue>
#include <llvm/ADT/SmallVector.h>

#include "Lexer.h"
#include "Ast.h"
#include "Comptime.h"

namespace june {

	class JuneContext;
	struct Type;

	constexpr u32 MAX_ARRAY_NESTING_LEVEL = 8;

	class Parser {
	public:
	
		Parser(JuneContext& context, FileUnit* FU, Logger& log);

		void Parse();

		void PrintTokens();

		u32 GetLinesParsed() const { return L.GetLinesLexed(); }

	private:
		JuneContext& Context;
		Lexer        L;
		Token        CTok;
		Token        PrevToken;
		FileUnit*    FU;
		FuncDecl*    CFunc   = nullptr;
		RecordDecl*  CRecord = nullptr;
		Logger&      Log;

		/*
		 * Used to keep track of variables
		 * within the scope of functions.
		 */
		struct Scope {
			Scope* Parent = nullptr;
			llvm::DenseMap<Identifier, VarDecl*> VarDecls;
			
			// Recursively searches the scope stack for the variable
			// declaration given the name
			VarDecl* FindVariable(Identifier Name);

		} * LocScope = nullptr;

		std::queue<Token> SavedTokens;

		u32 ArrNestingLevel = 0;
		u32 ArrNestingLengths[MAX_ARRAY_NESTING_LEVEL];

		bool ErrorSkipVarDecl = false;

		llvm::StringRef NativeModifierName;

		void ProcessGlobalVar(VarDecl* Global);

		void ParseImport();

		void ParseScopeStmts(LexScope& Scope);

		void ParseOptStmt(AstNode*& Stmt);
		AstNode* ParseStmt();

		FuncDecl* ParseFuncDecl(Token NameTok, mods::Mod Mods, llvm::SmallVector<Identifier>& Generics);
		VarDecl* ParseVarDecl(mods::Mod Mods);
		VarDecl* ParseVarDecl(Token NameTok, mods::Mod Mods, bool ParseTypeInfo = true);
		RecordDecl* ParseRecordDecl(Token NameTok, mods::Mod Mods);
		Identifier ParseIdentifier(const c8* ErrorMessage);
		Identifier ParseIdentifier(Token PossibleIdent, const c8* ErrorMessage);
		mods::Mod ParseModifiers();
		llvm::SmallVector<Identifier> ParseGenerics();

		InnerScopeStmt* ParseInnerScope();
		ReturnStmt* ParseReturn();
		AstNode* ParseLoop();
		RangeLoopStmt* ParseRangeLoop(Token LoopTok);
		IteratorLoopStmt* ParseIteratorLoop(Token LoopTok);
		PredicateLoopStmt* ParsePredicateLoop(Token LoopTok);
		IfStmt* ParseIf();
		LoopControlStmt* ParseLoopControl();

		//===-------------------------------===//
		// Expressions
		//===-------------------------------===//

		Expr* ParseAssignmentAndExprs();
		Expr* ParseExpr();
		Expr* ParsePrimaryAndPostExpr();
		Expr* ParseBinaryOpExpr(Expr* LHS);
		Expr* ParsePrimaryExpr();
		Expr* ParseMemoryRefs(Expr* Site);
		FuncCall* ParseFuncCall(Expr* Site);

		NumberLiteral* ParseIntLiteral();
		NumberLiteral* ParseHexLiteral();
		NumberLiteral* ParseBinLiteral();
		NumberLiteral* FinalizeIntLiteral(u32 Idx, u64 IntValue);
		NumberLiteral* ParseFloatLiteral();
		String8Literal* ParseString8Literal();
		NumberLiteral* ParseCharLiteral();

		Array* ParseArray();
		void SetNestingLevelLengths(Array* Arr, u32 CNestingLevel = 0);
		
		Type* ParseType(bool ReqArrayLengthComptime = true);
		RecordLocation ParseRecordLocation();

		//===-------------------------------===//
		// Utilities
		//===-------------------------------===//

		// Retreives the next Token from either
		// the Lexer or the SavedTokens and
		// stores it in CTok.
		void NextToken();

		// Looks ahead n tokens and saves the tokens 
		// skipped into SavedTokens.
		Token PeekToken(u32 n);

		// if the current token matches the TokenKind
		// then it is consumed, otherwise an error is
		// generated
		void Match(u16 TokenKind, const c8* Purpose = nullptr);

		// Skips tokens until it can find
		// a valid place to start parsing again.
		void SkipRecovery(bool ParsingImports);

		void AddComptimeGen(ComptimePurpose P, void* Payload);

		void CheckFuncRedeclaration(llvm::DenseMap<Identifier, FuncsList>& Funcs, FuncDecl* Func);
		void CheckFuncRedeclaration(FuncsList& Funcs, FuncDecl* Func);
	
		void Error(Token Tok, const c8* Msg) {
			Log.Error(Tok.Loc, Msg);
		}

		void Error(SourceLoc Loc, const c8* Msg) {
			Log.Error(Loc, Msg);
		}

		template<typename... Targs>
		void Error(Token Tok, const c8* Fmt, Targs&&... Args) {
			Log.Error(Tok.Loc, Fmt, std::forward<Targs>(Args)...);
		}

		template<typename... Targs>
		void Error(SourceLoc Loc, const c8* Fmt, Targs&&... Args) {
			Log.Error(Loc, Fmt, std::forward<Targs>(Args)...);
		}
	};
}

#endif // JUNE_PARSER_H