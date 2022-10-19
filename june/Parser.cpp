#include "Parser.h"

#include <iostream>

#include <assert.h>

#include "Types.h"
#include "JuneContext.h"
#include <llvm/IR/Module.h>

namespace june {
	template<typename N>
	static inline N* NewNode(Token STok) {
		N* Node = new N;
		Node->Loc = STok.Loc;
		return Node;
	}

	static inline BinaryOp* NewBinaryOp(Token OpTok, Expr* LHS, Expr* RHS) {
		BinaryOp* Op = NewNode<BinaryOp>(OpTok);
		Op->LHS = LHS;
		Op->RHS = RHS;
		Op->Op  = OpTok.Kind;
		return Op;
	}

	VarDecl* Parser::Scope::FindVariable(Identifier Name) {
		Scope* S = this;
		while (S) {
			auto it = S->VarDecls.find(Name);
			if (it != S->VarDecls.end()) {
				return it->second;
			}
			S = S->Parent;
		}
		return nullptr;
	}
}

#define PUSH_SCOPE()        \
Scope NewScope;             \
NewScope.Parent = LocScope; \
LocScope = &NewScope;

#define POP_SCOPE() \
LocScope = LocScope->Parent;

june::Parser::Parser(JuneContext& context, FileUnit* FU, Logger& log)
	: Context(context), L(context, FU->SBuf, log), FU(FU), Log(log) {
}

void june::Parser::Parse() {
	// Priming the parser
	NextToken();

	while (CTok.isNot(TokenKind::TK_EOF)) {
		if (CTok.is(TokenKind::KW_IMPORT)) {
			ParseImport();
		} else {
			break;
		}
	}

	while (CTok.isNot(TokenKind::TK_EOF)) {
		AstNode* Node = nullptr; ParseOptStmt(Node);
		if (!Node) continue;

		switch (Node->Kind) {
		case AstKind::RECORD_DECL:
			break;
		case AstKind::VAR_DECL: {
			VarDecl* Var = ocast<VarDecl*>(Node);
			if (Var->isNot(AstKind::ERROR)) {
				Var->IsGlobal = true;
				Context.UncheckedDecls.insert(Var);
				auto it = FU->GlobalVars.find(Var->Name);
				if (it != FU->GlobalVars.end()) {
					Error(Var->Loc, "Redeclaration of global variable '%s'. First declared at line: %s",
						Var->Name.Text, it->second->Loc.LineNumber);
				}
				FU->GlobalVars.insert({ Var->Name, Var });
			}
			break;
		}
		case AstKind::FUNC_DECL:
		case AstKind::GENERIC_FUNC_DECL: {
			FuncDecl* Func = ocast<FuncDecl*>(Node);
			if (Func->isNot(AstKind::ERROR)) {
				CheckFuncRedeclaration(FU->GlobalFuncs, Func);
				FU->GlobalFuncs[Func->Name].push_back(Func);
			}
			break;
		}
		default:
			FU->InvalidStmts.push_back(std::make_tuple(FileUnit::StmtScopeKind::GLOBAL, Node));
			break;
		}
	}
}

void june::Parser::PrintTokens() {
	do {
		NextToken();
		llvm::outs() << "Token: " << CTok.GetLexicalPresentation(Context) << '\n';
	} while (CTok.Kind != TokenKind::TK_EOF);
}

void june::Parser::ParseImport() {
	Token ImportTk = CTok;
	NextToken(); // Consuming 'import' token

	bool MoreDots = false;
	std::string FilePath = "";
	Identifier LastKey;
	do {
		Identifier IdentKey = ParseIdentifier("Expected identifier for import path");
		if (IdentKey.isNull()) {
			SkipRecovery(true);
			return;
		}
		LastKey = IdentKey;

		if (!FilePath.empty()) {
			FilePath += ".";
		}

		FilePath += IdentKey.Text.str();

		MoreDots = CTok.is('.');
		if (MoreDots) {
			NextToken(); // Consuming '.' token
		}
	} while (MoreDots);

	bool GlobalUsingImport = false;
	if (CTok.is('(')) {
		NextToken(); // Consuming '(' token

		if (CTok.is(TokenKind::IDENT)) {
			if (CTok.GetText() == "global") {
				GlobalUsingImport = true;
				NextToken(); // Consuming 'global' token
			} else {
				Error(CTok, "Expected extended import information");
			}
		} else {
			Error(CTok, "Expected extended import information");
		}

		Match(')');
	}

	Match(';');

	if (!GlobalUsingImport && FU->Imports.find(LastKey) != FU->Imports.end()) {
		Error(ImportTk, "Duplicate import", FilePath);
		return;
	}

	auto it = Context.FileUnits.find(FilePath);
	if (it != Context.FileUnits.end()) {
		if (GlobalUsingImport) {
			auto findIt = std::find(FU->GlobalUsingImports.begin(),
				                    FU->GlobalUsingImports.end(), it->second);
			if (findIt != FU->GlobalUsingImports.end()) {
				Error(ImportTk, "Duplicate global import", FilePath);
				return;
			}
			FU->GlobalUsingImports.push_back(it->second);
		} else {
			FU->Imports.insert({ LastKey, it->second });
		}
	} else {
		Error(ImportTk, "Failed to find import for path key '%s'", FilePath);
	}
}

void june::Parser::ParseScopeStmts(LexScope& Scope) {
	Scope.StartLoc = CTok.Loc;
	Match('{');
	while (CTok.isNot('}') && CTok.isNot(TokenKind::TK_EOF)) {
		AstNode* Stmt = nullptr; ParseOptStmt(Stmt);
		if (Stmt) {
			Scope.Stmts.push_back(Stmt);
		}
	}
	Scope.EndLoc = CTok.Loc;
	Match('}');
}

void june::Parser::ParseOptStmt(AstNode*& Stmt) {
	while (CTok.is(';'))
		NextToken(); // Consume any extra ';'
	if (CTok.isNot('}') && !CTok.is(TokenKind::TK_EOF)) {
		Stmt = ParseStmt();
	}
}

june::AstNode* june::Parser::ParseStmt() {
	AstNode* Stmt;
	switch (CTok.Kind) {
	case TokenKind::KW_RETURN: Stmt = ParseReturn(); Match(';'); break;
	case TokenKind::KW_LOOP:   Stmt = ParseLoop();               break;
	case TokenKind::KW_IF:     Stmt = ParseIf();                 break;
	case TokenKind::KW_CONTINUE:
	case TokenKind::KW_BREAK:  Stmt = ParseLoopControl(); Match(';'); break;
	case TokenKind::KW_NATIVE:
	case TokenKind::KW_COMPTIME: {
		mods::Mod Mods = ParseModifiers();
		Token NameTok = CTok;
		NextToken(); // Consuming name token
		llvm::SmallVector<Identifier> Generics = ParseGenerics();
		if (!Generics.empty()) {
			// Variable declarations cannot have generics
			if (CTok.is('(')) {
				Stmt = ParseFuncDecl(NameTok, Mods, Generics);
			} else {
				Stmt = ParseRecordDecl(NameTok, Mods);
			}
		} else {
			if (CTok.is('(')) {
				Stmt = ParseFuncDecl(NameTok, Mods, Generics);
			} else if (CTok.is(TokenKind::COL_COL)) {
				Stmt = ParseRecordDecl(NameTok, Mods);
			} else {
				Stmt = ParseVarDecl(NameTok, Mods); Match(';');
			}
		}
		break;
	}
	case TokenKind::IDENT: {
		
		llvm::SmallVector<Identifier> Generics;
		if (PeekToken(1).is('<')) {
			Token NameTok = CTok;
			NextToken(); // Consuming name token
			Generics = ParseGenerics();

			// Variable declarations cannot have generics
			if (CTok.is('(')) {
				Stmt = ParseFuncDecl(NameTok, 0, Generics);
			} else {
				ParseRecordDecl(NameTok, 0);
			}
		} else {
			Token PeekedTok = PeekToken(1);
			if (PeekedTok.is('(')) {
				// Distinguishing between a function call and a function declaration.
		
				Token TkAfterOpenL = PeekToken(2);
				bool IsFunctionDecl = false;
				if (TkAfterOpenL.is(')')) {
					// These cases:
					//
					// Function declaration: ident() ->
					// Function declaration: ident() {
					// Function declaration: ident() -    - Even though not valid it is an easy mistake so included
					if (PeekToken(3).is(TokenKind::MINUS_GT) || PeekToken(3).is('{') || PeekToken(3).is('-')) {
						IsFunctionDecl = true;
					}
				} else if (TkAfterOpenL.is(TokenKind::IDENT) && PeekToken(3).is(':')) {
					// This case:
					// ident(ident :
					IsFunctionDecl = true;
				}

				if (IsFunctionDecl) {
					Token NameTok = CTok; NextToken();
					Stmt = ParseFuncDecl(NameTok, 0, Generics);
				} else {
					// Putting the identifier back.
					
					Stmt = ParseExpr(); Match(';'); // Function calls
				}
			}
			else if (PeekedTok.is(':')) {
				Token NameTok = CTok; NextToken();
				Stmt = ParseVarDecl(NameTok, 0); Match(';');
			} else if (PeekedTok.is(TokenKind::COL_COL)) {
				Token NameTok = CTok; NextToken();
				Stmt = ParseRecordDecl(NameTok, 0);
			} else {
				Stmt = ParseAssignmentAndExprs(); Match(';');
			}	
		}
		break;
	}
	case '{': Stmt = ParseInnerScope(); break;
	default: Stmt = ParseAssignmentAndExprs(); Match(';'); break;
	}
	return Stmt;
}

june::FuncDecl* june::Parser::ParseFuncDecl(Token NameTok, mods::Mod Mods, llvm::SmallVector<Identifier>& Generics) {
	
	Identifier Name = ParseIdentifier(NameTok, "Expected identifier for function declaration");

	FuncDecl* Func = nullptr;
	if (Generics.empty()) {
		Func = NewNode<FuncDecl>(NameTok);
	} else {
		GenericFuncDecl* GenericFunc = NewNode<GenericFuncDecl>(NameTok);
		u32 GenericIdx = 0;
		for (Identifier Generic : Generics) {
			GenericType* GenTy = new GenericType;
			GenTy->Name = Generic;
			GenTy->Idx = GenericIdx++;
			GenericFunc->GenericTypes.insert({ Generic, GenTy });
		}
		Func = GenericFunc;
	}
	
	Func->Name = Name;
	Func->Mods = Mods;
	Func->FU   = FU;

	FuncDecl* PrevCFunc = CFunc;
	CFunc = Func;

	if (Func->Mods & mods::Mods::NATIVE) {
		if (!NativeModifierName.empty()) {
			Func->NativeName = NativeModifierName;
		}
	}
	
	if (Func->Name.isNull()) {
		Func->Kind = AstKind::ERROR;
	}

	//
	// SCOPE START
	//
	PUSH_SCOPE();

	Match('(');
	if (CTok.isNot(')')) {
		Func->Params.push_back(ParseVarDecl(0));
		while (CTok.is(',')) {
			NextToken(); // Consuming ',' token
			Func->Params.push_back(ParseVarDecl(0));
		}
	}
	Match(')');
	if (CTok.is(TokenKind::MINUS_GT) || CTok.is('-')) {
		Match(TokenKind::MINUS_GT);
		Func->RetTy = ParseType();
	} else {
		Func->RetTy = Context.VoidType;
	}

	for (u32 i = 0; i < Func->Params.size(); i++) {
		Func->Params[i]->ParamIdx = i;
	}
	
	if (Func->RetTy->GetKind() == TypeKind::FIXED_ARRAY) {
		Error(Func->Loc, "Functions cannot return arrays");
	}

	if (!(Func->Mods & mods::NATIVE)) {
		ParseScopeStmts(Func->Scope);
	} else {
		Match(';');
	}

	//
	// SCOPE END
	//
	POP_SCOPE();

	if (!Func->is(AstKind::ERROR) && Name == Context.MainIdentifier) {
		if (!(Func->Mods & mods::NATIVE)) {
			if (!(Func->RetTy->is(Context.I32Type) || Func->RetTy->is(Context.VoidType))) {
				Error(Func->Loc, "The 'main' function must return either type 'i32' or 'void'");
				Log.Note("Declare main as: 'main()' or 'main() -> i32'").EndNote();
			}

			Func->IsMainFunc = true;
			if (!Context.MainEntryFunc) {
				Context.MainEntryFunc = Func;
			} else {
				// duplicate entry function
				Error(Func->Loc, "Duplicate entry point found. First declared at: %s:%s",
					Context.MainEntryFunc->FU->FL.PathKey, Context.MainEntryFunc->Loc.LineNumber);
			}
		}
	}

	if (Func->isNot(AstKind::ERROR)) {
		if (CRecord) {
			Func->Record = CRecord;
			if (Func->Name == CRecord->Name) {
				CheckFuncRedeclaration(CRecord->Constructors, Func);
				CRecord->Constructors.push_back(Func);
				if (Func->RetTy->isNot(Context.VoidType)) {
					Error(Func->Loc, "Constructors expected to return void");
				}
			} else {
				CheckFuncRedeclaration(CRecord->Funcs, Func);
				CRecord->Funcs[Name].push_back(Func);
			}
		}
		if (!(Func->Mods & mods::Mods::NATIVE)) {
			if (Func->isNot(AstKind::GENERIC_FUNC_DECL))
				Context.UncheckedDecls.insert(Func);
		}
	}

	CFunc = PrevCFunc;
	return Func;
}

june::VarDecl* june::Parser::ParseVarDecl(mods::Mod Mods) {
	Token NameTok = CTok; NextToken();
	return ParseVarDecl(NameTok, Mods);
}

june::VarDecl* june::Parser::ParseVarDecl(Token NameTok, mods::Mod Mods) {

	Identifier Name = ParseIdentifier(NameTok, "Expected identifier for variable declaration");

	VarDecl* Var = NewNode<VarDecl>(NameTok);
	Var->Name = Name;
	Var->Mods = Mods;
	Var->FU     = FU;
	Var->Record = CRecord;

	if (Var->Mods & mods::Mods::NATIVE) {
		if (!NativeModifierName.empty()) {
			Var->NativeName = NativeModifierName;
		}
	}

	if (Var->Mods & mods::Mods::NATIVE) {
		Context.RequestGen(Var);
	}

	if (Name.isNull()) {
		Var->Kind = AstKind::ERROR;
	}

	if (!Var->is(AstKind::ERROR)) {
		if (CFunc) {
			if (LocScope) {
				auto it = LocScope->VarDecls.find(Name);
				if (it != LocScope->VarDecls.end()) {
					Error(Var->Loc, "Redeclaration of variable '%s'. First declared at line: %s",
						Name.Text, it->second->Loc.LineNumber);
				}

				LocScope->VarDecls.insert({ Name, Var });
			}

			CFunc->AllocVars.push_back(Var);
		} else if (CRecord) {
			Var->FieldIdx = CRecord->Fields.size();
			CRecord->Fields.insert({ Name, Var });
			CRecord->FieldsByIdxOrder.push_back(Var);
		}
	}

	Match(':');
	if (CTok.is('=')) {
		Var->UsesInferedType = true;
	} else {
		Var->Ty = ParseType();
	}

	if (CTok.is('=')) {
		NextToken(); // Consuming '='
		Var->Assignment = ParseExpr();
	}

	return Var;
}

june::RecordDecl* june::Parser::ParseRecordDecl(Token NameTok, mods::Mod Mods) {

	Identifier Name = ParseIdentifier(NameTok, "Expected identifier for record declaration");

	Match(TokenKind::COL_COL);
	Match(TokenKind::KW_RECORD);

	RecordDecl* Record = NewNode<RecordDecl>(NameTok);
	Record->Name   = Name;
	Record->Mods   = Mods;
	Record->FU     = FU;
	Record->Parent = CRecord;

	RecordDecl* PrevCRecord = CRecord;
	CRecord = Record;

	if (Name.isNull()) {
		Record->Kind = AstKind::ERROR;
	}

	if (Record->isNot(AstKind::ERROR)) {
		RecordLocation Loc = RecordLocation::CreateRecLocationByRecord(Record);
		auto it = FU->Records.find(Loc);
		if (it != FU->Records.end()) {
			Error(Record->Loc, "Redeclaration of record '%s'. First declarated at line: %s",
				Name, it->second->Loc.LineNumber);
		}

		FU->Records.insert({ Loc, Record });
	}

	Match('{');
	while (CTok.isNot('}') && CTok.isNot(TokenKind::TK_EOF)) {
		AstNode* Stmt = nullptr; ParseOptStmt(Stmt);
		if (!Stmt) continue;
		
		if (Stmt->is(AstKind::VAR_DECL)) {
			Record->FieldsHaveAssignment |=
				ocast<VarDecl*>(Stmt)->Assignment != nullptr;
		} else if (Stmt->isNot(AstKind::FUNC_DECL) && Stmt->isNot(AstKind::RECORD_DECL)) {
			FU->InvalidStmts.push_back(std::make_tuple(FileUnit::StmtScopeKind::RECORD, Stmt));
		}
	}
	Match('}');

	CRecord = PrevCRecord;
	return Record;
}

june::Identifier june::Parser::ParseIdentifier(const c8* ErrorMessage) {
	if (CTok.isNot(TokenKind::IDENT)) {
		Error(CTok, ErrorMessage);
		return Identifier();
	}
	llvm::StringRef Text = CTok.GetText();
	NextToken(); // Consuming ident Token
	return Identifier(Text);
}

june::Identifier june::Parser::ParseIdentifier(Token PossibleIdent, const c8* ErrorMessage) {
	if (PossibleIdent.isNot(TokenKind::IDENT)) {
		Error(PossibleIdent, ErrorMessage);
		return Identifier();
	}
	llvm::StringRef Text = PossibleIdent.GetText();
	return Identifier(Text);
}

june::mods::Mod june::Parser::ParseModifiers() {
	NativeModifierName = "";
	mods::Mod mods = 0;
	while (true) {
	switch (CTok.Kind) {
	case TokenKind::KW_NATIVE: {
		if (mods & mods::NATIVE)
			Error(CTok, "Duplicate modifier");
		mods |= mods::NATIVE;

		NextToken(); // Consuming 'native' token

		if (CTok.is('(')) {
			NextToken(); // Consuming '(' token
			if (CTok.isNot(TokenKind::STRING_LITERAL)) {
				Error(CTok, "Expected string literal for native function name");
			} else {
				NativeModifierName = CTok.GetText();
				
				NativeModifierName = NativeModifierName.substr(1);
				if (!NativeModifierName.empty() && *(NativeModifierName.end()-1) == '"') {
					NativeModifierName = NativeModifierName.substr(0, NativeModifierName.size() - 1);
				}
				if (NativeModifierName.empty()) {
					Error(CTok, "Native name cannot be empty");
				}
			}
			
			NextToken(); // Consuming string literal
			Match(')');
		}
		break;
	}
	case TokenKind::KW_COMPTIME: {
		if (mods & mods::COMPTIME)
			Error(CTok, "Duplicate modifier");
		mods |= mods::COMPTIME;
		
		NextToken(); // Consuming 'comptime' token

		break;
	}
	default:
		return mods;
	}
	}
}

llvm::SmallVector<june::Identifier> june::Parser::ParseGenerics() {
	if (CTok.isNot('<')) return {};
	NextToken(); // Consuming '<' token

	llvm::SmallVector<Identifier> Generics;
	if (CTok.isNot('>')) {
		bool MoreGenerics = false;
		do {
			Token GenericNameTok = CTok;
			Identifier Generic = ParseIdentifier("Expected identifier for generic name");
			if (std::find(Generics.begin(), Generics.end(), Generic) != Generics.end()) {
				Error(GenericNameTok, "Duplicate generic");
			}
			Generics.push_back(Generic);
			MoreGenerics = CTok.is(',');
			if (MoreGenerics) {
				NextToken(); // Consuming ',' token
			}
		} while (MoreGenerics);
	}

	Match('>');
	return Generics;
}

june::InnerScopeStmt* june::Parser::ParseInnerScope() {
	InnerScopeStmt* InnerScope = NewNode<InnerScopeStmt>(CTok);
	PUSH_SCOPE();
	ParseScopeStmts(InnerScope->Scope);
	POP_SCOPE();
	return InnerScope;
}

june::ReturnStmt* june::Parser::ParseReturn() {

	ReturnStmt* Ret = NewNode<ReturnStmt>(CTok);
	NextToken(); // Consuming 'return'

	if (CFunc) {
		++CFunc->NumReturns;
	}

	if (CTok.isNot(';')) {
		Ret->Val = ParseExpr();
	}
	
	return Ret;
}

june::AstNode* june::Parser::ParseLoop() {
	Token LoopTok = CTok;
	NextToken(); // Consuming 'loop' token
	
	AstKind LoopKind;
	switch (CTok.Kind) {
	case ';':
		LoopKind = AstKind::RANGE_LOOP;
		break;
	case TokenKind::IDENT:
		if (PeekToken(1).is(':'))   // loop i :
			LoopKind = AstKind::RANGE_LOOP;
		else if (PeekToken(1).is(TokenKind::KW_IN))
			LoopKind = AstKind::ITERATOR_LOOP;
		else
			LoopKind = AstKind::PREDICATE_LOOP;
		break;
	default:
		LoopKind = AstKind::PREDICATE_LOOP;
		break;
	}

	if (LoopKind == AstKind::RANGE_LOOP) {
		return ParseRangeLoop(LoopTok);
	} else if (LoopKind == AstKind::ITERATOR_LOOP) {
		return ParseIteratorLoop(LoopTok);
	} else {
		return ParsePredicateLoop(LoopTok);
	}
}

june::RangeLoopStmt* june::Parser::ParseRangeLoop(Token LoopTok) {
	RangeLoopStmt* Loop = NewNode<RangeLoopStmt>(LoopTok);
	
	PUSH_SCOPE();
	if (CTok.isNot(';')) {
		Loop->Decl = ParseVarDecl(0);
	}
	Match(';');

	if (CTok.isNot(';')) {
		Loop->Cond = ParseExpr();
	}
	Match(';');

	if (CTok.isNot('{')) {
		Loop->Inc = ParseExpr();
	}

	ParseScopeStmts(Loop->Scope);
	POP_SCOPE();

	return Loop;
}


june::PredicateLoopStmt* june::Parser::ParsePredicateLoop(Token LoopTok) {
	PredicateLoopStmt* Loop = NewNode<PredicateLoopStmt>(LoopTok);
	if (CTok.isNot('{')) {
		Loop->Cond = ParseExpr();
	}

	PUSH_SCOPE();
	ParseScopeStmts(Loop->Scope);
	POP_SCOPE();

	return Loop;
}

june::IteratorLoopStmt* june::Parser::ParseIteratorLoop(Token LoopTok) {
	IteratorLoopStmt* Loop = NewNode<IteratorLoopStmt>(LoopTok);

	PUSH_SCOPE();
	
	Loop->VarVal = NewNode<VarDecl>(CTok);
	Loop->VarVal->Name = ParseIdentifier("Expected identifier for variable in loop");
	Loop->VarVal->Mods = 0;
	
	if (!Loop->VarVal->Name.isNull()) {
		LocScope->VarDecls.insert({ Loop->VarVal->Name, Loop->VarVal });
	}
	
	Match(TokenKind::KW_IN);
	Loop->IterOnExpr = ParseExpr();

	ParseScopeStmts(Loop->Scope);
	POP_SCOPE();

	return Loop;
}

june::IfStmt* june::Parser::ParseIf() {
	IfStmt* If = NewNode<IfStmt>(CTok);
	NextToken(); // Consuming 'if' token

	// TODO: Later allow for variable
	//       declarations inside of if statements
	If->Cond = ParseExpr();

	PUSH_SCOPE();
	ParseScopeStmts(If->Scope);
	POP_SCOPE();

	if (CTok.is(TokenKind::KW_ELSE)) {
		NextToken(); // Consuming 'else' token
		if (CTok.is(TokenKind::KW_IF)) {
			If->Else = ParseIf();
		} else {
			// Else on its own
			If->Else = ParseInnerScope();
			If->Else->Kind = AstKind::ELSE_SCOPE;
		}
	}

	return If;
}

june::LoopControlStmt* june::Parser::ParseLoopControl() {
	
	LoopControlStmt* LoopControl = NewNode<LoopControlStmt>(CTok);
	
	if (CTok.is(TokenKind::KW_CONTINUE)) {
		LoopControl->Kind = AstKind::CONTINUE;
	} else {
		LoopControl->Kind = AstKind::BREAK;
	}
		
	NextToken(); // Consuming 'break' or 'continue' token

	return LoopControl;
}

//===-------------------------------===//
// Expressions
//===-------------------------------===//

june::Expr* june::Parser::ParseAssignmentAndExprs() {
	Expr* LHS = ParseExpr();
	switch (CTok.Kind) {
	case '=':
	case TokenKind::PLUS_EQ:
	case TokenKind::MINUS_EQ:
	case TokenKind::STAR_EQ:
	case TokenKind::SLASH_EQ:
	case TokenKind::MOD_EQ:
	case TokenKind::AMP_EQ:
	case TokenKind::BAR_EQ:
	case TokenKind::CRT_EQ:
	case TokenKind::LT_LT_EQ:
	case TokenKind::GT_GT_EQ: {
		Token OpTok = CTok;
		NextToken(); // Consuming assignment operator token
		Expr* E = ParseExpr();
		return NewBinaryOp(OpTok, LHS, E);
	}
	default:
		return LHS;
	}
}

june::Expr* june::Parser::ParseExpr() {
	Expr* E = ParseBinaryOpExpr(ParsePrimaryAndPostExpr());
	if (CTok.is('?')) {
		TernaryCond* Ternary = NewNode<TernaryCond>(CTok);
		Ternary->Cond = E;
		NextToken(); // Consuming '?' token
		Ternary->Val1 = ParseExpr();
		if (Ternary->Val1->is(AstKind::ERROR)) {
			return E;
		}
		Match(TokenKind::BAR_GT);
		Ternary->Val2 = ParseExpr();
		return Ternary;
	}
	return E;
}

june::Expr* june::Parser::ParsePrimaryAndPostExpr() {
	Expr* E = ParsePrimaryExpr();
	if (CTok.is(TokenKind::PLUS_PLUS)) {
		UnaryOp* UOP = NewNode<UnaryOp>(CTok);
		UOP->Op = TokenKind::POST_PLUS_PLUS;
		NextToken(); // Consuming the unary operator
		UOP->Val = E;
		return UOP;
	} else if (CTok.is(TokenKind::MINUS_MINUS)) {
		UnaryOp* UOP = NewNode<UnaryOp>(CTok);
		UOP->Op = TokenKind::POST_MINUS_MINUS;
		NextToken(); // Consuming the unary operator
		UOP->Val = E;
		return UOP;
	} else {
		return E;
	}
}


june::Expr* june::Parser::ParseBinaryOpExpr(Expr* LHS) {
	// Since some operations have to be delayed
	// because of order of operations a stack
	// is formed keeping a backlog of those operations
	// that need to be processed later
	struct StackUnit {
		Token Op;
		Expr* E;
	};
	std::stack<StackUnit> OpStack;

	Token Op = CTok;
	Token NextOp;
	while (Context.BinaryOpsPrecedence.find(Op.Kind) != Context.BinaryOpsPrecedence.end()) {
		NextToken(); // Consuming the operator

		Expr* RHS = ParsePrimaryExpr();
		NextOp = CTok;
		bool MoreOperators = Context.BinaryOpsPrecedence.find(NextOp.Kind) != Context.BinaryOpsPrecedence.end();
		if (MoreOperators &&
			Context.BinaryOpsPrecedence[NextOp.Kind] > Context.BinaryOpsPrecedence[Op.Kind]) {
			// Delaying the operation until later since the next operator has a
			// higher precedence.
			StackUnit Unit = { Op, LHS };
			OpStack.push(Unit);
			LHS = RHS;
			Op = NextOp;
		} else {
			// Apply the binary operator!
			LHS = NewBinaryOp(Op, LHS, RHS);
	
			while (!OpStack.empty()) {
				RHS = LHS;
				StackUnit Unit = OpStack.top();
				// Still possible to have the right side have higher precedence.
				if (MoreOperators &&
					Context.BinaryOpsPrecedence[NextOp.Kind] > Context.BinaryOpsPrecedence[Unit.Op.Kind]) {
					LHS = RHS;
					Op = NextOp;
					break;
				}

				OpStack.pop();
				LHS = Unit.E;

				// Apply the binary operator!
				LHS = NewBinaryOp(Unit.Op, LHS, RHS);
			}
			Op = CTok;
		}
	}

	return LHS;
}

june::Expr* june::Parser::ParsePrimaryExpr() {
	switch (CTok.Kind) {
	//  ---- Literals ----
	case TokenKind::INT_LITERAL:    return ParseIntLiteral();
	case TokenKind::HEX_LITERAL:    return ParseHexLiteral();
	case TokenKind::BIN_LITERAL:    return ParseBinLiteral();
	case TokenKind::FLOAT_LITERAL:  return ParseFloatLiteral();
	case TokenKind::STRING_LITERAL: return ParseString8Literal();
	case TokenKind::CHAR_LITERAL:   return ParseCharLiteral();
	case TokenKind::KW_TRUE: {
		BoolLiteral* B = NewNode<BoolLiteral>(CTok);
		NextToken();
		B->tof = true;
		B->Ty = Context.BoolType;
		return B;
	}
	case TokenKind::KW_FALSE: {
		BoolLiteral* B = NewNode<BoolLiteral>(CTok);
		NextToken();
		B->tof = false;
		B->Ty = Context.BoolType;
		return B;
	}
	case TokenKind::KW_NULL: {
		Null* Nu = NewNode<Null>(CTok);
		NextToken(); // Consuming 'null'
		Nu->Ty = Context.NullType;
		return Nu;
	}
	// ---- Pre unary expressions ----
	case TokenKind::PLUS_PLUS:  case TokenKind::MINUS_MINUS: {
		UnaryOp* UOP = NewNode<UnaryOp>(CTok);
		UOP->Op = CTok.Kind;

		NextToken(); // Consuming the unary operator

		UOP->Val = ParsePrimaryExpr();
		return UOP;
	}
	case '-': case '+': {
		u16 Op = CTok.Kind;
		NextToken(); // Consuming the unary operator

		Expr* E = ParsePrimaryExpr();

		if (E->is(AstKind::NUMBER_LITERAL)) {
			// No reason to create a new node since
			// it is simple enough to compute the result
			// right away.
			
			NumberLiteral* Num = ocast<NumberLiteral*>(E);

			// TODO: Restrict overflows?
			if (Op == '-') {
				switch (Num->Ty->GetKind()) {
				case TypeKind::I8:
				case TypeKind::I16:
				case TypeKind::I32:
				case TypeKind::I64:
				case TypeKind::C8:
				case TypeKind::C16:
				case TypeKind::C32:
					Num->SignedIntValue = -Num->SignedIntValue;
					break;
				case TypeKind::U8:
				case TypeKind::U16:
				case TypeKind::U32:
				case TypeKind::U64:
					Num->UnsignedIntValue = -Num->UnsignedIntValue;
					break;
				case TypeKind::F32:
					Num->F32Value = -Num->F32Value;
					break;
				case TypeKind::F64:
					Num->F64Value = -Num->F64Value;
					break;
				}
			} // else '+' operator does not modify
			return Num;
		}

		UnaryOp* UOP = NewNode<UnaryOp>(CTok);
		UOP->Val = E;
		UOP->Op = Op;
		return UOP;
	}
	case '&': case '*': case '!': {
		UnaryOp* UOP = NewNode<UnaryOp>(CTok);
		UOP->Op = CTok.Kind;

		NextToken(); // Consuming the unary operator

		UOP->Val = ParsePrimaryExpr();
		return UOP;
	}
	// ---- Other ----
	case '(': {
		Token STok = CTok;
		NextToken(); // Consuming '(' token
		Expr* E = ParseExpr();
		if (!E->is(AstKind::ERROR) && CTok.isNot(','))
			Match(')');
		else if (!E->is(AstKind::ERROR) && CTok.is(',')) {
			// Tuples!
			Tuple* Tup = NewNode<Tuple>(STok);
			Tup->Values.push_back(E);
			while (CTok.is(',')) {
				NextToken(); // Consuming ',' token
				E = ParseExpr();
				Tup->Values.push_back(E);
				if (E->is(AstKind::ERROR))
					return Tup;
			}
			Match(')');
			return Tup;
		}
		return E;
	}
	case '[':
		return ParseArray();
	case TokenKind::KW_SIZEOF: {
		SizeofType* SO = NewNode<SizeofType>(CTok);
		NextToken(); // Consuming 'sizeof' token
		Match('(');
		SO->TyToGetSizeof = ParseType();
		SO->Ty = Context.U32Type;
		if (SO->TyToGetSizeof->is(Context.ErrorType)) {
			return SO;
		}
		Match(')');
		return SO;
	}
	case TokenKind::KW_CAST: {
		TypeCast* Cast = NewNode<TypeCast>(CTok);
		NextToken(); // Consuming 'cast' token
		Match('(');
		Cast->ToTy = ParseType();
		if (Cast->ToTy->is(Context.ErrorType)) {
			return Cast;
		}
		Match(')');
		Cast->Val = ParsePrimaryAndPostExpr();
		return Cast;
	}
	case TokenKind::KW_NEW: {
		HeapAllocType* HeapAlloc = NewNode<HeapAllocType>(CTok);
		NextToken(); // Consuming 'new' token
		HeapAlloc->TypeToAlloc = ParseType(false);
		return HeapAlloc;
	}
	case TokenKind::KW_THIS: {
		ThisRef* This = NewNode<ThisRef>(CTok);
		NextToken(); // Consuming 'this' token
		return ParseMemoryRefs(This);
	}
	case TokenKind::IDENT: {
		
		IdentRef* IRef = NewNode<IdentRef>(CTok);
		IRef->Ident = Identifier(CTok.GetText());

		// Even if the identifier is not in the current scope
		// of variable declarations it may be refering to
		// a function identifier or record,enum,ect.. so
		// no error is thrown and the process of determining
		// the identifier's declaration is processed during
		// analysis.
		if (LocScope) {
			if (VarDecl* VarRef = LocScope->FindVariable(IRef->Ident)) {
				IRef->VarRef  = VarRef;
				IRef->RefKind = IdentRef::VAR;
			}
		}

		NextToken(); // Consuming identifier token
		return ParseMemoryRefs(IRef);
	}
	default:
		Error(CTok, "Expected Expression");
		ErrorNode* EN = NewNode<ErrorNode>(CTok);
		NextToken(); // Shouldn't be needed but helps prevent endless looping
		SkipRecovery(false);
		return EN;
	}
}

june::Expr* june::Parser::ParseMemoryRefs(Expr* Site) {
	while (true) {
		switch (CTok.Kind) {
		case '(': {
			Site = ParseFuncCall(Site);
			break;
		}
		case '[': {
			ArrayAccess* AA = NewNode<ArrayAccess>(CTok);
			NextToken(); // Consuming '[' token

			AA->Site  = Site;
			AA->Index = ParseExpr();

			Site = AA;
			Match(']');
			break;
		}
		case '.': {
			FieldAccessor* FA = NewNode<FieldAccessor>(CTok);
			NextToken(); // Consuming '.' token

			FA->Ident = ParseIdentifier("Expected identifier for field");
			FA->Site  = Site;

			Site = FA;
			break;
		}
		default:
			return Site;
		}
	}
}

june::FuncCall* june::Parser::ParseFuncCall(Expr* Site) {
	FuncCall* FC = NewNode<FuncCall>(CTok);
	FC->Site = Site;
	NextToken(); // Consuming '(' token

	// In case it is a function declaration rather than
	// a function call it would be best to ignore declarations
	ErrorSkipVarDecl = true;

	if (CTok.isNot(')')) {
		bool MoreValues = false;
		bool AlreadyReportedErrAboutNamedArgsOrder = false;
		do {
			if (CTok.is(TokenKind::IDENT) && PeekToken(1).is('=')) {
				FuncCall::NamedArg NamedArg;
				NamedArg.Loc = CTok.Loc;
				NamedArg.Name = ParseIdentifier("Expected identifier for field name");
				NextToken(); // Consuming '='
				NamedArg.AssignValue = ParseExpr();
				FC->NamedArgs.push_back(NamedArg);
			} else {
				Expr* Arg = ParseExpr();
				FC->Args.push_back(Arg);
				if (!FC->NamedArgs.empty() && !AlreadyReportedErrAboutNamedArgsOrder &&
					Arg->isNot(AstKind::ERROR)) {
					Error(Arg->Loc, "Non-named arguments should come before named arguments");
					AlreadyReportedErrAboutNamedArgsOrder = true;
				}
			}
			if (CTok.is(',')) {
				NextToken(); // Consuming ','
				MoreValues = CTok.isNot(')');
			} else if (CTok.is(')')) {
				MoreValues = false;
			} else {
				SkipRecovery(false);
				MoreValues = false;
			}
		} while (MoreValues);
	}

	ErrorSkipVarDecl = false;

	Match(')', "for function call");
	return FC;
}

june::NumberLiteral* june::Parser::ParseIntLiteral() {
	assert(CTok.is(TokenKind::INT_LITERAL) && "The current token must be an integeral literal");

	llvm::StringRef Text = CTok.GetText();

	u32 Idx = 0;
	u64 IntValue = 0, PrevValue;
	while (Idx < Text.size()) {
		c8 C = Text[Idx];
		if (C == '\'') continue;
		if (!IsDigit(C)) break;
		++Idx;

		PrevValue = IntValue;
		IntValue = IntValue * 10 + ((u64)C - '0');

		// Check for overflow
		if (IntValue / 10 < PrevValue) {
			Error(CTok, "Integer value is too large");
			break;
		}
	}

	return FinalizeIntLiteral(Idx, IntValue);
}

june::NumberLiteral* june::Parser::ParseHexLiteral() {
	
	llvm::StringRef Text = CTok.GetText();

	// TODO: replace with array
	static std::unordered_map<c8, u64> HexToDecimalMapping =
	{
		{ '0', 0  }, { '1', 1  }, { '2', 2  }, { '3', 3  }, { '4', 4  },
		{ '5', 5  }, { '6', 6  }, { '7', 7  }, { '8', 8  }, { '9', 9  },
		{ 'a', 10 }, { 'b', 11 }, { 'c', 12 }, { 'd', 13 }, { 'e', 14 },
		{ 'f', 15 },
		{ 'A', 10 }, { 'B', 11 }, { 'C', 12 }, { 'D', 13 }, { 'E', 14 },
		{ 'F', 15 },
	};
	
	u32 Idx = 2; // Skip 0x
	u64 IntValue = 0, PrevValue;
	while (Idx < Text.size()) {
		c8 C = Text[Idx];
		if (C == '\'') continue;
		if (!IsHex(C)) break;
		++Idx;
		
		PrevValue = IntValue;
		IntValue = IntValue * 16 + HexToDecimalMapping[C];

		// Check for overflow
		if (IntValue / 16 < PrevValue) {
			Error(CTok, "Integer value is too large");
			break;
		}
	}

	return FinalizeIntLiteral(Idx, IntValue);
}

june::NumberLiteral* june::Parser::ParseBinLiteral() {

	llvm::StringRef Text = CTok.GetText();
	u32 Idx = 2; // Skip 0b
	u64 IntValue = 0, PrevValue;
	while (Idx < Text.size()) {
		c8 C = Text[Idx];
		if (C == '\'') continue;
		if (!(C == '0' || C == '1')) break;
		++Idx;

		PrevValue = IntValue;
		IntValue = IntValue * 2 + ((u64)C - '0');

		// Check for overflow
		if (IntValue / 2 < PrevValue) {
			Error(CTok, "Integer value is too large");
			break;
		}
	}

	return FinalizeIntLiteral(Idx, IntValue);
}

june::NumberLiteral* june::Parser::FinalizeIntLiteral(u32 Idx, u64 IntValue) {
	NumberLiteral* Number = NewNode<NumberLiteral>(CTok);
	
	llvm::StringRef Text = CTok.GetText();
	bool Unsigned = false;
	if (Idx < Text.size()) {
		switch (Text[Idx]) {
		case 'b': case 'B':
			Number->Ty = Context.I8Type;
			break;
		case 's': case 'S':
			Number->Ty = Context.I16Type;
			break;
		case 'i': case 'I':
			Number->Ty = Context.I32Type;
			break;
		case 'l': case 'L':
			Number->Ty = Context.I64Type;
			break;
		case 'u': {
			Unsigned = true;
			if (++Idx < Text.size()) {
				switch (Text[Idx]) {
				case 'b': case 'B':
					Number->Ty = Context.U8Type;
					break;
				case 's': case 'S':
					Number->Ty = Context.U16Type;
					break;
				case 'i': case 'I':
					Number->Ty = Context.U32Type;
					break;
				case 'l': case 'L':
					Number->Ty = Context.U64Type;
					break;
				}
			} else {
				Number->Ty = Context.U32Type;
			}
			break;
		}
		}
	} else {
		if (IntValue <= std::numeric_limits<s32>::max()) {
			Number->Ty = Context.I32Type;
		} else if (IntValue <= std::numeric_limits<s64>::max()) {
			Number->Ty = Context.I64Type;
		} else {
			Number->Ty = Context.U64Type;
			Unsigned = true;
		}
	}
	
	if (Unsigned) {
		Number->UnsignedIntValue = IntValue;
	} else {
		Number->SignedIntValue = IntValue;
	}

	NextToken();

	return Number;
}

june::NumberLiteral* june::Parser::ParseFloatLiteral() {

	const c8* Ptr = CTok.GetText().begin();
	u32 Len = CTok.GetText().size();

	// Calculating whole value.
	double Value = 0.0;
	u32 Index = 0;
	while (true) {
		c8 C = Ptr[Index];
		if (C == '\'') continue;
		if (!IsDigit(C)) break;
		++Index;
		Value *= 10.0;
		Value += (u64)((u64)C - '0');
	}
	u32 NumFractionDigits = 0;
	if (Ptr[Index] == '.') {
		// Calculating fraction digits
		++Index; // Move over '.'
		while (Index < Len && IsDigit(Ptr[Index])) {
			Value *= 10.0;
			Value += (u64)((u64)Ptr[Index++] - '0');
			++NumFractionDigits;
		}
	}
	s64 ExponentValue = 0;
	if (Index < Len && Ptr[Index] == 'E') {
		++Index; // Move over 'E'
		
		bool IsNeg = false;
		if (Index < Len && (Ptr[Index] == '+' || Ptr[Index] == '-')) {
			if (Ptr[Index] == '-') IsNeg = true;
			++Index;
		}

		// Calculating Exponent digits
		while (Index < Len && IsDigit(Ptr[Index])) {
			ExponentValue *= 10.0;
			ExponentValue += (u64)((u64)Ptr[Index++] - '0');
		}

		if (IsNeg) {
			ExponentValue = -ExponentValue;
		}
	}
	ExponentValue -= NumFractionDigits;

	if (ExponentValue != 0) {
		Value *= pow(10.0, ExponentValue);
	}

	NumberLiteral* Number = NewNode<NumberLiteral>(CTok);
	NextToken(); // Consuming float literal

	if (Index < Len && (Ptr[Index] == 'f')) {
		Number->Ty       = Context.F32Type;
		Number->F32Value = Value;
	} else {
		Number->Ty       = Context.F64Type;
		Number->F64Value = Value;
	}

	return Number;
}

// Returns 0xFF is invalid escape
static c8 GetEscapeChar(c8 ch) {
	switch (ch) {
	case '\\': return '\\';
	case 'n':  return '\n';
	case 't':  return '\t';
	case '0':  return '\0';
	case '"':  return '"';
	case 'a':  return '\a';
	case 'r':  return '\r';
	case 'v':  return '\v';
	case 'b':  return '\b';
	case 'f':  return '\f';
	case '?':  return '\?';
	case '\'': return '\'';
	default:
		return 0xFF;
	}
}

june::String8Literal* june::Parser::ParseString8Literal() {
	// Converting the backslashes into the correct codes

	String8Literal* String = NewNode<String8Literal>(CTok);
	String->ElmSlot = NewNode<NumberLiteral>(CTok);
	String->ElmSlot->Ty = Context.C8Type;

	llvm::StringRef Text = CTok.Loc.Text;
	u32 Index = 1;
	while (Index < Text.size() - 1) {
		c8 ch = Text[Index++];
		switch (ch) {
		case '\\': {
			c8 Escape = GetEscapeChar(Text[Index++]);
			if (Escape == 0xFF) {
				Error(CTok, "Unexpected escape sequence at index '%s'", Index - 2);
				goto stringLiteralSequenceError;
			} else {
				String->Characters += Escape;
			}
			break;
		}
		default:
			String->Characters += ch;
			break;
		}	
	}
stringLiteralSequenceError:

	NextToken(); // Consuming string literal token

	String->Characters += '\0'; // Null terminate the string.
	String->NumElements = String->Characters.size();
	String->RequiredNumElements = String->NumElements;

	return String;
}

june::NumberLiteral* june::Parser::ParseCharLiteral() {
	llvm::StringRef Text = CTok.GetText();
	if (Text[1] == '\\') {
		NumberLiteral* Number = NewNode<NumberLiteral>(CTok);
		Number->Ty = Context.C8Type;

		c8 Escape = GetEscapeChar(Text[2]);
		
		NextToken(); // Consuming the character token.

		if (Escape == 0xFF) {
			Error(CTok, "Unexpected escape sequence in char");
			return Number;
		} else {
			Number->SignedIntValue = Escape;
			return Number;
		}
	} else {
		NumberLiteral* Number = NewNode<NumberLiteral>(CTok);
		Number->Ty = Context.C8Type;
		Number->SignedIntValue = Text[1];

		NextToken(); // Consuming the character token.
		return Number;
	}
}

june::Array* june::Parser::ParseArray() {
	ExprFilledArray* Arr = NewNode<ExprFilledArray>(CTok);
	Match('[');

	if (ArrNestingLevel == 0) {
		// Clearing the sizes for the new array.
		for (u32 i = 0; i < MAX_ARRAY_NESTING_LEVEL; i++) {
			ArrNestingLengths[i] = 0;
		}
	}

	++ArrNestingLevel;
	if (CTok.isNot(']')) {
		bool MoreElements = false;
		do {

			Arr->Elements.push_back(ParseExpr());

			MoreElements = CTok.is(',');
			if (MoreElements) {
				NextToken(); // Consuming ',' token
			}
			if (CTok.is(']')) {
				break; // Allow for extra ',' token at the end
			}
		} while (MoreElements);
	}
	--ArrNestingLevel;

	Arr->NumElements = Arr->Elements.size();
	if (ArrNestingLevel < MAX_ARRAY_NESTING_LEVEL) {
		// Finding the maximum length at the given nesting level.
		if (Arr->NumElements > ArrNestingLengths[ArrNestingLevel]) {
			ArrNestingLengths[ArrNestingLevel] = Arr->NumElements;
		}
	} else {
		Error(Arr->Loc, "Array exceeds maximum array nesting level allowed");
		Log.Note("Maximum nesting level: %s", MAX_ARRAY_NESTING_LEVEL).EndNote();
	}

	if (ArrNestingLevel == 0) {
		// The array is finished being defined so applying
		// the maximum lengths for the nesting levels.
		SetNestingLevelLengths(Arr, 0);
	}

	Match(']');
	return Arr;
}

void june::Parser::SetNestingLevelLengths(Array* Arr, u32 CNestingLevel) {
	Arr->RequiredNumElements = ArrNestingLengths[CNestingLevel];
	for (u32 i = 0; i < Arr->NumElements; i++) {
		Expr* Elm = Arr->GetElement(i);
		if (Elm->is(AstKind::ARRAY)) {
			SetNestingLevelLengths(ocast<Array*>(Elm), CNestingLevel + 1);
		}
	}
}

june::Type* june::Parser::ParseType(bool ReqArrayLengthComptime) {
	Type* Ty = nullptr;
	switch (CTok.Kind) {
	case TokenKind::KW_TYPE_I8:     NextToken(); Ty = Context.I8Type;     break;
	case TokenKind::KW_TYPE_I16:    NextToken(); Ty = Context.I16Type;    break;
	case TokenKind::KW_TYPE_I32:    NextToken(); Ty = Context.I32Type;    break;
	case TokenKind::KW_TYPE_I64:    NextToken(); Ty = Context.I64Type;    break;
	case TokenKind::KW_TYPE_U8:     NextToken(); Ty = Context.U8Type;     break;
	case TokenKind::KW_TYPE_U16:    NextToken(); Ty = Context.U16Type;    break;
	case TokenKind::KW_TYPE_U32:    NextToken(); Ty = Context.U32Type;    break;
	case TokenKind::KW_TYPE_U64:    NextToken(); Ty = Context.U64Type;    break;
	case TokenKind::KW_TYPE_OSINT: {
		NextToken();
		switch (Context.LLJuneModule.getDataLayout().getPointerSize()) {
		case 1: Ty = Context.I8Type;  break;
		case 2: Ty = Context.I16Type; break;
		case 4: Ty = Context.I32Type; break;
		case 8: Ty = Context.I64Type; break;
		}
		break;
	}
	case TokenKind::KW_TYPE_OSUINT: {
		NextToken();
		switch (Context.LLJuneModule.getDataLayout().getPointerSize()) {
		case 1: Ty = Context.U8Type;  break;
		case 2: Ty = Context.U16Type; break;
		case 4: Ty = Context.U32Type; break;
		case 8: Ty = Context.U64Type; break;
		}
		break;
	}
	case TokenKind::KW_TYPE_C8:     NextToken(); Ty = Context.C8Type;     break;
	case TokenKind::KW_TYPE_C16:    NextToken(); Ty = Context.C16Type;    break;
	case TokenKind::KW_TYPE_C32:    NextToken(); Ty = Context.C32Type;    break;
	case TokenKind::KW_TYPE_F32:    NextToken(); Ty = Context.F32Type;    break;
	case TokenKind::KW_TYPE_F64:    NextToken(); Ty = Context.F64Type;    break;
	case TokenKind::KW_TYPE_BOOL:   NextToken(); Ty = Context.BoolType;   break;
	case TokenKind::KW_TYPE_VOID:   NextToken(); Ty = Context.VoidType;   break;
	case TokenKind::IDENT: {
		
		// Check to see if the type is a generic type
		if (CFunc && CFunc->is(AstKind::GENERIC_FUNC_DECL)) {
			GenericFuncDecl* GenericFunc = ocast<GenericFuncDecl*>(CFunc);
			auto it = GenericFunc->GenericTypes.find(Identifier(CTok.GetText()));
			if (it != GenericFunc->GenericTypes.end()) {
				Ty = it->second;
				NextToken(); // Consuming generic name token
				break;
			}
		}

		Token StartTok = CTok;
		RecordLocation Loc = ParseRecordLocation();
		Token EndTok = PrevToken;

		auto it = FU->QualifyingRecordTypes.find(std::make_tuple(CRecord, Loc));
		if (it != FU->QualifyingRecordTypes.end()) {
			Ty = it->second.RecType;
		} else {
			FileUnit::QualifyingRecordType URT;
			u32 ErrorLocLen = EndTok.GetText().end() - StartTok.GetText().begin();
			URT.ErrorLoc.Text = llvm::StringRef(StartTok.GetText().begin(), ErrorLocLen);
			URT.ErrorLoc.LineNumber = StartTok.Loc.LineNumber;
			URT.RelRecord = CRecord;
			URT.RecType = new RecordType;
			FU->QualifyingRecordTypes.insert({ std::make_tuple(CRecord, Loc), URT });
			Ty = URT.RecType;
		}

		break;
	}
	case '`': {
		NextToken(); // Consuming '`' token
		Ty = ParseType(ReqArrayLengthComptime);
		if (Ty->GetKind() == TypeKind::ERROR) {
			return Ty;
		}
		Match('`');
		break;
	}
	case '(': {
		Token STok = CTok;
		NextToken(); // Consuming '(' token

		llvm::SmallVector<Type*, 4> ParamTypes;
		if (CTok.is(TokenKind::IDENT) && PeekToken(1).is(':')) {
			bool MoreParams = false;
			do {
				ParseIdentifier("Expected identifier for function parameter");
				Match(':');
				ParamTypes.push_back(ParseType());
				MoreParams = CTok.is(',');
				if (MoreParams)
					NextToken(); // Consuming ',' token
			} while (MoreParams);
		} else if (CTok.isNot(')')) {
			ParamTypes.push_back(ParseType());
			while (CTok.is(',')) {
				NextToken(); // Consuming ',' token
				ParamTypes.push_back(ParseType());
			}
		}

		Match(')');
		if (CTok.is(TokenKind::MINUS_GT)) {
			NextToken();
			Type* RetTy = ParseType();
			Ty = FunctionType::Create(RetTy, ParamTypes);
		} else {
			if (ParamTypes.size() < 2) {
				Error(STok, "Tuple types must have at least two value types");
			} 
			Ty = TupleType::Create(ParamTypes);
		}

		break;
	}
	default:
		Error(CTok, "Expected Type");
		SkipRecovery(false);
		return Context.ErrorType;
	}

	if (CTok.is('*')) {
		NextToken(); // Consuming '*' token
		u32 NumStars = 1;
		while (CTok.is('*')) {
			NextToken();
			++NumStars;
		}
		for (u32 i = 0; i < NumStars; i++) {
			Ty = PointerType::Create(Ty, Context);
		}
	}

	if (CTok.is('[')) {
		// Fixed sized array
		FixedArrayType* PrevArrType = nullptr;
		FixedArrayType* FstArrType  = nullptr;
		while (CTok.is('[')) {
			NextToken(); // Consuming '[' token

			FixedArrayType* ArrType = FixedArrayType::Create(nullptr, 0, Context);
			if (!FstArrType)
				FstArrType = ArrType;
			if (PrevArrType) {
				PrevArrType->ElmTy = ArrType;
			}

			PrevArrType = ArrType;
			ArrType->LengthAsExpr = ParseExpr();

			// Can't generate it until more information is known about
			// other files. So it is delayed.
			if (ReqArrayLengthComptime) {
				AddComptimeGen(ComptimePurpose::ARRAY_DIM_SIZE, ArrType);
			}
			
			Match(']');
		}

		if (PrevArrType)
			PrevArrType->ElmTy = Ty;
		return FstArrType;
	}

	return Ty;
}

june::RecordLocation june::Parser::ParseRecordLocation() {
	Identifier Ident = ParseIdentifier("Expected identifier for record type");
	if (Ident.isNull()) return RecordLocation();
	RecordLocation Loc;
	Loc.Nesting.push_back(Ident);
	while (CTok.is('.')) {
		NextToken(); // Consuming '.' token
		Ident = ParseIdentifier("Expected identifier for record type");
		if (Ident.isNull()) return Loc;
		Loc.Nesting.push_back(Ident);
	}
	return Loc;
}

void june::Parser::NextToken() {
	PrevToken = CTok;
	if (!SavedTokens.empty()) {
		CTok = SavedTokens.front();
		SavedTokens.pop();
	} else {
		CTok = L.NextToken();
	}
}

june::Token june::Parser::PeekToken(u32 n) {
	if (n == 0)
		assert(!"There is no reason to peek zero tokens");

	for (u32 i = SavedTokens.size(); i < n; i++) {
		SavedTokens.push(L.NextToken());
	}
	return SavedTokens.back();
}

void june::Parser::Match(u16 TokenKind, const c8* Purpose) {
	if (CTok.is(TokenKind)) {
		NextToken(); // Consuming the matched token
		return;
	}
	Error(PrevToken, "Expected '%s'%s%s", GetTokenKindPresentation(TokenKind, Context),
		Purpose ? " " : "", Purpose);
}

void june::Parser::SkipRecovery(bool ParsingImports) {
	while (true) {
		switch (CTok.Kind) {
		case TokenKind::TK_EOF:
		case ';':
			return;
			// Declaration
		case TokenKind::IDENT:
			if ((PeekToken(1).is(':') && !ErrorSkipVarDecl) ||
				 PeekToken(1).is(TokenKind::COL_COL))
				return;
			NextToken(); // Consuming identifier
			break;
		case TokenKind::KW_IMPORT:
			if (ParsingImports)
				return;
			NextToken();
			break;
			// Statements
		case TokenKind::KW_RETURN:
		case TokenKind::KW_LOOP:
		case TokenKind::KW_IF:
		case TokenKind::KW_BREAK:
		case TokenKind::KW_CONTINUE:
			// Include an modifiers since those come at
			// the start of a statement.
		case TokenKind::KW_NATIVE:
		case TokenKind::KW_COMPTIME:
			return;
		case '{':
			return;
		default:
			// Skip and continue
			NextToken();
			break;
		}
	}
}

void june::Parser::AddComptimeGen(ComptimePurpose P, void* Payload) {
	ComptimeValue CV(Log);
	CV.P = P;
	CV.Payload = Payload;
	Context.RequestComptimeGen(CV);
}

void june::Parser::CheckFuncRedeclaration(llvm::DenseMap<Identifier, FuncsList>& Funcs, FuncDecl* Func) {
	auto it = Funcs.find(Func->Name);
	if (it != Funcs.end()) {
		CheckFuncRedeclaration(it->second, Func);
	}
}

void june::Parser::CheckFuncRedeclaration(FuncsList& Funcs, FuncDecl* Func) {
	for (FuncDecl* OFunc : Funcs) {
			if (OFunc->Params.size() != Func->Params.size()) continue;
			bool ParamTysMatch = true;
			for (u32 i = 0; i < OFunc->Params.size(); i++) {
				if (Func->Params[i]->Ty->isNot(OFunc->Params[i]->Ty)) {
					ParamTysMatch = false;
					break;
				}
			}
			if (ParamTysMatch) {
				Error(Func->Loc, "Redeclaration of function '%s'. First declarated at line: %s",
					Func->Name, OFunc->Loc.LineNumber);
				break;
			}
		}
}
