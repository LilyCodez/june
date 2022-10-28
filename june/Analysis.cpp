#include "Analysis.h"

#include "Types.h"
#include "JuneContext.h"
#include "Tokens.h"
#include "TypeBinding.h"

#include <limits>
#include <unordered_set>

inline u32 max(u32 a, u32 b) {
	return a > b ? a : b;
}

#define YIELD_ERROR(N)     \
N->Ty = Context.ErrorType; \
return;
#define YIELD_ERROR_WHEN(CH)     \
if (CH->Ty                       \
        ->is(Context.ErrorType)) \
	return;
#define YIELD_ERROR_WHEN_M(N, CH)  \
if (CH->Ty                         \
        ->is(Context.ErrorType)) { \
	YIELD_ERROR(N); }

june::Analysis::Analysis(JuneContext& context, Logger& log, bool forCodeGen)
	: Context(context), Log(log), ForCodeGen(forCodeGen) {
}

void june::Analysis::ResolveRecordTypes(JuneContext& Context, FileUnit* FU) {

	if (!Context.CompileAsStandAlone) {
		// Auto import the string class.
		FU->Imports.insert({ Identifier("String"), Context.StringFU });
	}

	for (auto& [RelLoc, URT] : FU->QualifyingRecordTypes) {

		RecordDecl* FoundRecord = nullptr;

		RecordLocation RelRecLoc = std::get<1>(RelLoc);
		// relative search
		if (URT.RelRecord) {
			if (URT.RelRecord &&
				RelRecLoc.Nesting.size() == 1 &&
				RelRecLoc.Nesting[0] == URT.RelRecord->Name) {
				RecordLocation RecLoc =
					RecordLocation::CreateRecLocationByRecord(URT.RelRecord);
				FoundRecord = FU->Records.find(RecLoc)->second;
			} else {
				RecordLocation RecLoc =
					RecordLocation::CreateRecLocationRelToRec(URT.RelRecord, RelRecLoc);
				auto RelItr = FU->Records.find(RecLoc);
				if (RelItr != FU->Records.end()) {
					FoundRecord = RelItr->second;
				}
			}
		}

		// Absolute search of local file
		if (!FoundRecord) {
			// Absolute search
			auto FUAbsItr = FU->Records.find(RelRecLoc);
			if (FUAbsItr != FU->Records.end()) {
				FoundRecord = FUAbsItr->second;
			}
		}

		// Absolute search from an import
		if (!FoundRecord) {
			auto ImportItr = FU->Imports.find(RelRecLoc.Nesting[0]);
			if (ImportItr != FU->Imports.end()) {
				FileUnit* ExternalFU = ImportItr->second;
				auto ExternalAbsItr = ExternalFU->Records.find(RelRecLoc);
				if (ExternalAbsItr != ExternalFU->Records.end()) {
					FoundRecord = ExternalAbsItr->second;
				}
			}
		}

		// Absolute search in global using import.
		if (!FoundRecord) {
			for (FileUnit* GlobalFU : FU->GlobalUsingImports) {
				auto FUAbsItr = GlobalFU->Records.find(RelRecLoc);
				if (FUAbsItr != GlobalFU->Records.end()) {
					FoundRecord = FUAbsItr->second;
				}
			}
		}

		if (!FoundRecord) {
			FU->Log.BeginError(URT.ErrorLoc, "Could not find record type '%s'", RelRecLoc.ToStr());
			FU->Log.EndError();
		} else {
			URT.RecType->Record = FoundRecord;
		}
	}
}

void june::Analysis::CheckRecords(JuneContext& Context, FileUnit* FU) {
	for (auto& [_, Record] : FU->Records) {
		Analysis A(Context, FU->Log, false);
		A.CheckRecordDecl(Record);
	}
}

void june::Analysis::ReportInvalidFUStmts(FileUnit* FU) {
	for (auto& [Kind, InvalidStmt] : FU->InvalidStmts) {
		FU->Log.BeginError(InvalidStmt->Loc, "Invalid statement at %s scope",
			Kind == FileUnit::StmtScopeKind::GLOBAL ? "global" : "record");
		FU->Log.EndError();
	}
}

void june::Analysis::CheckVarDecl(VarDecl* Var) {
	if (Var->HasBeenChecked) return;

	FU      = Var->FU;
	CRecord = Var->Record;
	CFunc   = Var->Func;

	Var->HasBeenChecked = true;
	Var->IsBeingChecked = true;

	if (Var->FieldIdx != -1) {
		CField = Var;
	} else if (Var->IsGlobal) {
		// Global variable. Need to request generation.
		CGlobal = Var;
		Context.RequestGen(Var);
		if (!Var->ParentDeclList) {
			Context.UncheckedDecls.erase(Var);
		}
	}

#define VAR_YIELD(E)         \
E;                           \
Var->IsBeingChecked = false; \
CField  = nullptr;           \
CGlobal = nullptr;           \
YIELD_ERROR(Var)

	if (Var->Mods & mods::Mods::NATIVE && Var->FieldIdx != -1) {
		VAR_YIELD(Error(Var, "Variables marked 'native' cannot be a field"));
	}

	if (Var->Assignment) {

		CheckNode(Var->Assignment);

		if (Var->Mods & mods::Mods::NATIVE) {
			VAR_YIELD(Error(Var, "Variables marked 'native' should not be initialized"));
		}

		if (Var->Assignment->Ty->is(Context.ErrorType)) {
			VAR_YIELD();
		}

		if (Var->UsesInferedType) {
			if (!CheckInferedTypeAssignment(Var, Var->Assignment)) {
				VAR_YIELD();
			}
			Var->Ty = Var->Assignment->Ty;
		}

		if (Var->Ty->is(Context.VoidType)) {
			VAR_YIELD(Error(Var, "Variables cannot have type 'void'"));
		}

		if (Var->Assignment->Ty->GetKind() == TypeKind::UNDEFINED) {
			VAR_YIELD(Error(Var, "Cannot infer the type from an assignment of an undefined type"));
		}

		if (!Var->UsesInferedType && !IsAssignableTo(Var->Ty, Var->Assignment)) {
			VAR_YIELD(Error(Var,
				"Cannot assign value of type '%s' to variable of type '%s'",
				Var->Assignment->Ty->ToStr(), Var->Ty->ToStr()));
		}

		if (Var->Mods & mods::Mods::COMPTIME) {
			if (!Var->Assignment->IsComptimeCompat) {
				VAR_YIELD(Error(Var,
					"Variable marked 'comptime' but assignment was not able to be evaluted at compilation time"));
			}
			
			if (Var->Ty->GetKind() == TypeKind::FIXED_ARRAY) {
				VAR_YIELD(Error(Var,
					"Variable marked 'comptime' do not support arrays currently"));
			}

			if (Var->Ty->GetKind() == TypeKind::RECORD) {
				VAR_YIELD(Error(Var,
					"Variable marked 'comptime' do not support records currently"));
			}

			if (Var->Ty->GetKind() == TypeKind::TUPLE) {
				VAR_YIELD(Error(Var,
					"Variable marked 'comptime' do not support tuples currently"));
			}
		}

		AssignTo(Var->Assignment, Var->Ty, Var->Loc);

	} else if (Var->Mods & mods::Mods::COMPTIME) {
		VAR_YIELD(Error(Var, "Variables marked 'comptime' should be initialized"));
	}

	CheckRecordsInType(Var->Loc, Var->Ty);

	Var->IsBeingChecked = false;
	CField = nullptr;
	CGlobal = nullptr;

#undef VAR_YIELD
}

void june::Analysis::CheckRecordDecl(RecordDecl* Record) {
	if (Record->HasBeenChecked) return;

	FU = Record->FU;
	CRecord = Record;

	Record->HasBeenChecked = true;
	Record->IsBeingChecked = true;
	
	for (auto& [_, Field] : Record->Fields) {
		CheckVarDecl(Field);

		if (Field->Ty->GetKind() == TypeKind::RECORD) {
			RecordDecl* FieldRecord = Field->Ty->AsRecordType()->Record;
			Record->FieldsHaveAssignment |= FieldRecord->FieldsHaveAssignment;	
		}
	}

	Record->IsBeingChecked = false;
}

void june::Analysis::CheckFuncDecl(FuncDecl* Func) {
	
	if (Func->Mods & mods::NATIVE) return;
	
	Context.UncheckedDecls.erase(Func);

	FU      = Func->FU;
	CFunc   = Func;
	CRecord = Func->Record;

	Scope FuncScope(Func);
	CheckScope(Func->Scope, FuncScope);
	if (!FuncScope.AllPathsReturn && Func->RetTy->isNot(Context.VoidType)) {
		Error(Func, "Function missing return statement");
	}
}

void june::Analysis::CheckGenericFuncDecl(GenericFuncDecl* GenFunc, u32 BindingId) {
	// TODO: Probably don't want to reset if it has never been checked before.
	ResetGenericDecl(GenFunc);
	BindTypes(GenFunc, BindingId);
	CheckFuncDecl(GenFunc);
	UnbindTypes(GenFunc);
}

bool june::Analysis::TypeHasFieldsWithAssignment(Type* Ty) {
	if (Ty->GetKind() == TypeKind::RECORD) {
		RecordDecl* FieldRecord = Ty->AsRecordType()->Record;
		return FieldRecord->FieldsHaveAssignment;
	} else if (Ty->GetKind() == TypeKind::TUPLE) {
		TupleType* TupleTy = Ty->AsTupleType();
		for (Type* ValueTy : TupleTy->SubTypes) {
			if (TypeHasFieldsWithAssignment(ValueTy)) {
				return true;
			}
		}
	} else if (Ty->GetKind() == TypeKind::FIXED_ARRAY) {
		Type* BaseTy = Ty->AsFixedArrayType()->GetBaseType();
		return TypeHasFieldsWithAssignment(BaseTy);
	}
	return false;
}

void june::Analysis::CheckRecordsInType(SourceLoc ErrLoc, Type* Ty) {
	TypeKind K = Ty->GetKind();
	if (K == TypeKind::RECORD) {
		EnsureChecked(ErrLoc, Ty->AsRecordType()->Record);
	} else if (K == TypeKind::FIXED_ARRAY || K == TypeKind::POINTER) {
		CheckRecordsInType(ErrLoc, Ty->AsContainerType()->GetBaseType());
	} else if (Ty->GetKind() == TypeKind::TUPLE) {
		TupleType* TupleTy = Ty->AsTupleType();
		for (Type* ValueTy : TupleTy->SubTypes) {
			CheckRecordsInType(ErrLoc, ValueTy);
		}
	} else if (Ty->GetKind() == TypeKind::FUNCTION) {
		FunctionType* FuncTy = Ty->AsFunctionType();
		for (Type* ParamTy : FuncTy->ParamTypes) {
			CheckRecordsInType(ErrLoc, ParamTy);
		}
	}
}

bool june::Analysis::CheckInferedTypeAssignment(AstNode* Decl, Expr* Assignment) {
	if (Assignment->is(AstKind::NULLPTR)) {
		Error(Decl, "Cannot infer the type from a null assignment");
		return false;
	}

	if (Assignment->Ty->is(Context.UndefinedType)) {
		Error(Decl, "Cannot infer the type from an undefined type");
		return false;
	}

	return true;
}

void june::Analysis::CheckScope(const LexScope& LScope, Scope& NewScope) {
	NewScope.Parent = LocScope;
	LocScope = &NewScope;
	for (AstNode* Stmt : LScope.Stmts) {
		if (LocScope->FoundTerminal) {
			Error(Stmt, "Unreachable code");
			break;
		}

		if (Stmt->is(AstKind::FUNC_DECL)) {
			Error(Stmt, "Functions declared inside functions current not supported");
			continue;
		}

		if (Stmt->is(AstKind::RECORD_DECL)) {
			Error(Stmt, "records declared inside functions current not supported");
			continue;
		}

		// Ensuring that it is actually a valid statement.
		switch (Stmt->Kind) {
		case AstKind::FUNC_DECL:
		case AstKind::VAR_DECL:
		case AstKind::VAR_DECL_LIST:
		case AstKind::INNER_SCOPE:
		case AstKind::ELSE_SCOPE:
		case AstKind::RETURN:
		case AstKind::RANGE_LOOP:
		case AstKind::ITERATOR_LOOP:
		case AstKind::PREDICATE_LOOP:
		case AstKind::IF:
		case AstKind::FUNC_CALL:
		case AstKind::BREAK:
		case AstKind::CONTINUE:
		case AstKind::DELETE:
			break;
		case AstKind::BINARY_OP:
			switch (ocast<BinaryOp*>(Stmt)->Op) {
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
			case TokenKind::GT_GT_EQ:
				break;
			default:
				Error(Stmt, "Incomplete statement");
				continue;
			}
			break;
		case AstKind::UNARY_OP:
			switch (ocast<UnaryOp*>(Stmt)->Op) {
			case TokenKind::PLUS_PLUS:
			case TokenKind::POST_PLUS_PLUS:
			case TokenKind::MINUS_MINUS:
			case TokenKind::POST_MINUS_MINUS:
				break;
			default:
				Error(Stmt, "Incomplete statement");
				continue;
			}
			break;
		default:
			Error(Stmt, "Incomplete statement");
			continue;
		}

		CheckNode(Stmt);

	}
	LocScope = LocScope->Parent;
}

void june::Analysis::CheckNode(AstNode* Node) {
	switch (Node->Kind) {
	case AstKind::VAR_DECL:
		CheckVarDecl(ocast<VarDecl*>(Node));
		break;
	case AstKind::VAR_DECL_LIST:
		CheckVarDeclList(ocast<VarDeclList*>(Node));
		break;
	case AstKind::INNER_SCOPE:
	case AstKind::ELSE_SCOPE:
		CheckInnerScope(ocast<InnerScopeStmt*>(Node));
		break;
	case AstKind::RETURN:
		CheckReturn(ocast<ReturnStmt*>(Node));
		break;
	case AstKind::RANGE_LOOP:
		CheckRangeLoop(ocast<RangeLoopStmt*>(Node));
		break;
	case AstKind::ITERATOR_LOOP:
		CheckIteratorLoop(ocast<IteratorLoopStmt*>(Node));
		break;
	case AstKind::PREDICATE_LOOP:
		CheckPredicateLoop(ocast<PredicateLoopStmt*>(Node));
		break;
	case AstKind::IF:
		CheckIf(ocast<IfStmt*>(Node));
		break;
	case AstKind::CONTINUE:
	case AstKind::BREAK:
		CheckLoopControl(ocast<LoopControlStmt*>(Node));
		break;
	case AstKind::DELETE:
		CheckDelete(ocast<DeleteStmt*>(Node));
		break;
	case AstKind::IDENT_REF:
		CheckIdentRef(ocast<IdentRef*>(Node), false);
		break;
	case AstKind::FIELD_ACCESSOR:
		CheckFieldAccessor(ocast<FieldAccessor*>(Node), false);
		break;
	case AstKind::FUNC_CALL:
		CheckFuncCall(ocast<FuncCall*>(Node));
		break;
	case AstKind::BINARY_OP:
		CheckBinaryOp(ocast<BinaryOp*>(Node));
		break;
	case AstKind::UNARY_OP:
		CheckUnaryOp(ocast<UnaryOp*>(Node));
		break;
	case AstKind::NUMBER_LITERAL:
	case AstKind::NULLPTR:
	case AstKind::BOOL_LITERAL:
	case AstKind::SIZEOF_TYPE:
		// Already assigned a type during parsing!
		break;
	case AstKind::ARRAY:
		CheckArray(ocast<Array*>(Node));
		break;
	case AstKind::ARRAY_ACCESS:
		CheckArrayAccess(ocast<ArrayAccess*>(Node));
		break;
	case AstKind::TYPE_CAST:
		CheckTypeCast(ocast<TypeCast*>(Node));
		break;
	case AstKind::HEAP_ALLOC_TYPE:
		CheckHeapAllocType(ocast<HeapAllocType*>(Node));
		break;
	case AstKind::THIS_REF:
		CheckThisRef(ocast<ThisRef*>(Node));
		break;
	case AstKind::TERNARY_COND:
		CheckTernaryCond(ocast<TernaryCond*>(Node));
		break;
	case AstKind::TUPLE:
		CheckTuple(ocast<Tuple*>(Node));
		break;
	default:
		assert(!"Unimplemented node check");
		break;
	}
}

bool june::Analysis::CheckInnerScope(InnerScopeStmt* InnerScope) {
	Scope NewScope(InnerScope);
	CheckScope(InnerScope->Scope, NewScope);
	return NewScope.AllPathsReturn;
}

void june::Analysis::CheckVarDeclList(VarDeclList* DeclList) {
	if (DeclList->HasBeenChecked) return;
	DeclList->HasBeenChecked = true;

	FU      = DeclList->FU;
	CRecord = DeclList->Record;
	if (!CRecord) {
		Context.UncheckedDecls.erase(DeclList);
	}

	if (DeclList->Assignment) {

		CheckNode(DeclList->Assignment);

		if (DeclList->Assignment->Ty->is(Context.ErrorType)) {
			return;
		}

		if (DeclList->UsesInferedTypes) {
			if (!CheckInferedTypeAssignment(DeclList, DeclList->Assignment)) {
				return;
			}
		}

		if (!DeclList->UsesInferedTypes && !IsAssignableTo(DeclList->Ty, DeclList->Assignment)) {
			Error(DeclList, "Cannot assign value of type '%s' to a declaration list of type '%s'",
				DeclList->Assignment->Ty->ToStr(), DeclList->Ty->ToStr());
			return;
		}

		DeclList->Ty = DeclList->Assignment->Ty;
	}

	if (DeclList->Ty->GetKind() != TypeKind::TUPLE) {
		Error(DeclList, "Cannot decompose type '%s' into a list of assignments",
			DeclList->Ty->ToStr());
		return;
	}

	if (DeclList->Ty->GetKind() == TypeKind::TUPLE) {
		TupleType* TupleTy = DeclList->Ty->AsTupleType();
		if (TupleTy->SubTypes.size() != DeclList->Decls.size()) {
			Error(DeclList, "Cannot decompose a tuple of type '%s' into '%s' declarations",
				DeclList->Ty->ToStr(), DeclList->Decls.size());
			return;
		}
		
		// Assigning the types to the declarations and processing them
		for (u32 i = 0; i < DeclList->Decls.size(); i++) {
			VarDecl* Var = DeclList->Decls[i];
			Var->Ty = TupleTy->SubTypes[i];
			CheckVarDecl(Var);
		}
	}
}

void june::Analysis::CheckReturn(ReturnStmt* Ret) {
	LocScope->FoundTerminal  = true;
	LocScope->AllPathsReturn = true;

	if (CFunc->NumReturns == 1 && LocScope->Node != CFunc && LocScope->Node->isNot(AstKind::INNER_SCOPE)) {
		++CFunc->NumReturns;
	}

	if (Ret->Val) {
		CheckNode(Ret->Val);
		YIELD_ERROR_WHEN(Ret->Val);
	}

	Type* ERetTy = CFunc->RetTy;
	Type* RTy = Ret->Val ? Ret->Val->Ty : Context.VoidType;
	
	bool ReturnMatched = true;
	if (Ret->Val) {
		if (IsAssignableTo(ERetTy, Ret->Val)) {
			CreateCast(Ret->Val, ERetTy);
		} else {
			ReturnMatched = false;
		}
	} else {
		ReturnMatched = ERetTy->is(Context.VoidType);
	}

	if (!ReturnMatched) {
		Error(Ret, "Return Type '%s', expected '%s'",
			RTy->ToStr(), ERetTy->ToStr());
	}
}

void june::Analysis::CheckRangeLoop(RangeLoopStmt* Loop) {
	if (Loop->Decl) {
		CheckNode(Loop->Decl);	
	}
	if (Loop->Cond) {
		CheckCond(Loop->Cond, Loop->ExpandedCondLoc, "Loop");
	}
	if (Loop->Inc) {
		CheckNode(Loop->Inc);
	}
	
	++LoopDepth;
	Scope NewScope(Loop);
	CheckScope(Loop->Scope, NewScope);
	--LoopDepth;
}

void june::Analysis::CheckIteratorLoop(IteratorLoopStmt* Loop) {
	CheckNode(Loop->IterOnExpr);
	YIELD_ERROR_WHEN(Loop->IterOnExpr);

	if (Loop->IterOnExpr->Ty->GetKind() != TypeKind::FIXED_ARRAY) {
		Error(Loop->IterOnExpr, "Cannot iterate on type: %s", Loop->IterOnExpr->Ty->ToStr());
		return;
	}

	Loop->VarVal->Ty = Loop->IterOnExpr->Ty->AsFixedArrayType()->ElmTy;

	++LoopDepth;
	Scope NewScope(Loop);
	CheckScope(Loop->Scope, NewScope);
	--LoopDepth;
}

void june::Analysis::CheckPredicateLoop(PredicateLoopStmt* Loop) {
	if (Loop->Cond) {
		CheckCond(Loop->Cond, Loop->ExpandedCondLoc, "Loop");
	}
	
	++LoopDepth;
	Scope NewScope(Loop);
	CheckScope(Loop->Scope, NewScope);
	--LoopDepth;
}

bool june::Analysis::CheckIf(IfStmt* If) {
	CheckCond(If->Cond, If->ExpandedCondLoc, "If");

	Scope IfBodyScope(If);
	CheckScope(If->Scope, IfBodyScope);
	bool AllPathsReturn = If->Else && IfBodyScope.AllPathsReturn;

	if (If->Else) {
		CheckNode(If->Else);
		if (If->Else->is(AstKind::IF)) {
			AllPathsReturn &= CheckIf(ocast<IfStmt*>(If->Else));
		} else {
			AllPathsReturn &= CheckInnerScope(ocast<InnerScopeStmt*>(If->Else));
		}
	}

	LocScope->AllPathsReturn = AllPathsReturn;
	LocScope->FoundTerminal |= AllPathsReturn;

	return AllPathsReturn;
}

void june::Analysis::CheckCond(Expr* Cond, SourceLoc ExpandedCondLoc, const c8* PreText) {
	CheckNode(Cond);
	if (Cond->Ty->isNot(Context.ErrorType)) {
		if (!IsComparable(Cond->Ty)) {
			Error(ExpandedCondLoc,
				"%s condition expected to be type 'bool', but found type '%s'",
				PreText, Cond->Ty->ToStr());
		}
	}
}

void june::Analysis::CheckLoopControl(LoopControlStmt* LoopControl) {
	
	LocScope->FoundTerminal = true;

	if (LoopDepth == 0) {
		if (LoopControl->Kind == AstKind::BREAK) {
			Error(LoopControl, "break statements may only be used inside of loops");
			return;
		} else {
			Error(LoopControl, "continue statements may only be used inside of loops");
			return;
		}
	}

	if (LoopControl->LoopCount > LoopDepth) {
		if (LoopControl->Kind == AstKind::BREAK) {
			Error(LoopControl, "number of requested breaks exceeds the loop depth");
		} else {
			Error(LoopControl, "number of requested continues exceeds the loop depth");
		}
	}
}

void june::Analysis::CheckDelete(DeleteStmt* Delete) {
	CheckNode(Delete->Val);
	YIELD_ERROR_WHEN(Delete->Val);

	if (Delete->Val->Ty->GetKind() != TypeKind::POINTER) {
		Error(Delete, "Cannot delete type '%s'", Delete->Val->Ty->ToStr());
	}
}

void june::Analysis::CheckIdentRef(IdentRef* IRef, bool GivePrefToFuncs) {
	CheckIdentRefCommon(IRef, GivePrefToFuncs, FU, nullptr);
}

void june::Analysis::CheckIdentRefCommon(IdentRef* IRef, bool GivePrefToFuncs, FileUnit* FUToLookup, RecordDecl* RecordToLookup) {
	assert(((u64)FUToLookup ^ (u64)RecordToLookup) && "Cannot lookup info in a file unit and a record at the same time!");
	
	auto SearchForFuncs = [&]() {
		if (FUToLookup) {
			// File unit exist so looking in global scope.
			auto it = FUToLookup->GlobalFuncs.find(IRef->Ident);
			if (it != FUToLookup->GlobalFuncs.end()) {
				IRef->FuncsRef = &it->second;
				IRef->RefKind  = IdentRef::FUNCS;
				return;
			}
			// Relative member function.
			if (CRecord) {
				auto it = CRecord->Funcs.find(IRef->Ident);
				if (it != CRecord->Funcs.end()) {
					IRef->FuncsRef = &it->second;
					IRef->RefKind  = IdentRef::FUNCS;
				}
			}
			// Searching in the global using imports.
			if (FUToLookup == FU && IRef->RefKind == IdentRef::NOT_FOUND) {
				for (FileUnit* GlobalFU : FU->GlobalUsingImports) {
					auto it = GlobalFU->GlobalFuncs.find(IRef->Ident);
					if (it != GlobalFU->GlobalFuncs.end()) {
						IRef->FuncsRef = &it->second;
						IRef->RefKind  = IdentRef::FUNCS;
					}
				}
			}
		} else {
			// Looking for member function.
			auto it = RecordToLookup->Funcs.find(IRef->Ident);
			if (it != RecordToLookup->Funcs.end()) {
				IRef->FuncsRef = &it->second;
				IRef->RefKind  = IdentRef::FUNCS;
			}
		}
	};

	auto SearchForVars = [&]() {
		if (FUToLookup) {
			if (CRecord) {
				auto it = CRecord->Fields.find(IRef->Ident);
				if (it != CRecord->Fields.end()) {
					IRef->VarRef  = it->second;
					IRef->RefKind = IdentRef::VAR;
				}
			}
			if (IRef->RefKind == IdentRef::NOT_FOUND) {
				// Still not found then searching the global
				// variables
				auto it = FUToLookup->GlobalVars.find(IRef->Ident);
				if (it != FUToLookup->GlobalVars.end()) {
					IRef->VarRef  = it->second;
					IRef->RefKind = IdentRef::VAR;
				}
			}
			// Searching in the global using imports.
			if (FUToLookup == FU && IRef->RefKind == IdentRef::NOT_FOUND) {
				for (FileUnit* GlobalFU : FU->GlobalUsingImports) {
					auto it = GlobalFU->GlobalVars.find(IRef->Ident);
					if (it != GlobalFU->GlobalVars.end()) {
						IRef->VarRef  = it->second;
						IRef->RefKind = IdentRef::VAR;
					}
				}
			}
		} else {
			// Searching for a field in the record.
			auto it = RecordToLookup->Fields.find(IRef->Ident);
			if (it != RecordToLookup->Fields.end()) {
				IRef->VarRef  = it->second;
				IRef->RefKind = IdentRef::VAR;
			}
		}
	};

	// If it expects a function then we search the
	// function first otherwise we search for a variable
	// first.
	if (GivePrefToFuncs && IRef->RefKind == IdentRef::NOT_FOUND) {
		SearchForFuncs();
	} else if (IRef->RefKind == IdentRef::NOT_FOUND) {
		SearchForVars();
	}

	// Checking if it refers to a file unit
	if (IRef->RefKind == IdentRef::NOT_FOUND && FUToLookup == FU) {
		auto ImportIt = FU->Imports.find(IRef->Ident);
		if (ImportIt != FU->Imports.end()) {
			IRef->FileUnitRef = ImportIt->second;
			IRef->RefKind     = IdentRef::FILE_UNIT;
		}
	}

	// Checking if it refers to a record
	if (IRef->RefKind == IdentRef::NOT_FOUND) {
		if (FUToLookup /* == FU */) {
			RecordLocation RecLoc = RecordLocation::CreateRecLocationByRecName(IRef->Ident);
			auto it = FU->Records.find(RecLoc);
			if (it != FU->Records.end()) {
				IRef->RecordRef = it->second;
				IRef->RefKind   = IdentRef::RECORD;
			}
			if (IRef->RefKind == IdentRef::NOT_FOUND) {
				for (FileUnit* GlobalFU : FU->GlobalUsingImports) {
					auto it = GlobalFU->Records.find(RecLoc);
					if (it != GlobalFU->Records.end()) {
						IRef->RecordRef = it->second;
						IRef->RefKind   = IdentRef::RECORD;
					}
				}
			}
		} else {
			// Search for a record inside another record.
			RecordLocation RecLoc = RecordLocation::CreateRecLocationByRecord(RecordToLookup);
			RecLoc.Nesting.push_back(IRef->Ident);
			auto it = RecordToLookup->FU->Records.find(RecLoc);
			if (it != RecordToLookup->FU->Records.end()) {
				IRef->RecordRef = it->second;
				IRef->RefKind   = IdentRef::RECORD;
			}
		}
	}

	// Reverse order of the first case.
	if (GivePrefToFuncs && IRef->RefKind == IdentRef::NOT_FOUND) {
		SearchForVars();
	} else if (IRef->RefKind == IdentRef::NOT_FOUND) {
		SearchForFuncs();
	}

	IRef->IsFoldable = false;

	switch (IRef->RefKind) {
	case IdentRef::VAR: {
		VarDecl* Var = IRef->VarRef;

		EnsureChecked(IRef->Loc, Var);

		if (!(Var->Mods & mods::Mods::COMPTIME)) {
			IRef->IsComptimeCompat = false;
		} else {
			IRef->IsFoldable = true;
		}

		IRef->Ty = Var->Ty;

		CheckRecordsInType(IRef->Loc, Var->Ty);
		if (Var->MemoryWasMoved) {
			Log.BeginError(IRef->Loc, "Cannot use variable '%s' after its memory was moved");
			AddMarkErrorMsgAboutBindLoc();
			Log.AddMarkErrorMsg(Var->MemoryMovedLoc, "Value moved here");
			Log.EndError();
		}

		break;
	}
	case IdentRef::FUNCS: {
		FuncDecl* Func = (*IRef->FuncsRef)[0];
		IRef->Ty = Func->RetTy;

		if (!(Func->Mods & mods::Mods::COMPTIME)) {
			IRef->IsComptimeCompat = false;
		}

		break;
	}
	case IdentRef::FILE_UNIT:
		IRef->Ty = Context.UndefinedType;
		break;
	case IdentRef::RECORD: {
		IRef->Ty = GetRecordType(IRef->RecordRef);
		break;
	case IdentRef::NOT_FOUND:
		if (!GivePrefToFuncs) {
			Error(IRef, "Could not find symbol for %s: '%s'",
				(RecordToLookup ? "field" : "identifier"), IRef->Ident);
		} else {
			Error(IRef, "Could not find function for identifier '%s'", IRef->Ident);
		}
		YIELD_ERROR(IRef);
	}
	}
}

void june::Analysis::CheckFieldAccessor(FieldAccessor* FA, bool GivePrefToFuncs) {
	
	Expr* Site = FA->Site;

	CheckNode(Site);
	YIELD_ERROR_WHEN_M(FA, Site);

	// Variable cases checked early.
	if (Site->Kind == AstKind::FUNC_CALL    ||
		Site->Kind == AstKind::ARRAY_ACCESS ||
		Site->Kind == AstKind::THIS_REF     ||
		((Site->Kind == AstKind::IDENT_REF ||
		  Site->Kind == AstKind::FIELD_ACCESSOR
			) && ocast<IdentRef*>(Site)->RefKind == IdentRef::VAR)
		) {

		// Checking for .length operator
		if (Site->Ty->GetKind() == TypeKind::FIXED_ARRAY) {
			if (FA->Ident == Context.LengthIdentifier) {
				FA->IsArrayLength = true;
				FA->Ty = Context.U32Type;
				return;
			}
		}

		// Must be an attempt to access a field/function of a variable
		if (!(Site->Ty->GetKind() == TypeKind::RECORD ||
			(Site->Ty->GetKind() == TypeKind::POINTER &&
				Site->Ty->AsPointerType()->ElmTy->GetKind() == TypeKind::RECORD))
			) {
			Error(FA, "Cannot access field of type '%s'", Site->Ty->ToStr());
			YIELD_ERROR(FA);
		}

		RecordDecl* Record = Site->Ty->GetKind() == TypeKind::RECORD ? Site->Ty->AsRecordType()->Record
			                                                         : Site->Ty->AsPointerType()->ElmTy->AsRecordType()->Record;
		CheckRecordsInType(FA->Loc, Site->Ty);
		CheckIdentRefCommon(FA, GivePrefToFuncs, nullptr, Record);
	
		return;
	}

	switch (Site->Kind) {
	case AstKind::IDENT_REF:
	case AstKind::FIELD_ACCESSOR: {
		IdentRef* IRef = ocast<IdentRef*>(Site);
		switch (IRef->RefKind) {
		case IdentRef::FILE_UNIT:
			CheckIdentRefCommon(FA, GivePrefToFuncs, IRef->FileUnitRef, nullptr);
			break;
		case IdentRef::RECORD:
			CheckIdentRefCommon(FA, GivePrefToFuncs, nullptr, IRef->RecordRef);
			break;
		default:
			assert(!"unimplemented!");
			break;
		}
		break;
	}
	default:
		assert(!"Failed to implement field accessor site case");
		break;
	}

}

void june::Analysis::CheckFuncCall(FuncCall* Call) {
	
	Call->IsFoldable = false;
	Call->IsComptimeCompat = false; // TODO: Allow for comptime functions

	// Checking arguments
	bool ArgsHaveErrs = false;
	for (Expr* Arg : Call->Args) {
		CheckNode(Arg);
		if (Arg->Ty->is(Context.ErrorType)) {
			ArgsHaveErrs = true;
		}
	}
	for (FuncCall::NamedArg& NamedArg : Call->NamedArgs) {
		CheckNode(NamedArg.AssignValue);
		if (NamedArg.AssignValue->Ty->is(Context.ErrorType)) {
			ArgsHaveErrs = true;
		}
	}

	if (ArgsHaveErrs) {
		YIELD_ERROR(Call);
	}

	switch (Call->Site->Kind) {
	case AstKind::IDENT_REF:
		CheckIdentRef(ocast<IdentRef*>(Call->Site), true);
		break;
	case AstKind::FIELD_ACCESSOR:
		CheckFieldAccessor(ocast<FieldAccessor*>(Call->Site), true);
		break;
	default:
		CheckNode(Call->Site);
		break;
	}
	YIELD_ERROR_WHEN_M(Call, Call->Site);

	FuncsList* Canidates = nullptr;
	RecordDecl* ConstructorRecord = nullptr;

	Expr* Site = Call->Site;

	if (Site->Kind == AstKind::FUNC_CALL    ||
		Site->Kind == AstKind::ARRAY_ACCESS ||
		Site->Kind == AstKind::THIS_REF     ||
		((Site->Kind == AstKind::IDENT_REF ||
			Site->Kind == AstKind::FIELD_ACCESSOR
			) && ocast<IdentRef*>(Site)->RefKind == IdentRef::VAR)
		) {
		// Call on a variable.
		if (Site->Ty->GetKind() != TypeKind::FUNCTION) {
			Error(Call, "Cannot make a call on a variable that does not have a function type");
			YIELD_ERROR(Call);
		}

		FunctionType* CalledFuncTy = Site->Ty->AsFunctionType();
		if (!Call->NamedArgs.empty()) {
			Error(Call, "Cannot have named arguments for a call on a variable");
			YIELD_ERROR(Call);
		}

		bool ValidCallArgs = true;
		if (Call->Args.size() != CalledFuncTy->ParamTypes.size()) {
			ValidCallArgs = false;
		} else {
			for (u32 i = 0; i < Call->Args.size(); i++) {
				if (!IsAssignableTo(CalledFuncTy->ParamTypes[i], Call->Args[i])) {
					ValidCallArgs = false;
					break;
				}
			}
		}

		if (!ValidCallArgs) {
			std::string FuncDef = "(";
			for (u32 i = 0; i < Call->Args.size(); i++) {
				FuncDef += Call->Args[i]->Ty->ToStr();
				if (i + 1 != Call->Args.size()) FuncDef += ", ";
			}
			FuncDef += ")";


			Error(Call, "Invalid arguments for call. Expected '%s' but found '%s'",
				CalledFuncTy->ArgsToStr(), FuncDef);
			YIELD_ERROR(Call);
		}

		for (u32 i = 0; i < Call->Args.size(); i++) {
			AssignTo(Call->Args[i], CalledFuncTy->ParamTypes[i], Call->Loc);
		}

		Call->Ty = CalledFuncTy->RetTy;
		return;
	}

	if (Site->Kind == AstKind::IDENT_REF || Site->Kind == AstKind::FIELD_ACCESSOR) {
		IdentRef* IRef = ocast<IdentRef*>(Site);
		switch (IRef->RefKind) {
		case IdentRef::FUNCS:
			Canidates = IRef->FuncsRef;
			break;
		case IdentRef::FILE_UNIT: {
			RecordLocation RecLoc = RecordLocation::CreateRecLocationByRecName(IRef->Ident);
			auto it = IRef->FileUnitRef->Records.find(RecLoc);
			if (it != IRef->FileUnitRef->Records.end()) {
				ConstructorRecord = it->second;
			} else {
				Error(Call, "File '%s' does not have a primary record",
					IRef->FileUnitRef->FL.PathKey);
				YIELD_ERROR(Call);
			}

			Call->IsConstructorCall = true;
			Canidates = &ConstructorRecord->Constructors;
			break;
		}
		case IdentRef::RECORD:
			Call->IsConstructorCall = true;
			ConstructorRecord = ocast<IdentRef*>(Call->Site)->RecordRef;
			Canidates = &ConstructorRecord->Constructors;
			break;
		default:
			break;
		}
	} else if (Site->Kind == AstKind::HEAP_ALLOC_TYPE) {
		HeapAllocType* HeapAlloc = ocast<HeapAllocType*>(Site);
		if (HeapAlloc->TypeToAlloc->GetKind() == TypeKind::RECORD) {
			Call->IsConstructorCall = true;
			ConstructorRecord = HeapAlloc->TypeToAlloc->AsRecordType()->Record;
			Canidates = &ConstructorRecord->Constructors;
		} else {
			Error(Call, "Cannot make a heap allocation call for type '%s'",
				HeapAlloc->TypeToAlloc->ToStr());
			YIELD_ERROR(Call);
		}
	}

	if (ConstructorRecord) {
		EnsureChecked(Call->Loc, ConstructorRecord);
	}
	
	if (Call->IsConstructorCall && Canidates->empty()) {
		CheckDefaultRecordInitFuncCall(Call, ConstructorRecord);
		return;
	}

	FuncDecl* CalledFunc = nullptr;
	if (Call->NamedArgs.empty()) {
		CalledFunc = FindBestFuncCallCanidate(Canidates, Call);
	} else {
		CalledFunc = FindBestFuncCallCanidateWithNamedArgs(Canidates, Call);
	}

	if (!CalledFunc) {
		std::string FuncDef = "";
		if (Call->Site->is(AstKind::IDENT_REF) || Call->Site->is(AstKind::FIELD_ACCESSOR)) {
			FuncDef += ocast<IdentRef*>(Call->Site)->Ident.Text;
		}

		FuncDef += "(";
		for (u32 i = 0; i < Call->Args.size(); i++) {
			FuncDef += Call->Args[i]->Ty->ToStr();
			if (i + 1 != Call->Args.size()) FuncDef += ", ";
		}
		for (FuncCall::NamedArg& NamedArg : Call->NamedArgs) {
			FuncDef += ", " + NamedArg.Name.Text.str() + "=" + NamedArg.AssignValue->Ty->ToStr();
		}
		FuncDef += ")";

		std::string ftype = "function";
		Error(Call,
			"Could not find overloaded %s for definition: '%s'",
			ftype,
			FuncDef);
		if (Canidates && Canidates->size() == 1) {
			FuncDecl* OnlyFunc = (*Canidates)[0];
			std::string OptFuncDef = std::string(OnlyFunc->Name.Text);
			if (OnlyFunc->is(AstKind::GENERIC_FUNC_DECL)) {
				GenericFuncDecl* GenFunc = ocast<GenericFuncDecl*>(OnlyFunc);
				OptFuncDef += "<";
				u32 Count = 0;
				for (auto [GenericName, _] : GenFunc->GenericTypes) {
					OptFuncDef += GenericName.Text.str();
					if (++Count != GenFunc->GenericTypes.size())
						OptFuncDef += ",";
				}
				OptFuncDef += ">";
			}
			OptFuncDef += + "(";
			for (u32 i = 0; i < OnlyFunc->Params.size(); i++) {
				OptFuncDef += OnlyFunc->Params[i]->Ty->ToStr();
				if (i + 1 != OnlyFunc->Params.size()) OptFuncDef += ", ";
			}
			OptFuncDef += ")";

			Log.Note("Did you mean to call %s '%s'",
				ftype, OptFuncDef).EndNote();
		}

		YIELD_ERROR(Call);
	}

	TypeBindList TypeBindings;

	if (CalledFunc->is(AstKind::GENERIC_FUNC_DECL)) {
		TypeBindings.OriginalBindingLoc = Call->Loc;
		TypeBindings.OriginalFileFU = FU;
		if (CFunc->is(AstKind::GENERIC_FUNC_DECL)) {
			GenericFuncDecl* GenFunc = ocast<GenericFuncDecl*>(CFunc);
			TypeBindings.RecursiveCallGenericFunc = GenFunc;
			TypeBindings.RecursiveCallBindingId   = GenFunc->CurBindingId;
		}
		
		GenericFuncDecl* GenFunc = ocast<GenericFuncDecl*>(CalledFunc);
		TypeBindings.List.reserve(GenFunc->GenericTypes.size());

		// Generating the type bindings.
		for (u32 i = 0; i < Call->Args.size(); i++) {
			Type* ParamTy = CalledFunc->Params[i]->Ty;
			if (ParamTy->isGeneric()) {
				GenericType* GenTy = ParamTy->AsGenericType();
				if (!IsGenericTypeNameBound(TypeBindings, GenTy->Name)) {
					// Unboxing is good here since if the function being called from
					// has generics those types should already have been binded during
					// its check.
					TypeBindings.List.push_back(
						std::make_tuple(GenTy->Name, Call->Args[i]->Ty->UnboxGeneric()));
				}
			}
		}
		for (FuncCall::NamedArg& NamedArg : Call->NamedArgs) {
			Type* ParamTy = CalledFunc->Params[NamedArg.VarRef->ParamIdx]->Ty;
			if (ParamTy->isGeneric()) {
				GenericType* GenTy = ParamTy->AsGenericType();
				if (!IsGenericTypeNameBound(TypeBindings, GenTy->Name)) {
					TypeBindings.List.push_back(
						std::make_tuple(GenTy->Name, NamedArg.AssignValue->Ty->UnboxGeneric()));
				}
			}
		}

		if (TypeBindings.List.size() != GenFunc->GenericTypes.size()) {
			// There are unbound types.
			std::string UnboundTypesNames = "";
			for (auto [GenName, GenType] : GenFunc->GenericTypes) {
				if (!IsGenericTypeNameBound(TypeBindings, GenName)) {
					if (!UnboundTypesNames.empty()) {
						UnboundTypesNames += ", ";
					}
					UnboundTypesNames += GenName.Text.str();
				}
			}
			Error(Call, "Call to generic function did not bind all the generic types. Missing bindings for: [ %s ]",
				UnboundTypesNames);
			YIELD_ERROR(Call);
		}

		Call->TypeBindingId = Context.RequestGen(TypeBindings, GenFunc);

		// Have to temporarily bind the types
		// properly create casting.
		BindTypes(GenFunc, Call->TypeBindingId);
	}

	// TODO: VarArgs will require further work to get this to work right
	// Ensuring that the arguments comply with the function
	for (u32 i = 0; i < Call->Args.size(); i++) {
		AssignTo(Call->Args[i], CalledFunc->Params[i]->Ty->UnboxGeneric(), Call->Loc);
	}
	for (FuncCall::NamedArg& NamedArg : Call->NamedArgs) {
		AssignTo(NamedArg.AssignValue, CalledFunc->Params[NamedArg.VarRef->ParamIdx]->Ty->UnboxGeneric(), Call->Loc);
	}

	if (!Call->IsConstructorCall) {
		Call->Ty = CalledFunc->RetTy->UnboxGeneric();
	} else {
		Call->Ty = GetRecordType(ConstructorRecord);
		if (Call->Site->is(AstKind::HEAP_ALLOC_TYPE)) {
			Call->Ty = PointerType::Create(Call->Ty, Context);
		}
	}

	Call->CalledFunc = CalledFunc;
	if (!CalledFunc->is(AstKind::GENERIC_FUNC_DECL)) {		
		Context.RequestGen(CalledFunc);
	} else {
		UnbindTypes(ocast<GenericFuncDecl*>(CalledFunc));
	}

	CheckRecordsInType(Call->Loc, Call->Ty);
}

void june::Analysis::CheckDefaultRecordInitFuncCall(FuncCall* Call, RecordDecl* Record) {
	// Can still "call" a default generated constructor.

	if (Call->Args.size() + Call->NamedArgs.size() > Record->Fields.size()) {
		Error(Call, "Too many arguments to initialize record");
		YIELD_ERROR(Call);
	}

	std::unordered_set<u32> ConsumedArgs;
	bool FieldTypeMismatch = false;
	for (u32 i = 0; i < Call->Args.size(); i++) {
		ConsumedArgs.insert(i);
		if (!IsAssignableTo(Record->FieldsByIdxOrder[i]->Ty, Call->Args[i])) {
			Error(Call, "Type of Value '%s', expected '%s' for field '%s'",
				Call->Args[i]->Ty->ToStr(),
				Record->FieldsByIdxOrder[i]->Ty->ToStr(),
				Record->FieldsByIdxOrder[i]->Name);
			FieldTypeMismatch = true;
		}
	}

	if (FieldTypeMismatch) {
		YIELD_ERROR(Call);
	}

	bool CanidateHasNameSlotTaken = false;
	for (FuncCall::NamedArg& NamedArg : Call->NamedArgs) {
		auto it = Record->Fields.find(NamedArg.Name);
		if (it != Record->Fields.end()) {
			u32 FieldIdx = it->second->FieldIdx;
			if (ConsumedArgs.find(FieldIdx) != ConsumedArgs.end()) {
				CanidateHasNameSlotTaken = true;
			}
			NamedArg.VarRef = it->second;
			ConsumedArgs.insert(FieldIdx);
		} else {
			Error(NamedArg.Loc, "No field in record '%s' by name '%s'",
				Record->Name, NamedArg.Name.Text);
			continue;
		}
	}

	if (CanidateHasNameSlotTaken) {
		DisplayErrorForNamedArgsSlotTaken(Call, true);
	}

	for (u32 i = 0; i < Call->Args.size(); i++) {
		CreateCast(Call->Args[i], Record->FieldsByIdxOrder[i]->Ty);
	}
	for (FuncCall::NamedArg& NamedArg : Call->NamedArgs) {
		CreateCast(NamedArg.AssignValue, Record->FieldsByIdxOrder[NamedArg.VarRef->FieldIdx]->Ty);
	}

	Call->Ty = GetRecordType(Record);
	if (Call->Site->is(AstKind::HEAP_ALLOC_TYPE)) {
		Call->Ty = PointerType::Create(Call->Ty, Context);
	}
}

void june::Analysis::DisplayErrorForNamedArgsSlotTaken(FuncCall* Call, bool UseFieldIdx) {
	// The slot may be taken because there is a duplicate
	// name or because the name was consumed by the
	// non-named arguments.
	for (u32 i = 0; i < Call->NamedArgs.size(); i++) {
		VarDecl* ParamOrField = Call->NamedArgs[i].VarRef;
		if ((UseFieldIdx ? ParamOrField->FieldIdx : ParamOrField->ParamIdx) < Call->Args.size()) {
			Error(Call, "Named argument '%s' already consumed by non-named argument",
				Call->NamedArgs[i].Name);
		}

		for (u32 j = i+1; j < Call->NamedArgs.size(); j++) {
			if (Call->NamedArgs[i].Name == Call->NamedArgs[j].Name) {
				Error(Call, "Duplicate named argument '%s'", Call->NamedArgs[i].Name);
			}
		}
	}
}

june::FuncDecl* june::Analysis::FindBestFuncCallCanidate(FuncsList* Canidates, FuncCall* Call) {
	if (!Canidates) return nullptr;

	u32 LeastConflicts = std::numeric_limits<u32>::max();
	s32 SelectionIndex = -1;

	llvm::SmallVector<std::tuple<FuncDecl*, u32>> GenericFuncs;
	for (u32 i = 0; i < Canidates->size(); i++) {
		FuncDecl* Canidate = (*Canidates)[i];
		
		if (Canidate->is(AstKind::GENERIC_FUNC_DECL)) {
			GenericFuncs.push_back(std::make_tuple(Canidate, i));
			continue;
		}

		u32 NumConflicts = 0;
		if (!CompareAsCanidate<false>(Call, Canidate, NumConflicts)) {
			continue;
		}

		if (NumConflicts < LeastConflicts) {
			LeastConflicts = NumConflicts;
			SelectionIndex = i;
		}
	}

	if (!GenericFuncs.empty() && SelectionIndex == -1) {
		for (u32 i = 0; i < GenericFuncs.size(); i++) {
			FuncDecl* Canidate = std::get<0>(GenericFuncs[i]);

			u32 NumConflicts = 0;
			if (!CompareAsCanidate<true>(Call, Canidate, NumConflicts)) {
				continue;
			}

			if (NumConflicts < LeastConflicts) {
				LeastConflicts = NumConflicts;
				SelectionIndex = std::get<1>(GenericFuncs[i]);
			}
		}
	}

	if (SelectionIndex == -1) {
		return nullptr;
	}
	
	return (*Canidates)[SelectionIndex];
}

template<bool IsGenericFuncT>
bool june::Analysis::CompareAsCanidate(FuncCall* Call, FuncDecl* Canidate, u32& NumConflicts) {
	if (Canidate->Params.size() != Call->Args.size()) return false;

	bool ArgsAssignable = true;
	// TODO: VarArgs will require further work to get this to work right
	for (u32 i = 0; i < Call->Args.size(); i++) {
		if constexpr (IsGenericFuncT) {
			if (Canidate->Params[i]->Ty->isGeneric()) {
				// TODO: In the future check generic restrictions
				continue;
			}
		}

		if (!IsAssignableTo(Canidate->Params[i]->Ty, Call->Args[i])) {
			ArgsAssignable = false;
			break;
		}
	}
	if (!ArgsAssignable) return false;

	// Finding the function with the least conflicts
	// TODO: VarArgs will require further work to get this to work right
	for (u32 i = 0; i < Call->Args.size(); i++) {
		if constexpr (IsGenericFuncT) {
			if (Canidate->Params[i]->Ty->isGeneric()) {
				continue;
			}
		}

		if (Call->Args[i]->Ty
			->isNot(Canidate->Params[i]->Ty)) {
			++NumConflicts;
		}
	}

	return true;
}

template bool june::Analysis::CompareAsCanidate<true>
	(FuncCall* Call, FuncDecl* Canidate, u32& NumConflicts);
template bool june::Analysis::CompareAsCanidate<false>
	(FuncCall* Call, FuncDecl* Canidate, u32& NumConflicts);

june::FuncDecl* june::Analysis::FindBestFuncCallCanidateWithNamedArgs(FuncsList* Canidates, FuncCall* Call) {
	if (!Canidates) return nullptr;

	u32 LeastConflicts = std::numeric_limits<u32>::max();
	s32 SelectionIndex = -1;

	bool CanidateHasNameSlotTaken = false;

	llvm::SmallVector<std::tuple<FuncDecl*, u32>> GenericFuncs;
	for (u32 i = 0; i < Canidates->size(); i++) {
		FuncDecl* Canidate = (*Canidates)[i];
		
		if (Canidate->is(AstKind::GENERIC_FUNC_DECL)) {
			GenericFuncs.push_back(std::make_tuple(Canidate, i));
			continue;
		}

		u32 NumConflicts = 0;
		if (!CompareAsNamedArgCandiate<false>(Call, Canidate, NumConflicts, CanidateHasNameSlotTaken)) {
			continue;
		}

		if (NumConflicts < LeastConflicts) {
			LeastConflicts = NumConflicts;
			SelectionIndex = i;
		}
	}

	if (!GenericFuncs.empty() && SelectionIndex == -1) {
		for (u32 i = 0; i < GenericFuncs.size(); i++) {
			FuncDecl* Canidate = std::get<0>(GenericFuncs[i]);

			u32 NumConflicts = 0;
			if (!CompareAsNamedArgCandiate<true>(Call, Canidate, NumConflicts, CanidateHasNameSlotTaken)) {
				continue;
			}

			if (NumConflicts < LeastConflicts) {
				LeastConflicts = NumConflicts;
				SelectionIndex = std::get<1>(GenericFuncs[i]);
			}
		}
	}

	if (SelectionIndex == -1) {
		return nullptr;
	}
	
	if (CanidateHasNameSlotTaken) {
		DisplayErrorForNamedArgsSlotTaken(Call, false);
	}

	return (*Canidates)[SelectionIndex];
}


template<bool IsGenericFuncT>
bool june::Analysis::CompareAsNamedArgCandiate(FuncCall* Call, FuncDecl* Canidate, u32& NumConflicts, bool& CanidateHasNameSlotTaken) {
	
	CanidateHasNameSlotTaken = false;
	
	if (Canidate->Params.size() != Call->Args.size() + Call->NamedArgs.size()) return false;
	
	std::unordered_set<u32> ConsumedArgs;
	for (u32 i = 0; i < Call->Args.size(); i++) {
		ConsumedArgs.insert(i);

		if constexpr (IsGenericFuncT) {
			if (Canidate->Params[i]->Ty->isGeneric()) {
				// TODO: In the future check generic restrictions
				continue;
			}
		}

		if (!IsAssignableTo(Canidate->Params[i]->Ty, Call->Args[i])) {
			return false;
		}
	}

	for (FuncCall::NamedArg& NamedArg : Call->NamedArgs) {
		for (u32 i = 0; i < Canidate->Params.size(); i++) {
			VarDecl* Param = Canidate->Params[i];
			if (NamedArg.Name == Param->Name) {

				if constexpr (IsGenericFuncT) {
					if (Canidate->Params[i]->Ty->isGeneric()) {
						// TODO: In the future check generic restrictions
					} else  if (!IsAssignableTo(Param->Ty, NamedArg.AssignValue)) {
						return false;
					}
				} else {
					if (!IsAssignableTo(Param->Ty, NamedArg.AssignValue)) {
						return false;
					}
				}

				if (ConsumedArgs.find(i) != ConsumedArgs.end()) {
					CanidateHasNameSlotTaken = true;
				}
				NamedArg.VarRef = Param;
				ConsumedArgs.insert(i);
				break; // Found name no reason to continue searching
					    // the rest of the arguments.
			}
		}
		if (!NamedArg.VarRef) {
			// Could not find a variable by the given
			// name so just moving on to the next canidate.
			return false;
		}
	}

	// Finding the function with the least conflicts
	for (u32 i = 0; i < Call->Args.size(); i++) {
		if constexpr (IsGenericFuncT) {
			if (Canidate->Params[i]->Ty->isGeneric()) {
				continue;
			}
		}

		if (Call->Args[i]->Ty
			->isNot(Canidate->Params[i]->Ty)) {
			++NumConflicts;
		}
	}
	for (FuncCall::NamedArg& NamedArg : Call->NamedArgs) {
		if constexpr (IsGenericFuncT) {
			if (NamedArg.VarRef->Ty->isGeneric()) {
				continue;
			}
		}

		if (NamedArg.AssignValue->Ty
			->isNot(NamedArg.VarRef->Ty)) {
			++NumConflicts;
		}
	}

	return true;
}

template bool june::Analysis::CompareAsNamedArgCandiate<true>
	(FuncCall* Call, FuncDecl* Canidate, u32& NumConflicts, bool& CanidateHasNameSlotTaken);
template bool june::Analysis::CompareAsNamedArgCandiate<false>
	(FuncCall* Call, FuncDecl* Canidate, u32& NumConflicts, bool& CanidateHasNameSlotTaken);


void june::Analysis::CheckBinaryOp(BinaryOp* BinOp) {
	CheckNode(BinOp->LHS);
	CheckNode(BinOp->RHS);

	Type* LTy = BinOp->LHS->Ty;
	Type* RTy = BinOp->RHS->Ty;

	if (LTy->is(Context.ErrorType) || RTy->is(Context.ErrorType)) {
		YIELD_ERROR(BinOp);
	}

	if (!BinOp->LHS->IsFoldable || !BinOp->RHS->IsFoldable) {
		BinOp->IsFoldable = false;
	}

	if (!BinOp->LHS->IsComptimeCompat || !BinOp->RHS->IsComptimeCompat) {
		BinOp->IsComptimeCompat = false;
	}

#define OPERATOR_CANNOT_APPLY(T)                              \
Error(BinOp,                                                  \
	"Operator '%s' cannot apply to type '%s'",                \
	GetTokenKindPresentation(BinOp->Op, Context), T->ToStr()); \
YIELD_ERROR(BinOp)

	switch (BinOp->Op) {
	case '=':
	case TokenKind::PLUS_EQ: case TokenKind::MINUS_EQ: case TokenKind::STAR_EQ: case TokenKind::SLASH_EQ:
	case TokenKind::MOD_EQ: case TokenKind::AMP_EQ:
	case TokenKind::CRT_EQ: case TokenKind::BAR_EQ:
	case TokenKind::LT_LT_EQ: case TokenKind::GT_GT_EQ: {

		if (!IsLValue(BinOp->LHS)) {
			Error(BinOp->LHS, "Expected to be a modifiable variable");
			YIELD_ERROR(BinOp);
		}

		if (BinOp->IsComptimeCompat) {
			Error(BinOp->LHS, "Cannot modify a variable marked with comptime");
			YIELD_ERROR(BinOp);
		}

		bool UsesPointerArithmetic = false;
		switch (BinOp->Op) {
		case TokenKind::PLUS_EQ: case TokenKind::MINUS_EQ: {
			if (LTy->GetKind() == TypeKind::POINTER) {
				// Pointer arithmetic case
				if (!RTy->isInt()) {
					Error(BinOp->RHS, "Pointer arithmetic expects integers");
					YIELD_ERROR(BinOp);
				}

				UsesPointerArithmetic = true;
			} else {
				if (!RTy->isNumber()) {
					OPERATOR_CANNOT_APPLY(RTy);
				}
				if (!LTy->isNumber()) {
					OPERATOR_CANNOT_APPLY(LTy);
				}
			}
			break;
		}
		case TokenKind::STAR_EQ: case TokenKind::SLASH_EQ:
			if (!RTy->isNumber()) {
				OPERATOR_CANNOT_APPLY(RTy);
			}
			if (!LTy->isNumber()) {
				OPERATOR_CANNOT_APPLY(LTy);
			}
			break;
		case TokenKind::MOD_EQ:
		case TokenKind::LT_LT_EQ: case TokenKind::GT_GT_EQ:
			if (!RTy->isInt()) {
				OPERATOR_CANNOT_APPLY(RTy);
			}
			if (!LTy->isInt()) {
				OPERATOR_CANNOT_APPLY(LTy);
			}
			break;
		case TokenKind::BAR_EQ: case TokenKind::AMP_EQ:
		case TokenKind::CRT_EQ:
			if (RTy->is(Context.BoolType)) {
				if (LTy->isNot(Context.BoolType)) {
					Error(BinOp, "Variable expected to be a boolean type");
					YIELD_ERROR(BinOp);
				}
			} else {
				if (!RTy->isInt()) {
					OPERATOR_CANNOT_APPLY(RTy);
				}
				if (!LTy->isInt()) {
					OPERATOR_CANNOT_APPLY(LTy);
				}
			}
			break;
		default:
			break;
		}

		if (!UsesPointerArithmetic) {
			if (!IsAssignableTo(LTy, BinOp->RHS)) {
				Error(BinOp, "Cannot assign value of type '%s' to variable of type '%s'",
					RTy->ToStr(), LTy->ToStr());
				YIELD_ERROR(BinOp);
			}


			if (BinOp->Op == '=') {
				AssignTo(BinOp->LHS, LTy, BinOp->Loc);
			} else {
				CreateCast(BinOp->RHS, LTy);
			}
		}

		BinOp->Ty = LTy;
		break;
	}
	case '+': case '-': {
		// Pointers are included so that pointer arithmetic
		// can be done.
		if (!(LTy->isNumber() || LTy->GetKind() == TypeKind::POINTER)) {
			OPERATOR_CANNOT_APPLY(LTy);
		}
		if (!(RTy->isNumber() || RTy->GetKind() == TypeKind::POINTER)) {
			OPERATOR_CANNOT_APPLY(RTy);
		}

		if (LTy->GetKind() == TypeKind::POINTER || RTy->GetKind() == TypeKind::POINTER) {
			// Pointer arithmetic

			if (BinOp->Op == '-' && LTy->isNumber()) {
				Error(BinOp->LHS, "Cannot subtract a pointer from a number");
				YIELD_ERROR(BinOp);
			}

			if (LTy->GetKind() == TypeKind::POINTER) {
				if (!RTy->isInt()) {
					Error(BinOp->RHS, "Pointer arithmetic expects integers");
					YIELD_ERROR(BinOp);
				}
				
				BinOp->Ty = LTy;
			} else {
				if (!LTy->isInt()) {
					Error(BinOp->LHS, "Pointer arithmetic expects integers");
					YIELD_ERROR(BinOp);
				}
				
				BinOp->Ty = RTy;
			}
		} else {
			// Not pointer arithmetic

			Type* ToType;
			if (LTy->isInt() && RTy->isInt()) {
				u32 LargerMemSize = max(LTy->MemSize(), RTy->MemSize());
				bool IsSigned = LTy->isSigned() || RTy->isSigned();
				ToType = Type::GetIntTypeBasedOnSize(LargerMemSize, IsSigned, Context);
			} else {
				// At least one is a float
				u32 LargerMemSize = max(LTy->MemSize(), RTy->MemSize());
				ToType = Type::GetFloatTypeBasedOnSize(LargerMemSize, Context);
			}
		
			CreateCast(BinOp->LHS, ToType);
			CreateCast(BinOp->RHS, ToType);
			BinOp->Ty = ToType;
		}
		break;
	}
	case '*': case '/': {
		if (!LTy->isNumber()) {
			OPERATOR_CANNOT_APPLY(LTy);
		}
		if (!RTy->isNumber()) {
			OPERATOR_CANNOT_APPLY(RTy);
		}

		Type* ToType;
		if (LTy->isInt() && RTy->isInt()) {
			u32 LargerMemSize = max(LTy->MemSize(), RTy->MemSize());
			bool IsSigned = LTy->isSigned() || RTy->isSigned();
			ToType = Type::GetIntTypeBasedOnSize(LargerMemSize, IsSigned, Context);
		} else {
			// At least one is a float
			u32 LargerMemSize = max(LTy->MemSize(), RTy->MemSize());
			ToType = Type::GetFloatTypeBasedOnSize(LargerMemSize, Context);
		}
		

		CreateCast(BinOp->LHS, ToType);
		CreateCast(BinOp->RHS, ToType);
		BinOp->Ty = ToType;
		break;
	}
	case '%':
	case TokenKind::LT_LT: case TokenKind::GT_GT: {
		if (!LTy->isInt()) {
			OPERATOR_CANNOT_APPLY(LTy);
		}
		if (!RTy->isInt()) {
			OPERATOR_CANNOT_APPLY(RTy);
		}

		Type* ToType;
		u32 LargerMemSize = max(LTy->MemSize(), RTy->MemSize());
		bool IsSigned = LTy->isSigned() || RTy->isSigned();
		ToType = Type::GetIntTypeBasedOnSize(LargerMemSize, IsSigned, Context);

		CreateCast(BinOp->LHS, ToType);
		CreateCast(BinOp->RHS, ToType);
		BinOp->Ty = ToType;
		break;
	}
	case '|': case '&': case '^': {
		bool IsBool = RTy->is(Context.BoolType);
		if (IsBool) {
			if (LTy->isNot(Context.BoolType)) {
				Error(BinOp, "Both sides of the operator '%s' must be a booleans or ints",
					GetTokenKindPresentation(BinOp->Op, Context));
				YIELD_ERROR(BinOp);
			}

			BinOp->Ty = Context.BoolType;
		} else {
			if (!LTy->isInt()) {
				OPERATOR_CANNOT_APPLY(LTy);
			}
			if (!RTy->isInt()) {
				OPERATOR_CANNOT_APPLY(RTy);
			}

			Type* ToType;
			u32 LargerMemSize = max(LTy->MemSize(), RTy->MemSize());
			bool IsSigned = LTy->isSigned() || RTy->isSigned();
			ToType = Type::GetIntTypeBasedOnSize(LargerMemSize, IsSigned, Context);

			CreateCast(BinOp->LHS, ToType);
			CreateCast(BinOp->RHS, ToType);
			BinOp->Ty = ToType;
		}
		break;
	}
	case TokenKind::EQ_EQ: case TokenKind::EXL_EQ: {
		if ((LTy->GetKind() == TypeKind::POINTER || LTy->GetKind() == TypeKind::NULLPTR) &&
			(RTy->GetKind() == TypeKind::POINTER || RTy->GetKind() == TypeKind::NULLPTR)
			) {
			CreateCast(BinOp->LHS, Context.I64Type);
			CreateCast(BinOp->RHS, Context.I64Type);
			BinOp->Ty = Context.BoolType;
		} else if (LTy->is(Context.BoolType) && RTy->is(Context.BoolType)) {
			BinOp->Ty = Context.BoolType;
		} else {
			goto number_compare_cases_lab;
		}
		break;
	}
	case '<': case '>':
	case TokenKind::LT_EQ: case TokenKind::GT_EQ: {
		number_compare_cases_lab:
		if (!LTy->isNumber()) {
			OPERATOR_CANNOT_APPLY(LTy);
		}
		if (!RTy->isNumber()) {
			OPERATOR_CANNOT_APPLY(RTy);
		}

		Type* ToType;
		if (LTy->isInt() && RTy->isInt()) {
			u32 LargerMemSize = max(LTy->MemSize(), RTy->MemSize());
			bool IsSigned = LTy->isSigned() || RTy->isSigned();
			ToType = Type::GetIntTypeBasedOnSize(LargerMemSize, IsSigned, Context);
		} else {
			// At least one is a float
			u32 LargerMemSize = max(LTy->MemSize(), RTy->MemSize());
			ToType = Type::GetFloatTypeBasedOnSize(LargerMemSize, Context);
		}

		CreateCast(BinOp->LHS, ToType);
		CreateCast(BinOp->RHS, ToType);
		BinOp->Ty = Context.BoolType;
		break;
	}
	case TokenKind::AMP_AMP: case TokenKind::BAR_BAR: {
		if (!IsComparable(LTy)) {
			OPERATOR_CANNOT_APPLY(LTy);
		}
		if (!IsComparable(RTy)) {
			OPERATOR_CANNOT_APPLY(RTy);
		}
	
		// These type of operators require
		// branching so folding is not able
		// to be performed.
		BinOp->IsFoldable = false;

		BinOp->Ty = Context.BoolType;
		break;
	}
	default:
		assert(!"Unimplemented binary op check");
		break;
	}

#undef OPERATOR_CANNOT_APPLY
}

void june::Analysis::CheckUnaryOp(UnaryOp* UOP) {
	CheckNode(UOP->Val);
	YIELD_ERROR_WHEN_M(UOP, UOP->Val);

#define OPERATOR_CANNOT_APPLY(T)                             \
Error(UOP,                                                   \
	"Operator '%s' cannot apply to type '%s'",               \
	 GetTokenKindPresentation(UOP->Op, Context), T->ToStr()); \
YIELD_ERROR(UOP)

	UOP->IsFoldable = UOP->Val->IsFoldable;
	UOP->IsComptimeCompat = UOP->Val->IsComptimeCompat;

	Type* VT = UOP->Val->Ty;
	switch (UOP->Op) {
	case TokenKind::PLUS_PLUS:   case TokenKind::POST_PLUS_PLUS:
	case TokenKind::MINUS_MINUS: case TokenKind::POST_MINUS_MINUS: {
		if (!(VT->isInt() || VT->GetKind() == TypeKind::POINTER)) {
			OPERATOR_CANNOT_APPLY(VT);
		}

		if (!IsLValue(UOP->Val)) {
			Error(UOP, "Operator '%s' requires the value to be a variable",
				GetTokenKindPresentation(UOP->Op, Context));
			YIELD_ERROR(UOP);
		}

		if (UOP->Val->IsComptimeCompat) {
			Error(UOP, "Operator '%s' requries the value to be modifiable",
				GetTokenKindPresentation(UOP->Op, Context));
			YIELD_ERROR(UOP);
		}

		UOP->Ty = UOP->Val->Ty;
		break;
	}
	case '&': {
		if (!IsLValue(UOP->Val)) {
			Error(UOP, "Operator '%s' requires the value to be a variable",
				GetTokenKindPresentation(UOP->Op, Context));
			YIELD_ERROR(UOP);
		}

		if (UOP->Val->is(AstKind::IDENT_REF) || UOP->Val->is(AstKind::FIELD_ACCESSOR)) {
			// TODO: What about RVO?
			// TODO: What if the function has infered param types?
			IdentRef* IRef = ocast<IdentRef*>(UOP->Val);
			if (IRef->RefKind == IdentRef::FUNCS) {
				FuncDecl* Func = (*IRef->FuncsRef)[0];

				if (Func->is(AstKind::GENERIC_FUNC_DECL)) {
					Error(UOP, "Cannot get the address of a generic function");
					YIELD_ERROR(UOP);
				}

				llvm::SmallVector<Type*, 4> ParamTypes;
				if (Func->Record) {
					// It is a member function so the first argument is an argument to
					// the pointer of the record.
					ParamTypes.push_back(PointerType::Create(GetRecordType(Func->Record), Context));
				}

				for (VarDecl* Param : Func->Params) {
					ParamTypes.push_back(Param->Ty);
				}
				UOP->Ty = FunctionType::Create(Func->RetTy, ParamTypes);
				Context.RequestGen(Func);
				break;
			}
		}

		if (UOP->Val->IsComptimeCompat) {
			Error(UOP, "Cannot take the address of a comptime variable");
			YIELD_ERROR(UOP);
		}

		UOP->Ty = PointerType::Create(VT, Context);
		break;
	}
	case '*': {
		if (VT->GetKind() != TypeKind::POINTER) {
			OPERATOR_CANNOT_APPLY(VT);
		}

		UOP->Ty = VT->AsPointerType()->ElmTy;
		break;
	}
	case '!': {
		if (!IsComparable(VT)) {
			OPERATOR_CANNOT_APPLY(VT);
		}

		UOP->Ty = Context.BoolType;
		break;
	}
	case '-': case '+': case '~': {
		if (!VT->isNumber()) {
			OPERATOR_CANNOT_APPLY(VT);
		}

		// TODO: handle casting for unsigned?

		UOP->Ty = VT;
		break;
	}
	default:
		assert(!"Unhandled unary check");
		break;
	}
#undef OPERATOR_CANNOT_APPLY
}

void june::Analysis::CheckArray(Array* Arr) {

	if (Arr->NumElements == 0) {
		Error(Arr, "Arrays must have at least one element");
		YIELD_ERROR(Arr);
	}

	Type* ElmTypes = nullptr;
	for (u32 i = 0; i < Arr->NumElements; i++) {
		Expr* Elm = Arr->GetElement(i);

		CheckNode(Elm);
		YIELD_ERROR_WHEN_M(Arr, Elm);

		if (!Elm->IsFoldable) {
			Arr->IsFoldable = false;
		}
		if (!Elm->IsComptimeCompat) {
			Arr->IsComptimeCompat = false;
		}

		if (!ElmTypes) {
			ElmTypes = Elm->Ty;
		} else {
			// TODO: Make sure other elements are compatible.
		}
	}

	Arr->Ty = FixedArrayType::Create(ElmTypes, Arr->RequiredNumElements, Context);
}

void june::Analysis::CheckArrayAccess(ArrayAccess* AA) {
	
	CheckNode(AA->Index);
	YIELD_ERROR_WHEN_M(AA, AA->Index);

	if (!AA->Index->Ty->isInt()) {
		Error(AA, "Expected int for index. Found '%s'", AA->Index->Ty->ToStr());
	}

	CheckNode(AA->Site);
	YIELD_ERROR_WHEN_M(AA, AA->Site);

	AA->IsComptimeCompat = AA->Site->IsComptimeCompat;

	TypeKind K = AA->Site->Ty->GetKind();
	if (K == TypeKind::TUPLE) {
		if (AA->Index->isNot(AstKind::NUMBER_LITERAL)) {
			Error(AA, "Indexing on tuples requires the index expression to be a simple integer");
			YIELD_ERROR(AA);
		}

		TupleType* TupleTy = AA->Site->Ty->AsTupleType();

		NumberLiteral* IndexNum = ocast<NumberLiteral*>(AA->Index);
		if (IndexNum->UnsignedIntValue > TupleTy->SubTypes.size()) {
			Error(AA, "Index exceeds the number of values for the tuple");
			YIELD_ERROR(AA);
		}

		Type* ValTy = TupleTy->SubTypes[IndexNum->UnsignedIntValue];
		AA->Ty = ValTy;
		return;
	}


	if (!(K == TypeKind::FIXED_ARRAY || K == TypeKind::POINTER)) {
		Error(AA, "Cannot index non-array or pointer type. Type was '%s'",
			AA->Site->Ty->ToStr());
		YIELD_ERROR(AA);
	}

	AA->Ty = AA->Site->Ty->AsContainerType()->ElmTy;
}

void june::Analysis::CheckTypeCast(TypeCast* Cast) {
	CheckNode(Cast->Val);
	YIELD_ERROR_WHEN_M(Cast, Cast->Val);

	if (Cast->CastKind == TypeCast::STANDARD) {
		if (!IsCastableTo(Cast->ToTy, Cast->Val->Ty)) {
			Error(Cast, "Cannot cast from type '%s' to type '%s'",
				Cast->Val->Ty->ToStr(), Cast->ToTy->ToStr());
			YIELD_ERROR(Cast);
		}
	} else if (Cast->CastKind == TypeCast::BITS) {
		if (!IsBitsCastableTo(Cast->ToTy, Cast->Val->Ty)) {
			Error(Cast, "Cannot bits cast from type '%s' to type '%s'",
				Cast->Val->Ty->ToStr(), Cast->ToTy->ToStr());
			YIELD_ERROR(Cast);
		}
	}

	// TODO: What if the casting requires non-foldability?
	Cast->IsComptimeCompat = Cast->Val->IsComptimeCompat;
	Cast->IsFoldable = Cast->Val->IsFoldable;
	Cast->Ty = Cast->ToTy;
}

void june::Analysis::CheckHeapAllocType(HeapAllocType* HeapAlloc) {
	HeapAlloc->IsFoldable = false;
	HeapAlloc->IsComptimeCompat = false;

	if (HeapAlloc->TypeToAlloc->GetKind() == TypeKind::FIXED_ARRAY) {
		HeapAlloc->Ty = PointerType::Create(
			HeapAlloc->TypeToAlloc->AsFixedArrayType()->GetBaseType(), Context);
		FixedArrayType* ArrTyItr = HeapAlloc->TypeToAlloc->AsFixedArrayType();
		while (true) {
			CheckNode(ArrTyItr->LengthAsExpr);
			if (!ArrTyItr->LengthAsExpr->Ty->isInt()) {
				Error(HeapAlloc, "Array length expected to be an integer");
			}

			if (ArrTyItr->ElmTy->GetKind() == TypeKind::FIXED_ARRAY) {
				ArrTyItr = ArrTyItr->ElmTy->AsFixedArrayType();
			} else {
				break;
			}
		}
	} else {
		HeapAlloc->Ty = PointerType::Create(HeapAlloc->TypeToAlloc, Context);
	}
}

void june::Analysis::CheckThisRef(ThisRef* This) {
	if (!CRecord) {
		Error(This, "Cannot use 'this' in global scope");
		YIELD_ERROR(This);
	}
	This->IsFoldable = false;
	// Just take the type as absolute.
	This->Ty = PointerType::Create(GetRecordType(CRecord), Context);
}

void june::Analysis::CheckTernaryCond(TernaryCond* Ternary) {
	CheckNode(Ternary->Cond);
	YIELD_ERROR_WHEN_M(Ternary, Ternary->Cond);

	CheckCond(Ternary->Cond, Ternary->ExpandedCondLoc, "Operator '?'");

	CheckNode(Ternary->Val1);
	CheckNode(Ternary->Val2);

	YIELD_ERROR_WHEN_M(Ternary, Ternary->Val1);
	YIELD_ERROR_WHEN_M(Ternary, Ternary->Val2);

	if (!IsCastableTo(Ternary->Val1->Ty, Ternary->Val2->Ty)) {
		Error(Ternary, "Conditional operator '?' expects both values to have compatible types");
		YIELD_ERROR(Ternary);
	}
	CreateCast(Ternary->Val2, Ternary->Val1->Ty);

	if (!Ternary->Val1->IsFoldable || !Ternary->Val2->IsFoldable) {
		Ternary->IsComptimeCompat = false;
	}
	if (!Ternary->Val1->IsComptimeCompat || !Ternary->Val2->IsComptimeCompat) {
		Ternary->IsComptimeCompat = false;
	}
	Ternary->Ty = Ternary->Val1->Ty;
}

void june::Analysis::CheckTuple(Tuple* Tup) {

	llvm::SmallVector<Type*, 4> SubTypes;
	Tup->IsFoldable = false;
	
	bool EncounteredValError = false;
	for (Expr* Val : Tup->Values) {
		CheckNode(Val);
		if (!Val->IsComptimeCompat) {
			Tup->IsComptimeCompat = false;
		}
		if (Val->Ty->is(Context.ErrorType)) {
			EncounteredValError = true;
		}
		SubTypes.push_back(Val->Ty);
	}

	if (EncounteredValError) {
		YIELD_ERROR(Tup);
	}

	Tup->Ty = TupleType::Create(SubTypes);
}

bool june::Analysis::IsAssignableTo(Type* ToTy, Expr* FromExpr) {
	return IsAssignableTo(ToTy, FromExpr->Ty, FromExpr, false);
}

bool june::Analysis::IsAssignableTo(Type* ToTy, Type* FromTy, Expr* FromExpr, bool LossenNumConversion) {
	switch (ToTy->GetKind()) {
	case TypeKind::I8:
	case TypeKind::I16:
	case TypeKind::I32:
	case TypeKind::I64:
	case TypeKind::U8:
	case TypeKind::U16:
	case TypeKind::U32:
	case TypeKind::U64:
	case TypeKind::C8:
	case TypeKind::C16:
	case TypeKind::C32:
		if (FromTy->isInt()) {
			if (ToTy->MemSize() >= FromTy->MemSize() || LossenNumConversion) {
				return true;
			} else if (FromExpr && FromExpr->is(AstKind::NUMBER_LITERAL)) {
				// If the FromExpr is a basic number literal
				// then it will be allowed as long as it's value
				// would not result in a loss of data
				
				NumberLiteral* Num = ocast<NumberLiteral*>(FromExpr);
#define RANGE(ty, v)     v >= std::numeric_limits<ty>::min() && v <= std::numeric_limits<ty>::max();
#define POS_RANGE(ty, v) v >= 0 && v <= std::numeric_limits<ty>::max();
				
				if (Num->Ty->isSigned()) {
					switch (ToTy->GetKind()) {
					case TypeKind::I8:  return RANGE(s8, Num->SignedIntValue);
					case TypeKind::I16: return RANGE(s16, Num->SignedIntValue);
					case TypeKind::I32: return RANGE(s32, Num->SignedIntValue);
					case TypeKind::I64: return RANGE(s64, Num->SignedIntValue);
					case TypeKind::U8:  return POS_RANGE(u8, Num->SignedIntValue);
					case TypeKind::U16: return POS_RANGE(u16, Num->SignedIntValue);
					case TypeKind::U32: return POS_RANGE(u32, Num->SignedIntValue);
					case TypeKind::U64: return POS_RANGE(u64, Num->SignedIntValue);
					case TypeKind::C8:	return RANGE(s8, Num->SignedIntValue);
					case TypeKind::C16:	return RANGE(s16, Num->SignedIntValue);
					case TypeKind::C32: return RANGE(s32, Num->SignedIntValue);
					default:
						return false;
					}
				} else {
					switch (ToTy->GetKind()) {
					case TypeKind::I8:  return RANGE(s8, Num->UnsignedIntValue);
					case TypeKind::I16: return RANGE(s16, Num->UnsignedIntValue);
					case TypeKind::I32: return RANGE(s32, Num->UnsignedIntValue);
					case TypeKind::I64: return RANGE(s64, Num->UnsignedIntValue);
					case TypeKind::U8:  return POS_RANGE(u8, Num->UnsignedIntValue);
					case TypeKind::U16: return POS_RANGE(u16, Num->UnsignedIntValue);
					case TypeKind::U32: return POS_RANGE(u32, Num->UnsignedIntValue);
					case TypeKind::U64: return POS_RANGE(u64, Num->UnsignedIntValue);
					case TypeKind::C8:  return RANGE(s8, Num->UnsignedIntValue);
					case TypeKind::C16:	return RANGE(s16, Num->UnsignedIntValue);
					case TypeKind::C32:	return RANGE(s32, Num->UnsignedIntValue);
					default:
						return false;
					}
				}
#undef RANGE
#undef POS_RANGE
			}
		}
		return false;
	case TypeKind::F32:
	case TypeKind::F64:
 		if (FromTy->isFloat()) {
			if (ToTy->MemSize() >= FromTy->MemSize())
				return true;
			// It is still possible the 64-bit float fits in the range
			// of the 32-bit float.
			if (FromExpr && FromExpr->is(AstKind::NUMBER_LITERAL)) {
				NumberLiteral* Num = ocast<NumberLiteral*>(FromExpr);
				return 
					Num->F64Value >= std::numeric_limits<float>::min() &&
					Num->F64Value <= std::numeric_limits<float>::max();
			}
			return false;
		} else if (FromTy->isInt()) {
			// TODO: What about longs?
			return true; // Can always assign integers to floats
		}
		return false;
	case TypeKind::BOOL:
		return FromTy->is(Context.BoolType);
	case TypeKind::POINTER: {
		if (FromTy->GetKind() == TypeKind::POINTER) {
			if (ToTy->is(Context.VoidPtrType)) {
				PointerType* FromPtrTy = FromTy->AsPointerType();
				return FromPtrTy->GetNestingLevel() == 0;
			}
			return ToTy->is(FromTy);
		} else if (FromTy->GetKind() == TypeKind::NULLPTR) {
			return true;
		} else if (FromTy->GetKind() == TypeKind::FIXED_ARRAY){
			PointerType* ToPtrTy = ToTy->AsPointerType();
			if (ToPtrTy->GetNestingLevel() == 0) {
				ContainerType* FromCT = FromTy->AsContainerType();
				if (FromCT->GetNestingLevel() != 0) return false;
				return ToPtrTy->ElmTy->is(FromCT->ElmTy);
			}
		}

		return false;
	}
	case TypeKind::FIXED_ARRAY: {
		if (FromTy->GetKind() != TypeKind::FIXED_ARRAY) return false;
		FixedArrayType* ToArrTy = ToTy->AsFixedArrayType();
		FixedArrayType* FromArrTy = FromTy->AsFixedArrayType();
		u32 CompNestLevel = ToArrTy->GetNestingLevel();
		if (CompNestLevel != FromArrTy->GetNestingLevel()) return false;

		if (FromExpr && FromExpr->is(AstKind::ARRAY)) {
			// Making sure that the length of the destination
			// is the same or bigger than the length of the
			// source
			if (ToArrTy->Length < FromArrTy->Length) return false;
			for (u32 i = 0; i < CompNestLevel; i++) {
				ToArrTy = ToArrTy->ElmTy->AsFixedArrayType();
				FromArrTy = FromArrTy->ElmTy->AsFixedArrayType();
				if (ToArrTy->Length < FromArrTy->Length) return false;
			}
		} else {
			if (ToArrTy->Length != FromArrTy->Length) return false;
		}
		return IsAssignableTo(ToArrTy->ElmTy, FromArrTy->ElmTy, nullptr, true);
	}
	case TypeKind::TUPLE:
		return FromTy->is(ToTy);
	case TypeKind::RECORD:
		return FromTy->is(ToTy);
	case TypeKind::VOID:
		return false;
	case TypeKind::UNDEFINED:
		return false;
	case TypeKind::NULLPTR:
		return false;
	case TypeKind::FUNCTION:
		return FromTy->is(ToTy);
	default:
		assert(!"unimplemented IsAssignableTo()");
		return false;
	}
}

bool june::Analysis::IsCastableTo(Type* ToTy, Type* FromTy) {
	switch (ToTy->GetKind()) {
	case TypeKind::I8:
	case TypeKind::I16:
	case TypeKind::I32:
	case TypeKind::I64:
	case TypeKind::U8:
	case TypeKind::U16:
	case TypeKind::U32:
	case TypeKind::U64:
	case TypeKind::C8:
	case TypeKind::C16:
	case TypeKind::C32:
		if (FromTy->isNumber() || FromTy->GetKind() == TypeKind::POINTER || FromTy->is(Context.BoolType))
			return true; // Allow pointers/numbers to cast to integers
		return false;
	case TypeKind::F32:
	case TypeKind::F64:
		return FromTy->isNumber();
	case TypeKind::POINTER:
		if (FromTy->isNumber() || FromTy->GetKind() == TypeKind::POINTER)
			return true; // Allow pointers/numbers to cast to pointers
		return IsAssignableTo(ToTy, FromTy, nullptr, false);
	default:
		return IsAssignableTo(ToTy, FromTy, nullptr, false);
	}
}

bool june::Analysis::IsBitsCastableTo(Type* ToTy, Type* FromTy) {
	if (ToTy->isNumber()) {
		return FromTy->isNumber() || FromTy->GetKind() == TypeKind::POINTER;
	}
	return false;
}

void june::Analysis::CreateCast(Expr* E, Type* ToType) {
	if (ToType->is(E->Ty)) return;
	E->CastTy = ToType;

	if (E->is(AstKind::ARRAY)) {
		TypeKind ToK = ToType->GetKind();
		if (ToK == TypeKind::FIXED_ARRAY || ToK == TypeKind::POINTER) {
			Type* CastToBaseTy = ToType->AsContainerType()->GetBaseType();
			if (CastToBaseTy->isNot(E->Ty->AsFixedArrayType()->GetBaseType())) {
				CreateArrayElementsCast(CastToBaseTy, ocast<Array*>(E));
			}
		}
	}
}

void june::Analysis::CreateArrayElementsCast(Type* BaseType, Array* Arr) {
	for (u32 i = 0; i < Arr->NumElements; i++) {
		Expr* Elm = Arr->GetElement(i);
		if (Elm->is(AstKind::ARRAY)) {
			CreateArrayElementsCast(BaseType, ocast<Array*>(Elm));
		} else {
			CreateCast(Elm, BaseType);
		}
	}
}

bool june::Analysis::IsLValue(Expr* E) {
	AstKind K = E->Kind;
	if (K == AstKind::UNARY_OP) {
		UnaryOp* UOP = ocast<UnaryOp*>(E);
		return UOP->Op == '*'; // Can assign to dereferences
	}
	if (K == AstKind::IDENT_REF || K == AstKind::FIELD_ACCESSOR || K == AstKind::ARRAY_ACCESS) {
		return true;
	}
	if (K == AstKind::FUNC_CALL) {
		FuncCall* Call = ocast<FuncCall*>(E);
		TypeKind TK = Call->Ty->GetKind();
		return TK == TypeKind::POINTER || TK == TypeKind::RECORD;
	}
	return false;
}

bool june::Analysis::IsComparable(Type* Ty) {
	return Ty->is(Context.BoolType) || Ty->GetKind() == TypeKind::POINTER;
}

void june::Analysis::EnsureChecked(SourceLoc ELoc, VarDecl* Var) {
	if (Var->IsBeingChecked) {
		if (CField) {
			Error(ELoc, "Fields form a circular dependency");
			DisplayCircularDep(CField);
		} else if (CGlobal) {
			Error(ELoc, "Global variables form a circular depedency");
			DisplayCircularDep(CGlobal);
		} else {
			Error(ELoc, "Cannot access a local variable while it is being declared");
		}
		Var->Ty = Context.ErrorType;
		return;
	}

	Analysis A(Context, Var->FU->Log, ForCodeGen);
	if (CField) {
		Var->DepD = CField; // CField depends on Var.
	} else {
		Var->DepD = CGlobal;
	}
	if (Var->ParentDeclList) {
		// Want to check the entire list instead
		A.CheckVarDeclList(Var->ParentDeclList);
	} else {
		A.CheckVarDecl(Var);
	}
	Var->DepD = nullptr; // Dependency finished.
}

void june::Analysis::EnsureChecked(SourceLoc ELoc, RecordDecl* Record) {
	if (ForCodeGen) {
		RequestRecordDestructionGen(Record);
	} else {
		if (Record->IsBeingChecked) {
			Error(ELoc, "Records form a circular dependency");
			DisplayCircularDep(CRecord);
			return;
		}

		Analysis A(Context, Record->FU->Log, ForCodeGen);
		Record->DepD = CRecord;
		A.CheckRecordDecl(Record);
		Record->DepD = nullptr;
	}
}

void june::Analysis::DisplayCircularDep(Decl* StartDep) {
	Log.Note("Dependency graph: \n");
	std::vector<Decl*> DepOrder;
	Decl* DepD = StartDep;
	u32 LongestIdentLen = 0;
	while (DepD) {
		if (DepD->Name.Text.size() > LongestIdentLen) {
			LongestIdentLen = DepD->Name.Text.size();
		}
		if (std::find(DepOrder.begin(), DepOrder.end(), DepD) != DepOrder.end()) {
			// TODO: For some strange reason it looks back on itself
			break;
		}
		DepOrder.push_back(DepD);
		DepD = DepD->DepD;
	}
	std::reverse(DepOrder.rbegin(), DepOrder.rend());
	std::rotate(DepOrder.rbegin(), DepOrder.rbegin() + 1, DepOrder.rend());

	auto it = DepOrder.begin();
	while (it != DepOrder.end()) {
		Decl* DepRHS = nullptr;
		Decl* DepLHS = (*it);
		if ((it + 1) != DepOrder.end()) {
			DepRHS = *(it + 1);
		} else {
			DepRHS = StartDep;
		}

		std::string LPad = std::string(LongestIdentLen - DepLHS->Name.Text.size(), ' ');
		std::string RPad = std::string(LongestIdentLen - DepRHS->Name.Text.size(), ' ');
		Log.NoteLn("'%s'%s deps-on '%s'%s   At: %s.june:%s", DepLHS->Name, LPad, DepRHS->Name, RPad,
			DepLHS->FU->FL.PathKey.c_str(), DepLHS->Loc.LineNumber
			);
		++it;
	}
			
	Log.EndNote();
}

june::RecordType* june::Analysis::GetRecordType(RecordDecl* Record) {
	// Using absolute paths at this point since all information about
	// where records are at is determined from parsing.
	RecordLocation RecLoc =  RecordLocation::CreateRecLocationByRecord(Record);
	auto RelLoc = std::make_tuple(nullptr, RecLoc);
	auto it = FU->QualifyingRecordTypes.find(RelLoc);
	RecordType* ResTy;
	if (it != FU->QualifyingRecordTypes.end()) {
		ResTy = it->second.RecType;
	} else {
		ResTy = new RecordType;
		ResTy->Record = Record;
		FU->QualifyingRecordTypes.insert({ RelLoc,
			FileUnit::QualifyingRecordType{ ResTy } });
	}

	return ResTy;
}

bool june::Analysis::RequestRecordDestructionGen(RecordDecl* Record) {
	if (!Record->AlreadyRequestedDestructionGen) {
		Record->AlreadyRequestedDestructionGen = true;

		Record->NeedsDestruction = Record->Destructor != nullptr;
		if (Record->Destructor)
			Context.RequestGen(Record->Destructor);
		for (VarDecl* Field : Record->FieldsByIdxOrder) {
			Record->NeedsDestruction |= TypeNeedsDestructionAndGenDestructors(Field->Ty);
		}
	}
	return Record->NeedsDestruction;
}

bool june::Analysis::TypeNeedsDestructionAndGenDestructors(Type* Ty) {
	if (Ty->GetKind() == TypeKind::RECORD) {
		return RequestRecordDestructionGen(Ty->AsRecordType()->Record);
	} else if (Ty->GetKind() == TypeKind::TUPLE) {
		TupleType* TupleTy = Ty->AsTupleType();
		for (Type* ValueTy : TupleTy->SubTypes) {
			if (TypeNeedsDestructionAndGenDestructors(ValueTy)) {
				return true;
			}
		}
	} else if (Ty->GetKind() == TypeKind::FIXED_ARRAY) {
		Type* BaseTy = Ty->AsFixedArrayType()->GetBaseType();
		return TypeNeedsDestructionAndGenDestructors(BaseTy);
	}
	return false;
}

void june::Analysis::AssignTo(Expr* Assignment, Type* ToTy, SourceLoc AssignLoc) {
	if (Assignment->is(AstKind::IDENT_REF)) {
		if (TypeNeedsDestructionAndGenDestructors(Assignment->Ty)) {
			IdentRef* IRef = ocast<IdentRef*>(Assignment);
			IRef->VarRef->MemoryWasMoved = true;
			IRef->VarRef->MemoryMovedLoc = AssignLoc;
		}
	}
	CreateCast(Assignment, ToTy);
}