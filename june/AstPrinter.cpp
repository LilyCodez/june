#include "AstPrinter.h"

#include <llvm/Support/raw_ostream.h>

#include "Tokens.h"
#include "Types.h"

namespace june {

	void PrintNode(const JuneContext& Context, const AstNode* N, u32 Depth);

	void PrintIndent(u32 Depth) {
		llvm::outs().indent(Depth * 4);
	}

	void PrintFuncDecl(const JuneContext& Context, const FuncDecl* Func, u32 Depth) {
		llvm::outs() << "(func| name=\"" << Func->Name << "\")";
		if (!Func->Scope.Stmts.empty()) {
			for (AstNode* N : Func->Scope.Stmts) {
				llvm::outs() << '\n';
				PrintNode(Context, N, Depth + 1);
			}
		}
	}

	void PrintGenericFuncDecl(const JuneContext& Context, const GenericFuncDecl* Func, u32 Depth) {
		llvm::outs() << "(generic-func| name=\"" << Func->Name << "\", generic-types=[";
		u32 Count = 0;
		for (auto [GenericName, GenericType] : Func->GenericTypes) {
			llvm::outs() << GenericName;
			if (++Count != Func->GenericTypes.size())
				llvm::outs() << ", ";
		}
		llvm::outs() << "])";
		if (!Func->Scope.Stmts.empty()) {
			for (AstNode* N : Func->Scope.Stmts) {
				llvm::outs() << '\n';
				PrintNode(Context, N, Depth + 1);
			}
		}
	}

	void PrintVarDecl(const JuneContext& Context, const VarDecl* Var, u32 Depth) {
		llvm::outs() << "(var| name=\"" << Var->Name << "\")";
		if (Var->Assignment) {
			llvm::outs() << '\n';
			PrintNode(Context, Var->Assignment, Depth + 1);
		}
	}

	void PrintVarDeclList(const JuneContext& Context, const VarDeclList* DeclList, u32 Depth) {
		llvm::outs() << "(decl-list)";
		for (VarDecl* Var : DeclList->Decls) {
			llvm::outs() << '\n';
			PrintNode(Context, Var, Depth + 1);
		}
	}

	void PrintRecordDecl(const JuneContext& Context, const RecordDecl* Record, u32 Depth) {
		llvm::outs() << "(record| name=\"" << Record->Name << "\")";
		if (!Record->Fields.empty()) {
			llvm::outs() << '\n';
			PrintIndent(Depth);
			llvm::outs() << "fields:";
			for (VarDecl* Field : Record->FieldsByIdxOrder) {
				llvm::outs() << '\n';
				PrintNode(Context, Field, Depth + 1);
			}
		}
		if (!Record->Constructors.empty()) {
			llvm::outs() << '\n';
			PrintIndent(Depth);
			llvm::outs() << "constructors:";
			for (FuncDecl* Constructor : Record->Constructors) {
				llvm::outs() << '\n';
				PrintNode(Context, Constructor, Depth + 1);
			}
		}
		if (!Record->Funcs.empty()) {
			llvm::outs() << '\n';
			PrintIndent(Depth);
			llvm::outs() << "functions:";
			for (auto& [_, Funcs] : Record->Funcs) {
				for (FuncDecl* Func : Funcs) {
					llvm::outs() << '\n';
					PrintNode(Context, Func, Depth + 1);
				}
			}
		}
	}

	void PrintInnerScope(const JuneContext& Context, const InnerScopeStmt* InnerScope, u32 Depth) {
		llvm::outs() << "(inner-scope)";
		if (!InnerScope->Scope.Stmts.empty()) {
			for (AstNode* Stmt : InnerScope->Scope.Stmts) {
				llvm::outs() << '\n';
				PrintNode(Context, Stmt, Depth + 1);
			}
		}
	}

	void PrintReturn(const JuneContext& Context, const ReturnStmt* Ret, u32 Depth) {
		llvm::outs() << "(return)\n";
		if (!Ret->Val) {
			PrintIndent(Depth + 1);
			llvm::outs() << "(void)";
		} else {
			PrintNode(Context, Ret->Val, Depth + 1);
		}
	}

	void PrintRangeLoop(const JuneContext& Context, const RangeLoopStmt* Loop, u32 Depth) {
		llvm::outs() << "(range-loop)";
		if (Loop->Decl) {
			llvm::outs() << '\n';
			PrintIndent(Depth);
			llvm::outs() << "decl:\n";
			PrintNode(Context, Loop->Decl, Depth + 1);
		}
		if (Loop->Cond) {
			llvm::outs() << '\n';
			PrintIndent(Depth);
			llvm::outs() << "cond:\n";
			PrintNode(Context, Loop->Cond, Depth + 1);
		}
		if (Loop->Inc) {
			llvm::outs() << '\n';
			PrintIndent(Depth);
			llvm::outs() << "inc:\n";
			PrintNode(Context, Loop->Inc, Depth + 1);
		}
		if (!Loop->Scope.Stmts.empty()) {
			llvm::outs() << '\n';
			PrintIndent(Depth);
			llvm::outs() << "stmts:";
			for (AstNode* N : Loop->Scope.Stmts) {
				llvm::outs() << '\n';
				PrintNode(Context, N, Depth + 1);
			}
		}
	}

	void PrintIteratorLoop(const JuneContext& Context, const IteratorLoopStmt* Loop, u32 Depth) {
		llvm::outs() << "(iterator-loop| var-ident=\"" << Loop->VarVal->Name << "\")\n";
		PrintIndent(Depth);
		llvm::outs() << "expr:\n";
		PrintNode(Context, Loop->IterOnExpr, Depth + 1);
	}

	void PrintPredicateLoop(const JuneContext& Context, const PredicateLoopStmt* Loop, u32 Depth) {
		llvm::outs() << "(predicate-loop)";
		if (Loop->Cond) {
			llvm::outs() << '\n';
			PrintIndent(Depth);
			llvm::outs() << "cond:\n";
			PrintNode(Context, Loop->Cond, Depth + 1);
		}
		if (!Loop->Scope.Stmts.empty()) {
			llvm::outs() << '\n';
			PrintIndent(Depth);
			llvm::outs() << "stmts:";
			for (AstNode* N : Loop->Scope.Stmts) {
				llvm::outs() << '\n';
				PrintNode(Context, N, Depth + 1);
			}
		}
	}

	void PrintLoopControl(const JuneContext& Context, const LoopControlStmt* LoopControl, u32 Depth) {
		if (LoopControl->Kind == AstKind::BREAK) {
			llvm::outs() << "(break)";
		} else {
			llvm::outs() << "(continue)";
		}
	}

	void PrintIf(const JuneContext& Context, const IfStmt* If, u32 Depth) {
		llvm::outs() << "(if)\n";
		PrintIndent(Depth);
		llvm::outs() << "cond:\n";
		PrintNode(Context, If->Cond, Depth + 1);
		if (!If->Scope.Stmts.empty()) {
			llvm::outs() << '\n';
			PrintIndent(Depth);
			llvm::outs() << "body:";
			for (AstNode* Stmt : If->Scope.Stmts) {
				llvm::outs() << '\n';
				PrintNode(Context, Stmt, Depth + 1);
			}
		}
		if (If->Else) {
			llvm::outs() << '\n';
			PrintIndent(Depth);
			llvm::outs() << "else:\n";
			PrintNode(Context, If->Else, Depth + 1);
		}
	}

	void PrintDelete(const JuneContext& Context, const DeleteStmt* Delete, u32 Depth) {
		llvm::outs() << "(delete)\n";
		PrintNode(Context, Delete->Val, Depth + 1);
	}

	void PrintIdentRef(const JuneContext& Context, const IdentRef* IRef, u32 Depth) {
		llvm::outs() << "(iref| ident=\"" << IRef->Ident << "\")";
	}

	void PrintFieldAccessor(const JuneContext& Context, const FieldAccessor* FA, u32 Depth) {
		llvm::outs() << "(field-accessor| field-name=\"" << FA->Ident << "\")\n";
		PrintNode(Context, FA->Site, Depth + 1);
	}

	void PrintFuncCall(const JuneContext& Context, const FuncCall* Call, u32 Depth) {
		llvm::outs() << "(func-call)\n";
		if (!Call->Args.empty()) {
			PrintIndent(Depth);
			llvm::outs() << "arguments:";
			for (Expr* Arg : Call->Args) {
				llvm::outs() << '\n';
				PrintNode(Context, Arg, Depth + 1);
			}
			llvm::outs() << '\n';
		}
		PrintIndent(Depth);
		llvm::outs() << "site:\n";
		PrintNode(Context, Call->Site, Depth + 1);
	}

	void PrintUnaryOp(const JuneContext& Context, const UnaryOp* UOP, u32 Depth) {
		llvm::outs() << "(uop| op='" << GetTokenKindPresentation(UOP->Op, Context) << "')\n";
		PrintNode(Context, UOP->Val, Depth + 1);
	}

	void PrintBinaryOp(const JuneContext& Context, const BinaryOp* BinOp, u32 Depth) {
		llvm::outs() << "(bin-op| op='" << GetTokenKindPresentation(BinOp->Op, Context) << "')\n";
		PrintNode(Context, BinOp->LHS, Depth + 1);
		llvm::outs() << '\n';
		PrintNode(Context, BinOp->RHS, Depth + 1);
	}

	void PrintNumberLiteral(const JuneContext& Context, const NumberLiteral* Number, u32 Depth) {
		llvm::outs() << "(num| ty=";
		switch (Number->Ty->GetKind()) {
		case TypeKind::I8:  llvm::outs() << "i8";  break;
		case TypeKind::I16: llvm::outs() << "i16"; break;
		case TypeKind::I32: llvm::outs() << "i32"; break;
		case TypeKind::I64: llvm::outs() << "i64"; break;
		case TypeKind::U8:  llvm::outs() << "u8";  break;
		case TypeKind::U16: llvm::outs() << "u16"; break;
		case TypeKind::U32: llvm::outs() << "u32"; break;
		case TypeKind::U64: llvm::outs() << "u64"; break;
		case TypeKind::C8:  llvm::outs() << "c8";  break;
		case TypeKind::C16: llvm::outs() << "c16"; break;
		case TypeKind::C32: llvm::outs() << "c32"; break;
		case TypeKind::F32: llvm::outs() << "f32"; break;
		case TypeKind::F64: llvm::outs() << "f64"; break;
		}
		llvm::outs() << " val=";
		switch (Number->Ty->GetKind()) {
		case TypeKind::C8:
			if (Number->SignedIntValue >= 32 && Number->SignedIntValue <= 126) {
				llvm::outs() << '\'' << (c8)Number->SignedIntValue << '\'';
			} else {
				switch (Number->SignedIntValue) {
				case '\\': llvm::outs() << "'\\'";   break;
				case '\n':  llvm::outs() << "'\\n'"; break;
				case '\t':  llvm::outs() << "'\\t'"; break;
				case '\0':  llvm::outs() << "'\\0'"; break;
				case '\"':  llvm::outs() << "'\"'";  break;
				case '\a':  llvm::outs() << "'\\a'"; break;
				case '\r':  llvm::outs() << "'\\r'"; break;
				case '\v':  llvm::outs() << "'\\v'"; break;
				case '\b':  llvm::outs() << "'\\b'"; break;
				case '\f':  llvm::outs() << "'\\f'"; break;
				case '\?':  llvm::outs() << "'\\?'"; break;
				case '\'': llvm::outs() << "'\\''";  break;
				default:
					llvm::outs() << Number->SignedIntValue;
					break;
				}
			}
			break;
		case TypeKind::C16:
		case TypeKind::C32:
		case TypeKind::I8: 
		case TypeKind::I16:
		case TypeKind::I32:
		case TypeKind::I64: llvm::outs() << Number->SignedIntValue; break;
		case TypeKind::U8:
		case TypeKind::U16:
		case TypeKind::U32:
		case TypeKind::U64: llvm::outs() << Number->UnsignedIntValue; break;
		case TypeKind::F32: llvm::outs() << Number->F32Value; break;
		case TypeKind::F64: llvm::outs() << Number->F64Value; break;
		}
		llvm::outs() << ")";
	}

	void PrintArray(const JuneContext& Context, const Array* Array, u32 Depth) {
		llvm::outs() << "(array)\n";
		for (u32 i = 0; i < Array->NumElements; i++) {
			if (i != 0)
				llvm::outs() << '\n';
			PrintNode(Context, Array->GetElement(i), Depth + 1);
		}
	}

	void PrintNull(const JuneContext& Context, const Null* Nu, u32 Depth) {
		llvm::outs() << "(null)";
	}

	void PrintArrayAccess(const JuneContext& Context, const ArrayAccess* AA, u32 Depth) {
		llvm::outs() << "(array-access)\n";
		PrintIndent(Depth);
		llvm::outs() << "index:\n";
		PrintNode(Context, AA->Index, Depth + 1);
		llvm::outs() << '\n';
		PrintIndent(Depth);
		llvm::outs() << "site:\n";
		PrintNode(Context, AA->Site, Depth + 1);
	}

	void PrintBool(const JuneContext& Context, const BoolLiteral* B, u32 Depth) {
		llvm::outs() << "(bool |val=" << B->tof << ")";
	}

	void PrintSizeofType(const JuneContext& Context, const SizeofType* SO, u32 Depth) {
		llvm::outs() << "(sizeof)";
	}

	void PrintTypeCast(const JuneContext& Context, const TypeCast* Cast, u32 Depth) {
		llvm::outs() << "(type-cast)\n";
		PrintNode(Context, Cast->Val, Depth + 1);
	}

	void PrintHeapAllocType(const JuneContext& Context, const HeapAllocType* HeapAlloc, u32 Depth) {
		llvm::outs() << "(heap-alloc-type)";
	}

	void PrintThisRef(const JuneContext& Context, const ThisRef* This, u32 Depth) {
		llvm::outs() << "(this)";
	}

	void PrintTernaryCond(const JuneContext& Context, const TernaryCond* Ternary, u32 Depth) {
		llvm::outs() << "(ternary-cond)\n";
		PrintIndent(Depth);
		llvm::outs() << "cond:\n";
		PrintNode(Context, Ternary->Cond, Depth + 1);
		llvm::outs() << "\nval1:\n";
		PrintNode(Context, Ternary->Val1, Depth + 1);
		llvm::outs() << "\nval2:\n";
		PrintNode(Context, Ternary->Val2, Depth + 1);
	}

	void PrintTuple(const JuneContext& Context, const Tuple* Tup, u32 Depth) {
		llvm::outs() << "(tuple)\n";
		PrintIndent(Depth);
		llvm::outs() << "values:";
		for (Expr* Value : Tup->Values) {
			llvm::outs() << '\n';
			PrintNode(Context, Value, Depth + 1);
		}
	}

	void PrintErrorNode() {
		llvm::outs() << "(error)";
	}

	void PrintNode(const JuneContext& Context, const AstNode* N, u32 Depth) {
		PrintIndent(Depth);
		switch (N->Kind) {
		case AstKind::FUNC_DECL:
			PrintFuncDecl(Context, ocast<const FuncDecl*>(N), Depth);
			break;
		case AstKind::GENERIC_FUNC_DECL:
			PrintGenericFuncDecl(Context, ocast<const GenericFuncDecl*>(N), Depth);
			break;
		case AstKind::VAR_DECL:
			PrintVarDecl(Context, ocast<const VarDecl*>(N), Depth);
			break;
		case AstKind::VAR_DECL_LIST:
			PrintVarDeclList(Context, ocast<const VarDeclList*>(N), Depth);
			break;
		case AstKind::RECORD_DECL:
			PrintRecordDecl(Context, ocast<const RecordDecl*>(N), Depth);
			break;
		case AstKind::INNER_SCOPE:
		case AstKind::ELSE_SCOPE:
			PrintInnerScope(Context, ocast<const InnerScopeStmt*>(N), Depth);
			break;
		case AstKind::RETURN:
			PrintReturn(Context, ocast<const ReturnStmt*>(N), Depth);
			break;
		case AstKind::RANGE_LOOP:
			PrintRangeLoop(Context, ocast<const RangeLoopStmt*>(N), Depth);
			break;
		case AstKind::ITERATOR_LOOP:
			PrintIteratorLoop(Context, ocast<const IteratorLoopStmt*>(N), Depth);
			break;
		case AstKind::PREDICATE_LOOP:
			PrintPredicateLoop(Context, ocast<const PredicateLoopStmt*>(N), Depth);
			break;
		case AstKind::IF:
			PrintIf(Context, ocast<const IfStmt*>(N), Depth);
			break;
		case AstKind::BREAK:
		case AstKind::CONTINUE:
			PrintLoopControl(Context, ocast<const LoopControlStmt*>(N), Depth);
			break;
		case AstKind::DELETE:
			PrintDelete(Context, ocast<const DeleteStmt*>(N), Depth);
			break;
		case AstKind::IDENT_REF:
			PrintIdentRef(Context, ocast<const IdentRef*>(N), Depth);
			break;
		case AstKind::FIELD_ACCESSOR:
			PrintFieldAccessor(Context, ocast<const FieldAccessor*>(N), Depth);
			break;
		case AstKind::FUNC_CALL:
			PrintFuncCall(Context, ocast<const FuncCall*>(N), Depth);
			break;
		case AstKind::BINARY_OP:
			PrintBinaryOp(Context, ocast<const BinaryOp*>(N), Depth);
			break;
		case AstKind::UNARY_OP:
			PrintUnaryOp(Context, ocast<const UnaryOp*>(N), Depth);
			break;
		case AstKind::NUMBER_LITERAL:
			PrintNumberLiteral(Context, ocast<const NumberLiteral*>(N), Depth);
			break;
		case AstKind::ARRAY:
			PrintArray(Context, ocast<const Array*>(N), Depth);
			break;
		case AstKind::NULLPTR:
			PrintNull(Context, ocast<const Null*>(N), Depth);
			break;
		case AstKind::ARRAY_ACCESS:
			PrintArrayAccess(Context, ocast<const ArrayAccess*>(N), Depth);
			break;
		case AstKind::BOOL_LITERAL:
			PrintBool(Context, ocast<const BoolLiteral*>(N), Depth);
			break;
		case AstKind::SIZEOF_TYPE:
			PrintSizeofType(Context, ocast<const SizeofType*>(N), Depth);
			break;
		case AstKind::TYPE_CAST:
			PrintTypeCast(Context, ocast<const TypeCast*>(N), Depth);
			break;
		case AstKind::HEAP_ALLOC_TYPE:
			PrintHeapAllocType(Context, ocast<const HeapAllocType*>(N), Depth);
			break;
		case AstKind::THIS_REF:
			PrintThisRef(Context, ocast<const ThisRef*>(N), Depth);
			break;
		case AstKind::TERNARY_COND:
			PrintTernaryCond(Context, ocast<const TernaryCond*>(N), Depth);
			break;
		case AstKind::TUPLE:
			PrintTuple(Context, ocast<const Tuple*>(N), Depth);
			break;
		case AstKind::ERROR:
			PrintErrorNode();
			break;
		default:
			assert(!"Failed to implement node print case");
			break;
		}
	}
}

void june::PrintFileUnit(const JuneContext& Context, const FileUnit* FU) {
	llvm::outs() << "- (File Unit | file=\"" << FU->FL.PathKey << "\")";
	if (!FU->GlobalFuncs.empty()) {
		llvm::outs() << "\nGlobal Functions:";
		for (const auto& [_, Funcs] : FU->GlobalFuncs) {
			for (const FuncDecl* Func : Funcs) {
				llvm::outs() << "\n";
				PrintNode(Context, Func, 1);
			}
		}
	}
	if (!FU->GlobalVars.empty()) {
		llvm::outs() << "\nGlobal Varables:";
		for (const auto& [_, Global] : FU->GlobalVars) {
			llvm::outs() << "\n";
			PrintNode(Context, Global, 1);
		}
	}
	if (!FU->Records.empty()) {
		llvm::outs() << "\nRecords:";
		for (const auto& [_, Record] : FU->Records) {
			llvm::outs() << "\n";
			PrintNode(Context, Record, 1);
		}
	}
}