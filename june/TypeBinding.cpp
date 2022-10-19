#include "TypeBinding.h"

#include "Types.h"
#include <stack>

static std::stack<u32> PrevBindingIdStack;

void june::BindTypes(GenericFuncDecl* GenFunc, u32 BindingId) {
	PrevBindingIdStack.push(GenFunc->CurBindingId);
	TypeBindList& Bindings = std::get<0>(GenFunc->BindingCache[BindingId]);

	for (auto& Binding : Bindings) {
		GenericType* GenTy = GenFunc->GenericTypes.find(std::get<0>(Binding))->second;
		// -- DEBUG
		// llvm::outs() << "Binding '" << GenTy->Name << "' with type '" << std::get<1>(Binding)->ToStr() << "'\n";
		GenTy->Bind(std::get<1>(Binding));
	}
}

void june::UnbindTypes(GenericFuncDecl* GenFunc) {
	u32 PrevBindingId = PrevBindingIdStack.top();
	PrevBindingIdStack.pop();
	if (PrevBindingId == INVALID_BINDING_ID) {
		for (auto [_, GenTy] : GenFunc->GenericTypes) {
			GenTy->Bind(nullptr);
		}
	} else {
		TypeBindList& PrevBindings = std::get<0>(GenFunc->BindingCache[PrevBindingId]);
		for (auto& Binding : PrevBindings) {
			GenericType* GenTy = GenFunc->GenericTypes.find(std::get<0>(Binding))->second;
			GenTy->Bind(std::get<1>(Binding));
		}
	}
}

bool june::IsGenericTypeNameBound(TypeBindList& Bindings, Identifier GenericName) {
	auto it = std::find_if(Bindings.begin(), Bindings.end(), [=](std::tuple<Identifier, Type*>& Binding) {
			return std::get<0>(Binding) == GenericName;
		});
	return it != Bindings.end();
}

u32 june::GetBindingsId(GenericFuncDecl* GenFunc, TypeBindList& Bindings) {
	u32 BindingId = 0;
	for (auto& BindingPair : GenFunc->BindingCache) {
		TypeBindList& Binding = std::get<0>(BindingPair);
		if (std::equal(Bindings.begin(), Bindings.end(),
			           Binding.begin(),
			[](std::tuple<Identifier, Type*>& LHS, std::tuple<Identifier, Type*>& RHS) {
				return std::get<0>(LHS) == std::get<0>(RHS) &&
					   std::get<1>(LHS)->is(std::get<1>(RHS));
			})) {
			return BindingId;
		}
		++BindingId;
	}
	return INVALID_BINDING_ID;
}

namespace june {

	void ResetExpr(Expr* E) {
		E->CastTy = nullptr;
		E->IsFoldable = true;
		E->IsComptimeCompat = true;
	}

	void ResetNode(AstNode* Node) {
		switch (Node->Kind) {
		case AstKind::IDENT_REF:
		case AstKind::NUMBER_LITERAL:
		case AstKind::NULLPTR:
		case AstKind::BOOL_LITERAL:
		case AstKind::SIZEOF_TYPE:
		case AstKind::THIS_REF: {
			ResetExpr(ocast<Expr*>(Node));
			break;
		}
		case AstKind::FUNC_DECL:
		case AstKind::GENERIC_FUNC_DECL: {
			FuncDecl* Func = ocast<GenericFuncDecl*>(Node);
			for (AstNode* Stmt : Func->Scope.Stmts) {
				ResetNode(Stmt);
			}
			break;
		}
		case AstKind::VAR_DECL: {
			VarDecl* Var = ocast<VarDecl*>(Node);
			Var->LLComptimeVal = nullptr;
			if (Var->Assignment) {
				ResetNode(Var->Assignment);
			}
			break;
		}
		case AstKind::INNER_SCOPE:
		case AstKind::ELSE_SCOPE: {
			InnerScopeStmt* InnerScope = ocast<InnerScopeStmt*>(Node);
			for (AstNode* Stmt : InnerScope->Scope.Stmts) {
				ResetNode(Stmt);
			}
			break;
		}
		case AstKind::RETURN: {
			ReturnStmt* Ret = ocast<ReturnStmt*>(Node);
			if (Ret->Val) {
				ResetNode(Ret->Val);
			}
			break;
		}
		case AstKind::RANGE_LOOP: {
			RangeLoopStmt* Loop = ocast<RangeLoopStmt*>(Node);
			if (Loop->Decl)
				ResetNode(Loop->Decl);
			if (Loop->Cond)
				ResetNode(Loop->Cond);
			if (Loop->Inc)
				ResetNode(Loop->Inc);
			break;
		}
		case AstKind::ITERATOR_LOOP: {
			IteratorLoopStmt* Loop = ocast<IteratorLoopStmt*>(Node);
			ResetNode(Loop->IterOnExpr);
			for (AstNode* Stmt : Loop->Scope.Stmts) {
				ResetNode(Stmt);
			}
			break;
		}
		case AstKind::PREDICATE_LOOP: {
			PredicateLoopStmt* Loop = ocast<PredicateLoopStmt*>(Node);
			if (Loop->Cond)
				ResetNode(Loop->Cond);
			for (AstNode* Stmt : Loop->Scope.Stmts) {
				ResetNode(Stmt);
			}
			break;
		}
		case AstKind::IF: {
			IfStmt* If = ocast<IfStmt*>(Node);
			if (If->Cond)
				ResetNode(If->Cond);
			for (AstNode* Stmt : If->Scope.Stmts) {
				ResetNode(Stmt);
			}
			if (If->Else)
				ResetNode(If->Else);
			break;
		}
		case AstKind::CONTINUE:
		case AstKind::BREAK:
			break;
		case AstKind::FIELD_ACCESSOR: {
			FieldAccessor* FA = ocast<FieldAccessor*>(Node);
			FA->IsArrayLength = false;
			ResetExpr(FA);
			ResetNode(FA->Site);
			break;
		}
		case AstKind::FUNC_CALL: {
			FuncCall* Call = ocast<FuncCall*>(Node);
			for (Expr* Arg : Call->Args) {
				ResetNode(Arg);
			}
			Call->CalledFunc = nullptr;
			Call->IsConstructorCall = false;
			ResetExpr(Call);
			break;
		}
		case AstKind::BINARY_OP: {
			BinaryOp* BinOp = ocast<BinaryOp*>(Node);
			ResetNode(BinOp->LHS);
			ResetNode(BinOp->RHS);
			ResetExpr(BinOp);
			break;
		}
		case AstKind::UNARY_OP: {
			UnaryOp* UOP = ocast<UnaryOp*>(Node);
			ResetNode(UOP->Val);
			ResetExpr(UOP);
			break;
		}
		case AstKind::ARRAY: {
			Array* Arr = ocast<Array*>(Node);
			for (u32 i = 0; i < Arr->NumElements; i++) {
				ResetNode(Arr->GetElement(i));
			}
			ResetExpr(Arr);
			break;
		}
		case AstKind::ARRAY_ACCESS: {
			ArrayAccess* AA = ocast<ArrayAccess*>(Node);
			ResetNode(AA->Site);
			ResetExpr(AA);
			break;
		}
		case AstKind::TYPE_CAST: {
			TypeCast* Cast = ocast<TypeCast*>(Node);
			ResetNode(Cast->Val);
			ResetExpr(Cast);
			break;
		}
		case AstKind::HEAP_ALLOC_TYPE: {
			HeapAllocType* HeapAlloc = ocast<HeapAllocType*>(Node);
			ResetExpr(HeapAlloc);
			break;
		}
		case AstKind::TERNARY_COND: {
			TernaryCond* Cond = ocast<TernaryCond*>(Node);
			ResetNode(Cond->Cond);
			ResetNode(Cond->Val1);
			ResetNode(Cond->Val2);
			ResetExpr(Cond);
			break;
		}
		case AstKind::TUPLE: {
			Tuple* Tup = ocast<Tuple*>(Node);
			for (Expr* Val : Tup->Values) {
				ResetNode(Val);
			}
			ResetExpr(Tup);
			break;
		}
		default:
			assert(!"Unimplemented node reset");
			break;
		}
	}
}

void june::ResetGenericDecl(Decl* D) {
	ResetNode(D);
}