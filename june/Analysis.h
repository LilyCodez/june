#ifndef JUNE_ANALYSIS_H
#define JUNE_ANALYSIS_H

#include "Ast.h"
#include "Logger.h"

namespace june {

	class JuneContext;
	struct Type;

	class Analysis {
	public:

		explicit Analysis(JuneContext& context, Logger& log, bool forCodeGen);

		static void ResolveRecordTypes(JuneContext& Context, FileUnit* FU);

		static void CheckRecords(JuneContext& Context, FileUnit* FU);

		static void ReportInvalidFUStmts(FileUnit* FU);

		void CheckFuncDecl(FuncDecl* Func);
		void CheckGenericFuncDecl(GenericFuncDecl* GenFunc, u32 BindingId);

		void CheckVarDecl(VarDecl* Var);

		void CheckVarDeclList(VarDeclList* DeclList);

		void CheckRecordDecl(RecordDecl* Record);

		void CheckNode(AstNode* Node);

	private:

		JuneContext& Context;
		Logger&      Log;

		FileUnit*   FU;
		FuncDecl*   CFunc   = nullptr;
		RecordDecl* CRecord = nullptr;
		VarDecl*    CField  = nullptr;
		VarDecl*    CGlobal = nullptr;

		// True if checking stuff that will be used
		// for code generation
		bool ForCodeGen = false;

		struct Scope {
			Scope* Parent = nullptr;
			// This refers to anything that
			// prevents the usual flow of
			// execution such as 'break',
			// 'continue', 'return'
			bool FoundTerminal = false;
			// Keeping track of returns
			// as a way of find out
			// if a function definitatively
			// returns.
			bool AllPathsReturn = false;

			Scope(AstNode* node)
				: Node(node) {}
				
			AstNode* Node = nullptr;
		} *LocScope = nullptr;

		// Every time a loop is entered this is incremented,
		// and decremented when existed
		u32 LoopDepth = 0;

		bool TypeHasFieldsWithAssignment(Type* Ty);
		void CheckRecordsInType(SourceLoc ErrLoc, Type* Ty);
		
		bool CheckInferedTypeAssignment(AstNode* Decl, Expr* Assignment);

		void CheckScope(const LexScope& LScope, Scope& NewScope);
	
		bool CheckInnerScope(InnerScopeStmt* InnerScope);
		void CheckReturn(ReturnStmt* Ret);
		void CheckRangeLoop(RangeLoopStmt* Loop);
		void CheckIteratorLoop(IteratorLoopStmt* Loop);
		void CheckPredicateLoop(PredicateLoopStmt* Loop);
		bool CheckIf(IfStmt* If);
		void CheckCond(Expr* Cond, SourceLoc ExpandedCondLoc, const c8* PreText);
		void CheckLoopControl(LoopControlStmt* LoopControl);
		void CheckDelete(DeleteStmt* Delete);

		void CheckIdentRef(IdentRef* IRef, bool GivePrefToFuncs);
		void CheckIdentRefCommon(IdentRef* IRef, bool GivePrefToFuncs, FileUnit* FUToLookup, RecordDecl* RecordToLookup);
		void CheckFieldAccessor(FieldAccessor* FA, bool GivePrefToFuncs);
		void CheckFuncCall(FuncCall* Call);
		void CheckDefaultRecordInitFuncCall(FuncCall* Call, RecordDecl* Record);
		void DisplayErrorForNamedArgsSlotTaken(FuncCall* Call, bool UseFieldIdx);
		
		FuncDecl* FindBestFuncCallCanidate(FuncsList* Canidates, FuncCall* Call);
		template<bool IsGenericFuncT>
		bool CompareAsCanidate(FuncCall* Call, FuncDecl* Canidate, u32& NumConflicts);
		
		FuncDecl* FindBestFuncCallCanidateWithNamedArgs(FuncsList* Canidates, FuncCall* Call);
		template<bool IsGenericFuncT>
		bool CompareAsNamedArgCandiate(FuncCall* Call, FuncDecl* Canidate, u32& NumConflicts, bool& CanidateHasNameSlotTaken);

		void CheckBinaryOp(BinaryOp* BinOp);
		void CheckUnaryOp(UnaryOp* UOP);
		void CheckArray(Array* Arr);
		void CheckArrayAccess(ArrayAccess* AA);
		void CheckTypeCast(TypeCast* Cast);
		void CheckHeapAllocType(HeapAllocType* HeapAlloc);
		void CheckThisRef(ThisRef* This);
		void CheckTernaryCond(TernaryCond* Ternary);
		void CheckTuple(Tuple* Tup);

		bool IsAssignableTo(Type* ToTy, Expr* FromExpr);
		bool IsAssignableTo(Type* ToTy, Type* FromTy, Expr* FromExpr, bool LossenNumConversion);
		bool IsCastableTo(Type* ToTy, Type* FromTy);
		void CreateCast(Expr* E, Type* ToType);
		void CreateArrayElementsCast(Type* BaseType, Array* Arr);

		bool IsLValue(Expr* E);

		bool IsComparable(Type* Ty);

		void EnsureChecked(SourceLoc ELoc, VarDecl* Var);
		void EnsureChecked(SourceLoc ELoc, RecordDecl* Record);
		void DisplayCircularDep(Decl* StartDep);

		RecordType* GetRecordType(RecordDecl* Record);

		bool RequestRecordDestructionGen(RecordDecl* Record);
		bool TypeNeedsDestructionAndGenDestructors(Type* Ty);
	
		void AssignTo(Expr* Assignment, Type* ToTy, SourceLoc AssignLoc);

		void AddMarkErrorMsgAboutBindLoc() {
			if (CFunc->is(AstKind::GENERIC_FUNC_DECL)) {
				GenericFuncDecl* GenFunc = ocast< GenericFuncDecl*>(CFunc);
				
				TypeBindList& Bindings = std::get<0>(GenFunc->BindingCache[GenFunc->CurBindingId]);
				FileUnit* OriginalFU      = Bindings.OriginalFileFU;
				SourceLoc OriginalBindLoc = Bindings.OriginalBindingLoc;

				while (Bindings.RecursiveCallGenericFunc) {

					GenFunc  = Bindings.RecursiveCallGenericFunc;
					Bindings = std::get<0>(GenFunc->BindingCache[Bindings.RecursiveCallBindingId]);

					OriginalFU      = Bindings.OriginalFileFU;
					OriginalBindLoc = Bindings.OriginalBindingLoc;

				}

				Log.AddMarkErrorMsg(OriginalFU->FL.ErrorPathKey, OriginalBindLoc,
					"Type(s) originally bound here");
				
			}
		}

		void Error(SourceLoc Loc, const c8* Msg) {
			Log.BeginError(Loc, Msg);
			AddMarkErrorMsgAboutBindLoc();
			Log.EndError();
		}

		template<typename... Targs>
		void Error(SourceLoc Loc, const c8* Fmt, Targs&&... Args) {
			Log.BeginError(Loc, Fmt, std::forward<Targs>(Args)...);
			AddMarkErrorMsgAboutBindLoc();
			Log.EndError();
		}

		void Error(AstNode* N, const c8* Msg) {
			Log.BeginError(N->Loc, Msg);
			AddMarkErrorMsgAboutBindLoc();
			Log.EndError();
		}

		template<typename... Targs>
		void Error(AstNode* N, const c8* Fmt, Targs&&... Args) {
			Log.BeginError(N->Loc, Fmt, std::forward<Targs>(Args)...);
			AddMarkErrorMsgAboutBindLoc();
			Log.EndError();
		}
	};
}

#endif // JUNE_ANALYSIS_H