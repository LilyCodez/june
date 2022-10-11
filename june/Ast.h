#ifndef JUNE_AST_H
#define JUNE_AST_H

#include "Identifier.h"
#include "Logger.h"
#include "RecordLocation.h"

#include <llvm/ADT/StringRef.h>
#include <llvm/ADT/DenseMap.h>

namespace llvm {
	class Function;
	class Value;
	class StructType;
	class DICompileUnit;
	class Type;
	namespace Intrinsic {
		typedef unsigned ID;
	}
}

namespace june {

	struct FuncDecl;
	struct VarDecl;
	struct RecordDecl;
	struct Type;
	struct Expr;
	struct AstNode;
	struct RecordType;
	class DebugInfoEmitter;

	using ScopeStmts = llvm::SmallVector<AstNode*, 8>;
	using FuncsList  = llvm::SmallVector<FuncDecl*, 4>;

	enum class AstKind {

		ERROR,

		FUNC_DECL,
		VAR_DECL,
		RECORD_DECL,

		INNER_SCOPE,
		RETURN,
		RANGE_LOOP,
		PREDICATE_LOOP,
		IF,
		BREAK,
		CONTINUE,

		IDENT_REF,
		FUNC_CALL,
		BINARY_OP,
		UNARY_OP,
		NUMBER_LITERAL,
		ARRAY,
		NULLPTR,
		ARRAY_ACCESS,
		FIELD_ACCESSOR,
		BOOL_LITERAL,
		SIZEOF_TYPE,
		TYPE_CAST,
		HEAP_ALLOC_TYPE,
		THIS_REF,
		TERNARY_COND,

	};

	//===-------------------------------===//
	// Modifiers
	//===-------------------------------===//

	namespace mods {
		enum Mods {
			MODS_START = 0x01,

			NATIVE     = 0x01,

			MODS_END = NATIVE,
		};

		typedef u16 Mod;
	}

	struct FileUnit {

		bool HasBeenParsed = false;

		FileLocation      FL;
		SourceBuf         SBuf;
		Logger            Log;
		DebugInfoEmitter* DIEmitter;
		
		// When parsing a file record types
		// cannot be resolved until the file
		// has been fully parsed. This structure
		// may represent a the record type before
		// and after it has been qualified be
		// searching for it's reference.
		struct QualifyingRecordType {
			RecordType* RecType;
			RecordDecl* RelRecord = nullptr;
			// Only used if the record type cannot be found.
			SourceLoc ErrorLoc;
		};

		// The reason for the tuple is that during parsing
		// it cannot be known if a location is relative
		// or absolute. However, relative to a certain record
		// scope all declared record types must be the same.
		llvm::DenseMap<std::tuple<RecordDecl*, RecordLocation>,
			QualifyingRecordType> QualifyingRecordTypes;

		// list
		//  < qualifying-type, key-to-map >
		
		llvm::DenseMap<Identifier, FileUnit*>       Imports;
		llvm::DenseMap<Identifier, FuncsList>       GlobalFuncs;
		llvm::DenseMap<Identifier, VarDecl*>        GlobalVars;
		llvm::DenseMap<RecordLocation, RecordDecl*> Records;
		
		enum class StmtScopeKind {
			GLOBAL,
			RECORD,
		};
		llvm::SmallVector<std::tuple<StmtScopeKind, AstNode*>, 8> InvalidStmts;
		
		FileUnit(llvm::raw_fd_ostream& ErrOS, const std::string& filePath)
			: Log(SBuf, ErrOS, filePath) {}

	};

	struct AstNode {

		SourceLoc Loc;

		AstKind Kind;

		AstNode(AstKind kind) : Kind(kind) {}

		// Checks if the statement is of the given kind
		bool is(AstKind kind) { return kind == Kind; }

		// Checks if the statement is not of the given kind
		bool isNot(AstKind kind) { return kind != Kind; }

	};

	struct LexScope {
		SourceLoc StartLoc;
		SourceLoc EndLoc;
		ScopeStmts Stmts;
	};

	struct Decl : AstNode {
		
		FileUnit*  FU;
		Identifier Name;
		mods::Mod  Mods;
		Decl*      DepD = nullptr;
		bool       GenRequestedAlready = false;
		bool       IsBeingChecked = false;
		bool       HasBeenChecked = false;
		
		Decl(AstKind kind) : AstNode(kind) {}
	
	};

	struct FuncDecl : Decl {

		llvm::SmallVector<VarDecl*, 2> Params;
		// Storing the variables that appear in the
		// function so they can be allocated at the
		// start of the function
		llvm::SmallVector<VarDecl*, 4> AllocVars;

		Type* RetTy;

		// If the function is a member function this
		// will be non-null.
		RecordDecl* ParentRecord = nullptr;

		bool IsMainFunc         = false;
		u32 NumReturns = 0;

		// Zero means it is not a LLVMIntrinsic.
		llvm::Intrinsic::ID LLVMIntrinsicID = 0;
		llvm::Function* LLAddress = nullptr;

		LexScope Scope;

		FuncDecl() : Decl(AstKind::FUNC_DECL) {}

	};

	struct VarDecl : Decl {

		Type* Ty;

		// nullptr means there is no assignment
		Expr* Assignment = nullptr;

		// Address in memory generated by llvm
		llvm::Value* LLAddress = nullptr;

		RecordDecl* Record = nullptr;
		u32 FieldIdx = -1;
		u32 ParamIdx = -1;
		bool UsesInferedType = false;
		bool IsGlobal        = false;

		VarDecl() : Decl(AstKind::VAR_DECL) {}

	};

	struct RecordDecl : Decl {

		RecordDecl* Parent = nullptr;

		llvm::SmallVector<VarDecl*>           FieldsByIdxOrder;
		llvm::DenseMap<Identifier, VarDecl*>  Fields;
		llvm::DenseMap<Identifier, FuncsList> Funcs; // member functions
		FuncsList                             Constructors;

		llvm::StructType* LLStructTy = nullptr;
		bool FieldsHaveAssignment    = false;

		RecordDecl() : Decl(AstKind::RECORD_DECL) {}

	};

	struct InnerScopeStmt : AstNode {

		LexScope Scope;

		InnerScopeStmt() : AstNode(AstKind::INNER_SCOPE) {}

	};

	struct ReturnStmt : AstNode {

		Expr* Val = nullptr;

		ReturnStmt() : AstNode(AstKind::RETURN) {}

	};

	struct IfStmt : AstNode {

		Expr*      Cond;
		AstNode*   Else = nullptr; // 'else' of 'else if'
		LexScope   Scope;

		IfStmt() : AstNode(AstKind::IF) {}

	};

	//  ex.  'loop i :i32 = 0; i < 10; i++'
	struct RangeLoopStmt : AstNode {

		VarDecl*   Decl = nullptr;
		Expr*      Cond = nullptr;
		Expr*      Inc  = nullptr;
		LexScope   Scope;

		RangeLoopStmt() : AstNode(AstKind::RANGE_LOOP) {}

	};

	//  ex  'loop a < 41'
	struct PredicateLoopStmt : AstNode {

		Expr*      Cond = nullptr;
		LexScope   Scope;

		PredicateLoopStmt() : AstNode(AstKind::PREDICATE_LOOP) {}

	};

	struct LoopControlStmt : AstNode {

		// How many loops to break/continue from
		u32 LoopCount = 1;

		LoopControlStmt()
			: AstNode(AstKind::ERROR) {}

	};

	struct Expr : AstNode {

		// Typically set during type checking.
		Type* Ty;
		// Somtimes an expression has a
		// cast type because LLVM expects
		// all types to be the same when
		// applying operators to them.
		//
		// The cast type behaves like an extra
		// node inserted into the tree as a way
		// to resolve the conflict.
		//
		//   Transformation:
		//         +                       +
		//       /   \         =>        /   \
		//      /     \                 /     \
		//  num(i16)  num(i32)    cast(i32)   num(i32)
		//                             |
		//                         num(i16)
		Type* CastTy = nullptr;

		// This indicates if the value
		// of the expression can be "folded"
		// by llvm. This means the value
		// can result in a constant value at
		// compile time rather than requiring
		// runtime to determine the expression's
		// result.
		bool IsFoldable = true;

		Expr(AstKind kind)
			: AstNode(kind) {}

	};

	// Generated in place of a expr
	// if the expression could not
	// be determined
	struct ErrorNode : Expr {
		ErrorNode()
			: Expr(AstKind::ERROR) {}
	};

	// Ex. 'abc' 'func'
	struct IdentRef : Expr {

		Identifier Ident;

		enum {
			VAR,
			FUNCS,  // Plural because of function overloading.
			FILE_UNIT,
			NOT_FOUND,
			RECORD
		} RefKind = NOT_FOUND;

		union {
			VarDecl*    VarRef;
			FuncsList*  FuncsRef;
			FileUnit*   FileUnitRef;
			RecordDecl* RecordRef;
		};

		IdentRef()
			: Expr(AstKind::IDENT_REF) {}

	};

	// Ex.  'a.b'
	struct FieldAccessor : IdentRef {

		// Request for the length of an array.
		bool IsArrayLength = false;

		Expr* Site;

		FieldAccessor() : IdentRef() {
			Kind = AstKind::FIELD_ACCESSOR;
		}
	};

	struct FuncCall : Expr {

		struct NamedArg {
			SourceLoc  Loc;
			VarDecl*   VarRef = nullptr;
			Identifier Name;
			Expr*      AssignValue;
		};
		
		llvm::SmallVector<Expr*, 2>    Args;
		llvm::SmallVector<NamedArg, 2> NamedArgs;

		Expr*     Site;
		FuncDecl* CalledFunc = nullptr;
		bool IsConstructorCall = false;

		FuncCall()
			: Expr(AstKind::FUNC_CALL) {}

	};

	// Ex. '4 + 5' '63 % 22'
	struct BinaryOp : Expr {

		u16   Op;
		Expr* LHS;
		Expr* RHS;

		BinaryOp()
			: Expr(AstKind::BINARY_OP) {}

	};

	// Ex. '!true' '-44'
	struct UnaryOp : Expr {

		u16   Op;
		Expr* Val;

		UnaryOp()
			: Expr(AstKind::UNARY_OP) {}

	};

	// Ex. '521'  '3.5'
	struct NumberLiteral : Expr {

		union {
			s64 SignedIntValue;
			u64 UnsignedIntValue;
			float F32Value;
			double F64Value;
		};

		NumberLiteral()
			: Expr(AstKind::NUMBER_LITERAL) {}

	};

	struct Array : Expr {

		// This is needed to ensure that the size
		// of the array at a certain nesting level is
		// identifical to all the other arrays at the
		// same nesting level.
		//
		// Example:
		//    [ [ 2, 54, 2 ], [ 66 ] ]
		//
		//     At nesting level 0 there is 1 array and
		//     at nesting level 1 there are 2 arrays.
		//     At the 2nd nesting level the '[ 66 ]' is
		//     a smaller length than '[ 2, 54, 2 ]' so
		//     all arrays at the 2nd nesting level recieve
		//     the maximum length at that level which is
		//     set into RequiredNumElements.
		//
		// Note: In the case of assigning directly to a
		//       dynamic array the RequiredNumElements
		//       is allowed to be ignored.
		u32 RequiredNumElements;

		// The number of generated unique elements in the array.
		u32 NumElements;

		virtual Expr* GetElement(u32 Idx) const = 0;

		Array()
			: Expr(AstKind::ARRAY) {}

	};

	// Ex. '{ 5, 14, 235, 12 }'
	struct ExprFilledArray : Array {
		
		llvm::SmallVector<Expr*, 4> Elements;

		Expr* GetElement(u32 Idx) const override {
			return Elements[Idx];
		};
	};

	// Ex. '"hello world!"'
	struct String8Literal : Array {

		std::string Characters;

		// Just need one then changes value based on the requested index
		NumberLiteral* ElmSlot;

		Expr* GetElement(u32 Idx) const override {
			ElmSlot->SignedIntValue = Characters[Idx];
			return ElmSlot;
		}
	};

	struct Null : Expr {
		Null() : Expr(AstKind::NULLPTR) {}
	};

	// Ex.  'a[24]'
	struct ArrayAccess : Expr {

		Expr* Site;
		Expr* Index;

		ArrayAccess()
			: Expr(AstKind::ARRAY_ACCESS) {}

	};

	// Ex. 'true' or 'false'
	struct BoolLiteral : Expr {

		bool tof;

		BoolLiteral()
			: Expr(AstKind::BOOL_LITERAL) {}
	
	};

	// Ex. 'sizeof(i32)'
	struct SizeofType : Expr {

		Type* TyToGetSizeof;

		SizeofType()
			: Expr(AstKind::SIZEOF_TYPE) {}

	};

	// Ex. cast(i32)
	struct TypeCast : Expr {
		
		Type* ToTy;
		Expr* Val;

		TypeCast()
			: Expr(AstKind::TYPE_CAST) {}

	};

	// Ex.  'new i32'
	struct HeapAllocType : Expr {
		
		Type* TypeToAlloc;

		HeapAllocType()
			: Expr(AstKind::HEAP_ALLOC_TYPE) {}

	};

	struct ThisRef : Expr {
		ThisRef()
			: Expr(AstKind::THIS_REF) {}
	};

	struct TernaryCond : Expr {

		Expr* Cond;
		Expr* Val1;
		Expr* Val2;

		TernaryCond()
			: Expr(AstKind::TERNARY_COND) {}

	};
}

#endif // JUNE_AST_H