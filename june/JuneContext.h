#ifndef JUNE_CONTEXT_H
#define JUNE_CONTEXT_H

#include "Prolog.h"
#include "Identifier.h"
#include "Comptime.h"
#include "Ast.h"

#include <queue>
#include <llvm/ADT/StringMap.h>
#include <llvm/ADT/DenseMap.h>
#include <tuple>
#include <unordered_set>

namespace llvm {
	class LLVMContext;
	class Module;
	class Function;
	class DIBasicType;
	class DICompositeType;
	namespace Intrinsic {
		typedef unsigned ID;
	}
}

namespace june {

	struct Type;
	struct PointerType;
	struct RecordType;
	
	class JuneContext {
	public:
	
		JuneContext();

		~JuneContext();

		void Init(bool EmitDebugInfo);


		// If the Text matches the keyword then it
		// returns the keyword TokenKind, otherwise
		// returns 0.
		u16 GetKeywordKind(llvm::StringRef Text) const;

		// Retrieves a keyword as a string
		// from it's TokenKind
		llvm::StringRef GetKwAsString(u32 TokenKind) const;

		void RequestGen(Decl* D);
		u32 RequestGen(TypeBindList& Bindings, GenericFuncDecl* GenFunc);
		
		PointerType* GetCachedPointerType(Type* ElmTy) const;
		
		void RequestComptimeGen(ComptimeValue CV);

		void AddGlobalPostponedAssignment(VarDecl* Global, Expr* Assignment);

		// Integer Types
		Type* I8Type;
		Type* I16Type;
		Type* I32Type;
		Type* I64Type;
		Type* U8Type;
		Type* U16Type;
		Type* U32Type;
		Type* U64Type;
		Type* C8Type;
		Type* C16Type;
		Type* C32Type;
		Type* F32Type;
		Type* F64Type;
		// Other Types
		Type* ErrorType;
		Type* VoidType;
		Type* VoidPtrType;
		Type* BoolType;
		Type* NullType;
		Type* UndefinedType;

		bool CompileAsStandAlone = false;

		// Caching some pointer types to converse memory.
		llvm::DenseMap<Type*, PointerType*> StandardPointerCache;

		llvm::StringMap<FileUnit*> FileUnits;
		FileUnit* StringFU       = nullptr;
		FileUnit* SysFU          = nullptr;
		FuncDecl* MainEntryFunc  = nullptr;
		

		// Maps TokenKinds to Precedence of a binary operator
		llvm::DenseMap<u16, u16> BinaryOpsPrecedence;

		// 'main' identifier (for identifying entry points)
		Identifier MainIdentifier;
		// 'length' identifier (for identifying array lengths)
		Identifier LengthIdentifier;

		struct DeclGen {
			u32   TypeBindingId;
			Decl* D;
		};

		std::queue<DeclGen>      QuededDeclsToGen;
		
		std::unordered_set<Decl*> UncheckedDecls;

		// ----- LLVM -----
		llvm::LLVMContext& LLContext;
		llvm::Module&      LLJuneModule;
		u32                NumGeneratedLLGlobals    = 0;
		u32                NumGeneratedGlobalArrays = 0;
		u32                NumGeneratedGlobalVars   = 0;
		llvm::Function*    JuneInitGlobalsFunc;
		llvm::Function*    JuneStdLibInitFunc;
		llvm::DenseMap<RecordDecl*, llvm::Function*>    DefaultRecordInitFuncs;
		llvm::DenseMap<Identifier, llvm::Intrinsic::ID> LLVMIntrinsicsTable;

		struct GlobalPostponedAssignment {
			union {
				VarDecl*     Global;
				VarDeclList* DeclList;
			};
			bool  UsesDeclList = false;
			Expr* Assignment;
		};
		llvm::SmallVector<GlobalPostponedAssignment, 16> GlobalPostponedAssignments;
		
		// LLVM Debugging basic types
		llvm::DenseMap<RecordDecl*, llvm::DICompositeType*> DIRecordTys;

		llvm::DIBasicType* DITyI8;
		llvm::DIBasicType* DITyI16;
		llvm::DIBasicType* DITyI32;
		llvm::DIBasicType* DITyI64;
		llvm::DIBasicType* DITyU8;
		llvm::DIBasicType* DITyU16;
		llvm::DIBasicType* DITyU32;
		llvm::DIBasicType* DITyU64;
		llvm::DIBasicType* DITyC8;
		llvm::DIBasicType* DITyC16;
		llvm::DIBasicType* DITyC32;
		llvm::DIBasicType* DITyBool;
		llvm::DIBasicType* DITyF32;
		llvm::DIBasicType* DITyF64;

	private:
		friend class Compiler;

		llvm::DenseMap<llvm::StringRef, u16>& TokenKeywordMap;
		llvm::DenseMap<u16, llvm::StringRef>& TokenKwKindToStringMap;

		std::queue<ComptimeValue> ComptimeValues;

	};
}

#endif // JUNE_CONTEXT_H