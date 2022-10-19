#include "IRGen.h"

#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Verifier.h>

#include "Types.h"
#include "Tokens.h"
#include "TypeBinding.h"

#include <unordered_set>

//===-------------------------------===//
// Helper Functions
//===-------------------------------===//

inline llvm::Constant* GetLLInt8(s32 value, llvm::LLVMContext& LLContext) {
	return llvm::ConstantInt::get(
		llvm::IntegerType::getInt8Ty(LLContext), value, true);
}
inline llvm::Constant* GetLLUInt8(u32 value, llvm::LLVMContext& LLContext) {
	return llvm::ConstantInt::get(
		llvm::IntegerType::getInt8Ty(LLContext), value, false);
}
inline llvm::Constant* GetLLInt16(s32 value, llvm::LLVMContext& LLContext) {
	return llvm::ConstantInt::get(
		llvm::IntegerType::getInt16Ty(LLContext), value, true);
}
inline llvm::Constant* GetLLUInt16(u32 value, llvm::LLVMContext& LLContext) {
	return llvm::ConstantInt::get(
		llvm::IntegerType::getInt16Ty(LLContext), value, false);
}
inline llvm::Constant* GetLLInt32(s32 value, llvm::LLVMContext& LLContext) {
	return llvm::ConstantInt::get(
		llvm::IntegerType::getInt32Ty(LLContext), value, true);
}
inline llvm::Constant* GetLLUInt32(u32 value, llvm::LLVMContext& LLContext) {
	return llvm::ConstantInt::get(
		llvm::IntegerType::getInt32Ty(LLContext), value, false);;
}
inline llvm::Constant* GetLLInt64(s64 value, llvm::LLVMContext& LLContext) {
	return llvm::ConstantInt::get(
		llvm::IntegerType::getInt64Ty(LLContext), value, true);
}
inline llvm::Constant* GetLLUInt64(u64 value, llvm::LLVMContext& LLContext) {
	return llvm::ConstantInt::get(
		llvm::IntegerType::getInt64Ty(LLContext), value, false);
}

struct LLValTypePrinter {
	LLValTypePrinter(llvm::Value* arg)
		: Arg(arg) {}

	llvm::Value* Arg;
	void PrintLLType(llvm::raw_ostream& OS, llvm::Value* LLValue) const {
		LLValue->getType()->print(OS);
	}
};

struct LLTypePrinter {
	LLTypePrinter(llvm::Type* arg)
		: Arg(arg) {}

	llvm::Type* Arg;
	void PrintLLType(llvm::raw_ostream& OS, llvm::Type* LLType) const {
		LLType->print(OS);
	}
};

llvm::raw_ostream& operator<<(llvm::raw_ostream& OS, LLValTypePrinter& Printer) {
	Printer.PrintLLType(OS, Printer.Arg);
	return OS;
}

llvm::raw_ostream& operator<<(llvm::raw_ostream& OS, LLTypePrinter& Printer) {
	Printer.PrintLLType(OS, Printer.Arg);
	return OS;
}





june::IRGen::IRGen(JuneContext& context, bool emitDebugInfo, bool displayLLVMIR)
	: Context(context),
	  LLContext(context.LLContext),
	  LLModule(context.LLJuneModule),
	  Builder(context.LLContext),
	  EmitDebugInfo(emitDebugInfo),
	  DisplayLLVMIR(displayLLVMIR) {
}



llvm::Type* june::GenType(JuneContext& Context, Type* Ty) {
	llvm::LLVMContext& LLContext = Context.LLContext;
	switch (Ty->GetKind()) {
	case TypeKind::I8:
	case TypeKind::U8:
	case TypeKind::C8:
		return llvm::Type::getInt8Ty(LLContext);
	case TypeKind::I16:
	case TypeKind::U16:
	case TypeKind::C16:
		return llvm::Type::getInt16Ty(LLContext);
	case TypeKind::I32:
	case TypeKind::U32:
	case TypeKind::C32:
		return llvm::Type::getInt32Ty(LLContext);
	case TypeKind::I64:
	case TypeKind::U64:
		return llvm::Type::getInt64Ty(LLContext);
	case TypeKind::F32:
		return llvm::Type::getFloatTy(LLContext);
	case TypeKind::F64:
		return llvm::Type::getDoubleTy(LLContext);
	case TypeKind::VOID:
		return llvm::Type::getVoidTy(LLContext);
	case TypeKind::BOOL:
		return llvm::Type::getInt1Ty(LLContext);
	case TypeKind::FIXED_ARRAY: {
		FixedArrayType* AT = Ty->AsFixedArrayType();
		return llvm::ArrayType::get(GenType(Context, AT->ElmTy), AT->Length);
	}
	case TypeKind::POINTER: {
		PointerType* PT = Ty->AsPointerType();
		switch (PT->ElmTy->GetKind()) {
		case TypeKind::POINTER:
			return llvm::PointerType::get(GenType(Context, PT->ElmTy), 0);
		case TypeKind::I8:
		case TypeKind::U8:
		case TypeKind::C8:
		case TypeKind::VOID:
			return llvm::Type::getInt8PtrTy(LLContext);
		case TypeKind::I16:
		case TypeKind::U16:
		case TypeKind::C16:
			return llvm::Type::getInt16PtrTy(LLContext);
		case TypeKind::I32:
		case TypeKind::U32:
		case TypeKind::C32:
			return llvm::Type::getInt32PtrTy(LLContext);
		case TypeKind::I64:
		case TypeKind::U64:
			return llvm::Type::getInt64PtrTy(LLContext);
		case TypeKind::F32:
			return llvm::Type::getFloatPtrTy(LLContext);
		case TypeKind::F64:
			return llvm::Type::getDoublePtrTy(LLContext);
		default:
			return llvm::PointerType::get(GenType(Context, PT->ElmTy), 0);
		}
	}
	case TypeKind::RECORD: {
		RecordType* RecordTy = Ty->AsRecordType();
		return GenRecordType(Context, RecordTy->Record);
	}
	case TypeKind::FUNCTION: {
		FunctionType* FuncTy = Ty->AsFunctionType();
		llvm::SmallVector<llvm::Type*, 4> LLParamTypes;
		for (Type* ParamType : FuncTy->ParamTypes) {
			llvm::Type* LLTy = GenType(Context, ParamType);
			if (ParamType->GetKind() == TypeKind::FIXED_ARRAY) {
				LLParamTypes.push_back(llvm::PointerType::get(LLTy, 0));
			} else {
				LLParamTypes.push_back(LLTy);
			}
		}
		llvm::Type* LLRetType = GenType(Context, FuncTy->RetTy);
		bool IsVarArgs = false;
		return llvm::PointerType::get(llvm::FunctionType::get(LLRetType, LLParamTypes, IsVarArgs), 0);
	}
	case TypeKind::TUPLE: {
		
		std::vector<llvm::Type*> LLStructValTypes;
		
		TupleType* TupleTy = Ty->AsTupleType();
		for (Type* ValTy : TupleTy->SubTypes) {
			LLStructValTypes.push_back(GenType(Context, ValTy));
		}
		llvm::StructType* LLStructTy = llvm::StructType::get(Context.LLContext, LLStructValTypes);
		
		return LLStructTy;
	}
	default:
		assert(!"Unimplemented GenType() case");
		return nullptr;
	}
}

llvm::Type* june::GenRecordType(JuneContext& Context, RecordDecl* Record) {
	if (Record->LLStructTy) // Record type already generated.
		return Record->LLStructTy;

	llvm::StructType* LLStructTy = llvm::StructType::create(Context.LLContext);
	Record->LLStructTy = LLStructTy; // Set early to prevent endless recursive

	std::vector<llvm::Type*> LLStructFieldTypes;
	LLStructFieldTypes.resize(Record->Fields.size());
	if (!Record->Fields.empty()) {
		for (VarDecl* Field : Record->FieldsByIdxOrder) {
			LLStructFieldTypes[Field->FieldIdx] = GenType(Context, Field->Ty);
		}
	} else {
		LLStructFieldTypes.push_back(llvm::Type::getInt8Ty(Context.LLContext));
	}
		
	LLStructTy->setBody(LLStructFieldTypes);
	std::string Name = std::string(Record->Name.Text);
	Name += ".rjune";
	LLStructTy->setName(Name);
		
	// TODO:!
	//if (Context.DisplayLLVMIR) {
	//	LLStructTy->print(llvm::outs());
	//	const llvm::StructLayout* LLStructLayout = LLModule.getDataLayout().getStructLayout(LLStructTy);
	//	llvm::Align Alignment = LLStructLayout->getAlignment();
	//	u64 SizeOfInBytes = LLStructLayout->getSizeInBytes();
	//	llvm::outs() << " alignment: " << Alignment.value() << ", sizeof: " << SizeOfInBytes;
	//
	//	llvm::outs() << "\n\n";
	//}
		
	return LLStructTy;
}


void june::IRGen::GenFunc(FuncDecl* Func) {

	// -- DEBUG
	// llvm::outs() << "generating function: " << Func->Name << '\n';

	CFunc = Func;

	GenFuncDecl(Func);

	GenFuncBody(Func);

	if (DisplayLLVMIR && !Func->LLVMIntrinsicID) {
		Func->LLAddress->print(llvm::outs());
		llvm::outs() << '\n';
	}

	if (Func->LLAddress && !(Func->Mods & mods::Mods::NATIVE)) {
		// -- DEBUG
		// llvm::verifyFunction(*Func->LLAddress);
	}
}

void june::IRGen::GenGenericFunc(GenericFuncDecl* Func, u32 BindingId) {
	
	CFunc = Func;
	
	BindTypes(Func, BindingId);

	Func->LLAddress = std::get<1>(Func->BindingCache[BindingId]);
	if (!Func->LLAddress) {
		GenFuncDecl(Func);
	}

	GenFuncBody(Func);

	UnbindTypes(Func);

	if (DisplayLLVMIR) {
		Func->LLAddress->print(llvm::outs());
		llvm::outs() << '\n';
	}

	if (Func->LLAddress) {
		// -- DEBUG
		//llvm::verifyFunction(*Func->LLAddress);
	}

	Func->LLAddress = nullptr;
}

void june::IRGen::GenGlobalVar(VarDecl* Global) {
	
	if (Global->Mods & mods::COMPTIME) {
		// Computed on request.
		return;
	}

	GenGlobalVarDecl(Global);

	if (Global->Mods & mods::Mods::NATIVE) {
		if (DisplayLLVMIR) {
			Global->LLAddress->print(llvm::outs());
			llvm::outs() << '\n';
		}
		return; // Global variables do not get initialized.
	}

	llvm::GlobalVariable* LLGVar =
		llvm::cast<llvm::GlobalVariable>(Global->LLAddress);

	LLGVar->setInitializer(GenGlobalConstVal(Global));

	if (Global->Assignment) {
		if (!Global->Assignment->IsFoldable) {
			// Could not be simply folded into a value so it
			// requires further initialization
			Context.GlobalPostponedAssignments.push_back(Global);
		}
	} else if (Global->Ty->GetKind() == TypeKind::FIXED_ARRAY) {
		if (Global->Ty->AsFixedArrayType()->GetBaseType()->GetKind() == TypeKind::RECORD) {
			// The objects of the array need to have their constructors
			// called.
			Context.GlobalPostponedAssignments.push_back(Global);
		}
	} else if (Global->Ty->GetKind() == TypeKind::RECORD) {
		// Need to default initialize a record
		Context.GlobalPostponedAssignments.push_back(Global);
	}

	if (DisplayLLVMIR) {
		LLGVar->print(llvm::outs());
		llvm::outs() << '\n';
	}
}

void june::IRGen::GenFuncDecl(FuncDecl* Func) {
	if (Func->LLAddress) return;

	if (Func->Mods & mods::Mods::NATIVE) {
		// Checking if the function is an intrinsic function.
		// If it is then there is no reason to create it.
		auto it = Context.LLVMIntrinsicsTable.find(Func->Name);
		if (it != Context.LLVMIntrinsicsTable.end()) {
			Func->LLVMIntrinsicID = it->second;
			return;
		}
	}

	bool RVO = FuncNeedsRVO(Func);

	llvm::Type* LLRetTy = RVO              ? llvm::Type::getVoidTy(LLContext) :
                          Func->IsMainFunc ? llvm::Type::getInt32Ty(LLContext)
		                                   : GenType(Func->RetTy);

	// TODO: This could probably be converted to an array
	// since the size is likely known.
	llvm::SmallVector<llvm::Type*, 4> LLParamTypes;

	if (Func->Record) {
		// Member functions recieve pointers to the record they
		// are contained inside of.
		LLParamTypes.push_back(llvm::PointerType::get(GenRecordType(Context, Func->Record), 0));
	}

	if (RVO) {
		// Instead of returning the structure we pass a reference
		// into the function of the structure and return void.
		if (Func->RetTy->GetKind() == TypeKind::RECORD) {
			LLParamTypes.push_back(llvm::PointerType::get(
				GenRecordType(Context, Func->RetTy->AsRecordType()->Record), 0));
		} else {
			LLParamTypes.push_back(llvm::PointerType::get(GenType(Func->RetTy), 0));
		}
	}

	for (VarDecl* Param : Func->Params) {
		TypeKind K = Param->Ty->GetKind();
		if (K == TypeKind::FIXED_ARRAY) {
			// Want to pass the array via a pointer so
			// that it is passed by reference.
			LLParamTypes.push_back(llvm::PointerType::get(GenType(Param->Ty), 0));
		} else {
			LLParamTypes.push_back(GenType(Param->Ty));
		}
	}

	bool IsVarArgs = false;
	llvm::FunctionType* LLFuncType =
		llvm::FunctionType::get(LLRetTy, LLParamTypes, IsVarArgs);

	// TODO: Create an abstract name mangler then
	// name mangle based on the mangler

	std::string LLFuncName = std::string(Func->Name.Text);
	if (!(Func->Mods & mods::Mods::NATIVE) && !Func->IsMainFunc) {
		// Adding .june to prevent conflicts with external dependencies.
		LLFuncName += ".june";
	}

	if (!Func->NativeName.empty()) {
		LLFuncName = Func->NativeName.str();
	}

	// TODO: Linkage
	llvm::Function* LLFunc = llvm::Function::Create(
		LLFuncType,
		llvm::Function::ExternalLinkage, // publically visible
		LLFuncName,
		LLModule
	);

	if (Func->Mods & mods::NATIVE) {
#ifdef _WIN32
		LLFunc->setDLLStorageClass(llvm::GlobalValue::DLLImportStorageClass);
		LLFunc->setCallingConv(llvm::CallingConv::X86_StdCall);
#endif
	}

	Func->LLAddress = LLFunc;
}

void june::IRGen::GenGenericFuncDecl(GenericFuncDecl* Func, u32 BindingId) {
	llvm::Function* LLFunc = std::get<1>(Func->BindingCache[BindingId]);
	if (!LLFunc) {
		BindTypes(Func, BindingId);
		GenFuncDecl(Func);
		UnbindTypes(Func);
		std::get<1>(Func->BindingCache[BindingId]) = Func->LLAddress;
		Func->LLAddress = nullptr;
	}
}

void june::IRGen::GenFuncBody(FuncDecl* Func) {
	if (Func->Mods & mods::NATIVE) return;

	LLFunc = Func->LLAddress;
	
	bool RVO = FuncNeedsRVO(Func);
	bool HasVoidRetTy = Func->RetTy->GetKind() == TypeKind::VOID && !Func->IsMainFunc || RVO;

	// Entry block for the function.
	llvm::BasicBlock* LLEntryBlock = llvm::BasicBlock::Create(LLContext, "entry.block", LLFunc);
	Builder.SetInsertPoint(LLEntryBlock);

	if (EmitDebugInfo) {
		GetDIEmitter(Func)->EmitFunc(Func, Builder);
	}

	if (Func->NumReturns > 1) {
		LLFuncEndBB = llvm::BasicBlock::Create(LLContext, "func.end", LLFunc);
		if (!HasVoidRetTy) {
			if (Func->IsMainFunc) {
				LLRetAddr = CreateAlloca(Context.I32Type, "retaddr");
			} else {
				LLRetAddr = CreateAlloca(Func->RetTy, "retaddr");
			}
		}
	}
	
	// Allocating space for the variables
	for (VarDecl* Var : Func->AllocVars) {	
		if (!(Var->Mods & mods::Mods::COMPTIME)) {
			GenAlloca(Var);
		}
	}

	// Storing the incoming variables
	u32 LLParamIndex = 0;
	if (Func->Record) {
		// Member function pointer
		llvm::Value* LLThisAddr = Builder.CreateAlloca(llvm::PointerType::get(GenRecordType(Context, Func->Record), 0));
		Builder.CreateStore(LLFunc->getArg(LLParamIndex++), LLThisAddr);
		LLThis = CreateLoad(LLThisAddr, "this");
	}

	if (RVO) {
		++LLParamIndex;
	}
	
	for (VarDecl* Param : Func->Params) {
		if (EmitDebugInfo)
			GetDIEmitter(Func)->EmitParam(Func, Param, Builder);
		Builder.CreateStore(LLFunc->getArg(LLParamIndex++), Param->LLAddress);
	}

	// If it is a constructor the fields need to be initialized early
	if (Func->Record && Func->Name == Func->Record->Name) {
		if (Func->Record->FieldsHaveAssignment) {
			GenDefaultRecordInitCall(Func->Record, LLThis);
		} else {
			llvm::Type* LLRecType = GenRecordType(Context, Func->Record);
			Builder.CreateStore(llvm::ConstantAggregateZero::get(LLRecType), LLThis);
		}
	}

	if (Func->IsMainFunc) {
		Context.JuneInitGlobalsFunc = GenGlobalInitFuncDecl();
		Builder.CreateCall(Context.JuneInitGlobalsFunc);
		if (!Context.CompileAsStandAlone) {
			FuncDecl* SysInitFunc = Context.SysFU->GlobalFuncs.find(Identifier("initialize"))->second[0];
			GenFuncDecl(SysInitFunc);
			Builder.CreateCall(SysInitFunc->LLAddress);
		}
	}

	ScopeStmts& Stmts = Func->Scope.Stmts;
 	for (AstNode* Node : Stmts) {
		GenNode(Node);
	}

	if (Func->NumReturns > 1) {
		GenBranchIfNotTerm(LLFuncEndBB);
		Builder.SetInsertPoint(LLFuncEndBB);
	}

	llvm::Instruction* LLRet = nullptr;
	if (Func->NumReturns > 1) {
		if (HasVoidRetTy) {
			LLRet = Builder.CreateRetVoid();
		} else {
			if (Func->IsMainFunc &&
				(Stmts.empty() || Stmts.back()->isNot(AstKind::RETURN))) {
				// Since main can be declared void it is possible it does not
				// have a return so storage is nessessary.
				llvm::Instruction* LLRetStore = Builder.CreateStore(GetLLInt32(0, LLContext), LLRetAddr);
				if (EmitDebugInfo)
					GetDIEmitter(Func)->EmitDebugLocation(LLRetStore, Func->Scope.EndLoc);
			}
			LLRet = Builder.CreateRet(CreateLoad(LLRetAddr));
		}
	} else if (Func->NumReturns == 0) {
		if (HasVoidRetTy) {
			LLRet = Builder.CreateRetVoid();
		} else if (Func->IsMainFunc &&
				  (Stmts.empty() || Stmts.back()->isNot(AstKind::RETURN))) {
			LLRet = Builder.CreateRet(GetLLInt32(0, LLContext));
		}
	}

	if (EmitDebugInfo) {
		if (LLRet)
			GetDIEmitter(Func)->EmitDebugLocation(LLRet, Func->Scope.EndLoc);
		GetDIEmitter(Func)->EmitFuncEnd(Func);
	}
}

void june::IRGen::GenGlobalVarDecl(VarDecl* Global) {
	if (Global->LLAddress) return; // Do not generate it twice

	std::string Name;
	if (Global->Mods & mods::Mods::NATIVE) {
		if (Global->NativeName.empty())
			Name = std::string(Global->Name.Text);
		else
			Name = std::string(Global->NativeName);
	} else {
		// TODO: Hand over to mangler
		Name = "g_" + Global->Name.Text.str();
		Name += "." + std::to_string(Context.NumGeneratedGlobalVars++);
	}

	llvm::GlobalVariable* LLGVar = MakeGlobalVar(Name, GenType(Global->Ty));
	Global->LLAddress = LLGVar;

	if (Global->Mods & mods::Mods::NATIVE) {
#ifdef _WIN32
		LLGVar->setDLLStorageClass(llvm::GlobalValue::DLLImportStorageClass);
#endif
	}

	if (EmitDebugInfo)
		GetDIEmitter(Global)->EmitGlobalVar(Global, Builder);
}

llvm::Value* june::IRGen::GenLocalVarDecl(VarDecl* Var) {
	if (Var->Mods & mods::Mods::COMPTIME) {
		// Computed on request. TODO: Might want to still generate here in case of variables being declared as part of expressions
		return nullptr;
	} else {
		assert(Var->LLAddress && "The address should have been generated at the start of the function!");
		if (EmitDebugInfo)
			GetDIEmitter(Var)->EmitLocalVar(Var, Builder);
		return GenVarDecl(GetAddressOfVar(Var), Var);
	}
}

llvm::Value* june::IRGen::GenVarDecl(llvm::Value* LLAddr, VarDecl* Var) {
	if (Var->Assignment) {
		GenAssignment(LLAddr, Var->Assignment);
	} else {
		GenDefaultValue(Var->Ty, LLAddr);
	}
	return LLAddr;
}

llvm::Value* june::IRGen::GenAlloca(VarDecl* Var) {
	
	llvm::Type* LLTy = GenType(Var->Ty);

	if (Var->ParamIdx != -1 && Var->Ty->GetKind() == TypeKind::FIXED_ARRAY)
		LLTy = llvm::PointerType::get(LLTy, 0);
	
	llvm::Value* LLAlloca = Builder.CreateAlloca(LLTy);
	Var->LLAddress = LLAlloca;
	if (DisplayLLVMIR) {
		// TODO: Hand over to mangler
		LLAlloca->setName(Var->Name.Text);
	}
	return LLAlloca;
}

llvm::Value* june::IRGen::GenNode(AstNode* Node) {
	switch (Node->Kind) {
	case AstKind::VAR_DECL:
		return GenLocalVarDecl(ocast<VarDecl*>(Node));
	case AstKind::INNER_SCOPE:
	case AstKind::ELSE_SCOPE:
		return GenInnerScope(ocast<InnerScopeStmt*>(Node));
	case AstKind::RETURN:
		return GenReturn(ocast<ReturnStmt*>(Node));
	case AstKind::RANGE_LOOP:
		return GenRangeLoop(ocast<RangeLoopStmt*>(Node));
	case AstKind::ITERATOR_LOOP:
		return GenIteratorLoop(ocast<IteratorLoopStmt*>(Node));
	case AstKind::PREDICATE_LOOP:
		return GenPredicateLoop(ocast<PredicateLoopStmt*>(Node));
	case AstKind::IF:
		return GenIf(ocast<IfStmt*>(Node));
	case AstKind::CONTINUE:
	case AstKind::BREAK:
		return GenLoopControl(ocast<LoopControlStmt*>(Node));
	case AstKind::IDENT_REF:
		return GenIdentRef(ocast<IdentRef*>(Node));
	case AstKind::FIELD_ACCESSOR:
		return GenFieldAccessor(ocast<FieldAccessor*>(Node));
	case AstKind::FUNC_CALL:
		return GenFuncCall(nullptr, ocast<FuncCall*>(Node));
	case AstKind::BINARY_OP:
		return GenBinaryOp(ocast<BinaryOp*>(Node));
	case AstKind::UNARY_OP:
		return GenUnaryOp(ocast<UnaryOp*>(Node));
	case AstKind::NUMBER_LITERAL:
		return GenNumberLiteral(ocast<NumberLiteral*>(Node));
	case AstKind::NULLPTR:
		return llvm::Constant::getNullValue(GenType(ocast<Null*>(Node)->CastTy));
	case AstKind::ARRAY:
		return GenArray(ocast<Array*>(Node), nullptr);
	case AstKind::ARRAY_ACCESS:
		return GenArrayAccess(ocast<ArrayAccess*>(Node));
	case AstKind::BOOL_LITERAL: {
		BoolLiteral* B = ocast<BoolLiteral*>(Node);
		if (B->tof) return llvm::ConstantInt::getTrue(LLContext);
		else        return llvm::ConstantInt::getFalse(LLContext);
	}
	case AstKind::SIZEOF_TYPE:
		return GetLLUInt32(
			SizeOfTypeInBytes(GenType(ocast<SizeofType*>(Node)->TyToGetSizeof)), LLContext);
	case AstKind::TYPE_CAST:
		return GenTypeCast(ocast<TypeCast*>(Node));
	case AstKind::HEAP_ALLOC_TYPE:
		return GenHeapAllocType(ocast<HeapAllocType*>(Node));
	case AstKind::THIS_REF:
		return LLThis;
	case AstKind::TERNARY_COND:
		return GenTernaryCond(ocast<TernaryCond*>(Node));
	case AstKind::TUPLE:
		return GenTuple(ocast<Tuple*>(Node), nullptr);
	default:
		assert(!"Unimplemented generation case!");
		return nullptr;
	}
}

void june::IRGen::GenGlobalInitFunc() {
	llvm::BasicBlock* LLEntryBlock = llvm::BasicBlock::Create(LLContext, "entry.block", Context.JuneInitGlobalsFunc);

	LLFunc = Context.JuneInitGlobalsFunc;
	Builder.SetInsertPoint(LLEntryBlock);

	GenGlobalPostponedAssignments();

	Builder.CreateRetVoid();

	if (DisplayLLVMIR) {
		Context.JuneInitGlobalsFunc->print(llvm::outs());
		llvm::outs() << '\n';
	}
}

llvm::Function* june::IRGen::GenGlobalInitFuncDecl() {
	llvm::FunctionType* LLFuncType =
		llvm::FunctionType::get(llvm::Type::getVoidTy(LLContext), false);
	llvm::Function* LLInitFunc =
		llvm::Function::Create(
			LLFuncType,
			llvm::Function::ExternalLinkage,
			"__june.init.globals",
			LLModule
		);
	return LLInitFunc;
}

void june::IRGen::GenGlobalPostponedAssignments() {
	// Iterator since it is modifiable during generation
	auto it = Context.GlobalPostponedAssignments.begin();
	while (it != Context.GlobalPostponedAssignments.end()) {
		VarDecl* Var = *it;
		if (Var->Assignment) {
			GenAssignment(Var->LLAddress, Var->Assignment);
		} else {
			if (Var->Ty->GetKind() == TypeKind::FIXED_ARRAY) {
				FixedArrayType* ArrTy = Var->Ty->AsFixedArrayType();
				if (ArrTy->GetBaseType()->GetKind() == TypeKind::RECORD) {
					llvm::Value* LLArrStartPtr = GetArrayAsPtrGeneral(Var->LLAddress, ArrTy->GetNestingLevel() + 1);
					llvm::Value* LLTotalLinearLength = GetLLUInt32(ArrTy->GetTotalLinearLength(), LLContext);
					GenRecordArrayObjsInitCalls(ArrTy, LLArrStartPtr, LLTotalLinearLength);
				}
			} else if (Var->Ty->GetKind() == TypeKind::RECORD) {
				GenDefaultValue(Var->Ty, Var->LLAddress);
			}
		}
		++it;
	}
}

llvm::Value* june::IRGen::GenRValue(AstNode* Node) {

	// Dereferencing any LValues
	llvm::Value* LLValue = GenNode(Node);
	switch (Node->Kind) {
	case AstKind::IDENT_REF:
	case AstKind::FIELD_ACCESSOR:
	case AstKind::ARRAY_ACCESS: {

		if (Node->Kind == AstKind::FIELD_ACCESSOR) {
			if (ocast<FieldAccessor*>(Node)->IsArrayLength) {
				break; // Do not load array lengths.
			}
		}

		if (ocast<Expr*>(Node)->IsComptimeCompat) {
			break; // Don't load compile time variables
		}

		// Want to make sure not to load an array
		// since arrays should always be taken as
		// l-values.
		if (ocast<Expr*>(Node)->Ty->GetKind() != TypeKind::FIXED_ARRAY) {
			LLValue = CreateLoad(LLValue);
		}
		break;
	}
	case AstKind::FUNC_CALL: {
		FuncCall* Call = ocast<FuncCall*>(Node);
		if (Call->IsConstructorCall ||
			(Call->CalledFunc && FuncNeedsRVO(Call->CalledFunc))) {
			LLValue = CreateLoad(LLValue);
		}
		break;
	}
	case AstKind::UNARY_OP:
		if (ocast<UnaryOp*>(Node)->Op == '*') {
			// Dereference operators load the original
			// l-value once, but if an r-value is requested
			// it must be loaded twice.
			LLValue = CreateLoad(LLValue);
		}
		break;
	default:
		break;
	}

	// TODO: Might not always be able to cast to Expr
	Expr* E = ocast<Expr*>(Node);
	if (E->CastTy) {
		LLValue = GenCast(E->CastTy, E->Ty, LLValue);
	}

	return LLValue;
}

llvm::Value* june::IRGen::GenInnerScope(InnerScopeStmt* InnerScope) {
	if (EmitDebugInfo)
		GetDIEmitter()->EmitScopeStart(CFunc->FU, InnerScope->Scope.StartLoc);
	GenBlock(nullptr, InnerScope->Scope);
	if (EmitDebugInfo)
		GetDIEmitter()->EmitScopeEnd();
	return nullptr;
}

llvm::Value* june::IRGen::GenReturn(ReturnStmt* Ret) {
	bool RVO = FuncNeedsRVO(CFunc);

	if (CFunc->NumReturns == 1) {
		if (Ret->Val && !RVO) {
			Builder.CreateRet(GenRValue(Ret->Val));
		} else if (CFunc->IsMainFunc) {
			Builder.CreateRet(GetLLInt32(0, LLContext));
		} else if (RVO) {
			GenStoreRVOStructRes(Ret->Val);
			Builder.CreateRetVoid();
		} else {
			Builder.CreateRetVoid();
		}
		EmitDebugLocation(Ret);
		return nullptr;
	}

	if (Ret->Val && !RVO) {
		Builder.CreateStore(GenRValue(Ret->Val), LLRetAddr);
	} else if (CFunc->IsMainFunc) {
		Builder.CreateStore(GetLLInt32(0, LLContext), LLRetAddr);
	} else if (RVO) {
		GenStoreRVOStructRes(Ret->Val);
	}
	EmitDebugLocation(Ret); // storage
	Builder.CreateBr(LLFuncEndBB);
	EmitDebugLocation(Ret);
	return nullptr;
}

llvm::Value* june::IRGen::GenRangeLoop(RangeLoopStmt* Loop) {

	llvm::BasicBlock* LLEndBB  = llvm::BasicBlock::Create(LLContext, "loop.end", LLFunc);
	llvm::BasicBlock* LLBodyBB = llvm::BasicBlock::Create(LLContext, "loop.body", LLFunc);
	llvm::BasicBlock* LLIncBB  = Loop->Inc ? llvm::BasicBlock::Create(LLContext, "loop.inc", LLFunc)
		                                   : nullptr;	
	llvm::BasicBlock* LLCondBB     = llvm::BasicBlock::Create(LLContext, "loop.cond", LLFunc);
	llvm::BasicBlock* LLContinueBB = LLIncBB ? LLIncBB : LLCondBB;

	LoopBreakStack.push_back(LLEndBB);
	LoopContinueStack.push_back(LLContinueBB);

	if (Loop->Decl) {
		GenNode(Loop->Decl);
	}

	// Generating the condition block
	GenLoopCondJump(LLCondBB, LLBodyBB, LLEndBB, Loop->Cond);
	EmitDebugLocation(Loop);

	// Generating the body of the loop
	if (EmitDebugInfo)
		GetDIEmitter()->EmitScopeStart(CFunc->FU, Loop->Scope.StartLoc);

	GenBlock(LLBodyBB, Loop->Scope);
	LoopBreakStack.pop_back();
	LoopContinueStack.pop_back();

	// Unconditionally branch back to the condition or inc. block
	// to restart the loop.
	GenBranchIfNotTerm(LLContinueBB, &Loop->Scope);
	
	// Creating the code for the inc. block if needed
	if (LLIncBB) {
		
		Builder.SetInsertPoint(LLIncBB);
		
		GenNode(Loop->Inc);

		// Jumping directly into the loop condition
		Builder.CreateBr(LLCondBB); // No need to check for terminal since expressions cannot jump.
		EmitDebugLocation(Loop->Inc);
	}

	// Finally continuing forward into a new block after the loop
	GenSetInsertBlock(LLEndBB, &Loop->Scope);

	if (EmitDebugInfo)
		GetDIEmitter()->EmitScopeEnd();

	return nullptr;
}

llvm::Value* june::IRGen::GenIteratorLoop(IteratorLoopStmt* Loop) {

	llvm::BasicBlock* LLEndBB  = llvm::BasicBlock::Create(LLContext, "loop.end", LLFunc);
	llvm::BasicBlock* LLBodyBB = llvm::BasicBlock::Create(LLContext, "loop.body", LLFunc);
	llvm::BasicBlock* LLIncBB  = llvm::BasicBlock::Create(LLContext, "loop.inc", LLFunc);
	llvm::BasicBlock* LLCondBB = llvm::BasicBlock::Create(LLContext, "loop.cond", LLFunc);
	llvm::BasicBlock* LLContinueBB = LLIncBB;

	LoopBreakStack.push_back(LLEndBB);
	LoopContinueStack.push_back(LLContinueBB);

	FixedArrayType* ArrTy = Loop->IterOnExpr->Ty->AsFixedArrayType();

	llvm::Value* LLArrItrPtrAddr = CreateTempAlloca(
		llvm::PointerType::get(GenType(ArrTy->ElmTy), 0));
	
	llvm::Value* LLPtrToArrStart = GetArrayAsPtr1Nesting(GenNode(Loop->IterOnExpr));
	llvm::Value* LLPtrToArrEnd   = CreateInBoundsGEP(LLPtrToArrStart, { GetLLUInt64(ArrTy->Length, LLContext) });;
	Builder.CreateStore(LLPtrToArrStart, LLArrItrPtrAddr);

	// Jumping directly into the loop condition
	Builder.CreateBr(LLCondBB);
	Builder.SetInsertPoint(LLCondBB);

	// Keep going until end of array
	llvm::Value* LLCond = Builder.CreateICmpNE(CreateLoad(LLArrItrPtrAddr), LLPtrToArrEnd);
	Builder.CreateCondBr(LLCond, LLBodyBB, LLEndBB);
	EmitDebugLocation(Loop);

	// Generating the body of the loop
	if (EmitDebugInfo)
		GetDIEmitter()->EmitScopeStart(CFunc->FU, Loop->Scope.StartLoc);

	GenBranchIfNotTerm(LLBodyBB);
	Builder.SetInsertPoint(LLBodyBB);

	// Creating the variable that is being looped on
	Loop->VarVal->LLAddress = CreateTempAlloca(GenType(ArrTy->ElmTy));
	Builder.CreateStore(CreateLoad(CreateLoad(LLArrItrPtrAddr)), Loop->VarVal->LLAddress);

	GenBlock(nullptr, Loop->Scope);
	
	LoopBreakStack.pop_back();
	LoopContinueStack.pop_back();

	// Jump back to the continue block to restart the loop
	GenBranchIfNotTerm(LLContinueBB, &Loop->Scope);

	// Incrementing the array pointer
	Builder.SetInsertPoint(LLIncBB);

	llvm::Value* LLArrItrPtr = CreateLoad(LLArrItrPtrAddr);
	llvm::Value* LLNextPtr = CreateInBoundsGEP(LLArrItrPtr, { GetLLUInt32(1, LLContext) });
	Builder.CreateStore(LLNextPtr, LLArrItrPtrAddr);

	// Jumping directly into the loop condition
	Builder.CreateBr(LLCondBB);

	// Finally continuing forward into a new block after the loop
	GenSetInsertBlock(LLEndBB, &Loop->Scope);

	if (EmitDebugInfo)
		GetDIEmitter()->EmitScopeEnd();

	return nullptr;
}

llvm::Value* june::IRGen::GenPredicateLoop(PredicateLoopStmt* Loop) {
	llvm::BasicBlock* LLEndBB  = llvm::BasicBlock::Create(LLContext, "loop.end", LLFunc);
	llvm::BasicBlock* LLBodyBB = llvm::BasicBlock::Create(LLContext, "loop.body", LLFunc);
	llvm::BasicBlock* LLCondBB = llvm::BasicBlock::Create(LLContext, "loop.cond", LLFunc);

	LoopBreakStack.push_back(LLEndBB);
	LoopContinueStack.push_back(LLCondBB);

	// Generating the condition block
	GenLoopCondJump(LLCondBB, LLBodyBB, LLEndBB, Loop->Cond);
	EmitDebugLocation(Loop);

	// Generating the body of the loop
	if (EmitDebugInfo)
		GetDIEmitter()->EmitScopeStart(CFunc->FU, Loop->Scope.StartLoc);

	GenBlock(LLBodyBB, Loop->Scope);
	LoopBreakStack.pop_back();
	LoopContinueStack.pop_back();

	// Unconditionally branch back to the condition block
	GenBranchIfNotTerm(LLCondBB, &Loop->Scope);

	// Finally continuing forward into a new block after the loop
	GenSetInsertBlock(LLEndBB, &Loop->Scope);

	if (EmitDebugInfo)
		GetDIEmitter()->EmitScopeEnd();

	return nullptr;
}

void june::IRGen::GenLoopCondJump(llvm::BasicBlock* LLCondBB, llvm::BasicBlock* LLBodyBB, llvm::BasicBlock* LLEndBB, Expr* Cond) {
	// Jumping directly into the loop condition
	Builder.CreateBr(LLCondBB);
	Builder.SetInsertPoint(LLCondBB);

	llvm::Value* LLCond;
	if (Cond) {
		LLCond = GenCond(Cond);
	} else {
		// Defaults to a true condition
		LLCond = llvm::ConstantInt::getTrue(LLContext);
	}
	Builder.CreateCondBr(LLCond, LLBodyBB, LLEndBB);
}

llvm::Value* june::IRGen::GenIf(IfStmt* If) {
	
	llvm::BasicBlock* LLThenBB = llvm::BasicBlock::Create(LLContext, "if.then", LLFunc);
	llvm::BasicBlock* LLEndBB  = llvm::BasicBlock::Create(LLContext, "if.end", LLFunc);
	llvm::BasicBlock* LLElseBB = LLEndBB;
	if (If->Else) {
		LLElseBB = llvm::BasicBlock::Create(LLContext, "if.else", LLFunc);
	}

	GenBranchOnCond(If->Cond, LLThenBB, LLElseBB);
	EmitDebugLocation(If);

	if (EmitDebugInfo)
		GetDIEmitter()->EmitScopeStart(CFunc->FU, If->Scope.StartLoc);
	GenBlock(LLThenBB, If->Scope);
	GenBranchIfNotTerm(LLEndBB, &If->Scope);
	if (EmitDebugInfo)
		GetDIEmitter()->EmitScopeEnd();

	// Generating the else statement if it exist
	if (AstNode* Else = If->Else) {
		Builder.SetInsertPoint(LLElseBB);
		GenNode(Else);
		if (Else->is(AstKind::INNER_SCOPE)) {
			GenSetInsertBlock(LLEndBB, &ocast<InnerScopeStmt*>(Else)->Scope);
		} else {
			GenSetInsertBlock(LLEndBB, &ocast<IfStmt*>(Else)->Scope);
		}
	} else {
		// Finally continuing forward into a new block after the if
		GenSetInsertBlock(LLEndBB, &If->Scope);
	}

	return nullptr;
}

llvm::Value* june::IRGen::GenLoopControl(LoopControlStmt* LoopControl) {
	if (LoopControl->Kind == AstKind::BREAK) {
		llvm::BasicBlock* LoopExit = LoopBreakStack[LoopControl->LoopCount - 1];
		Builder.CreateBr(LoopExit);
	} else {
		llvm::BasicBlock* LoopRestart = LoopContinueStack[LoopControl->LoopCount - 1];
		Builder.CreateBr(LoopRestart);
	}
	EmitDebugLocation(LoopControl);
	return nullptr;
}

llvm::Value* june::IRGen::GenIdentRef(IdentRef* IRef) {
	if (IRef->VarRef->Mods & mods::Mods::COMPTIME) {
		VarDecl* Var = IRef->VarRef;
		if (!Var->LLComptimeVal) {
			if (!Var->Assignment->IsFoldable) {
				// TODO: If the expression is not foldable then
				// it should be evaluted in an anoyomous function
				assert(!"Not handled yet");
			} else {
				Var->LLComptimeVal = llvm::cast<llvm::Constant>(GenNode(Var->Assignment));
			}
		}
		return Var->LLComptimeVal;
	}

	return GetAddressOfVar(IRef->VarRef);
}

llvm::Value* june::IRGen::GenFieldAccessor(FieldAccessor* FA) {
	if (FA->IsArrayLength) {
		return GetLLUInt32(FA->Site->Ty->AsFixedArrayType()->Length, LLContext);
	}
	
	if (FA->Site->is(AstKind::IDENT_REF) &&
		ocast<IdentRef*>(FA->Site)->RefKind == IdentRef::FILE_UNIT
		) {
		return GenIdentRef(FA);
	}

 	Expr* Site = FA->Site;
	if (Site->Kind == AstKind::FUNC_CALL    ||
		Site->Kind == AstKind::ARRAY_ACCESS ||
		Site->Kind == AstKind::THIS_REF     ||
		((Site->Kind == AstKind::IDENT_REF ||
			Site->Kind == AstKind::FIELD_ACCESSOR
			) && ocast<IdentRef*>(Site)->RefKind == IdentRef::VAR)
		) {
		
		llvm::Value* LLSite = GenNode(FA->Site);

		// Ex.  'a().b'  or  'a().j()'  ect..
		if (FA->Site->is(AstKind::FUNC_CALL)) {
			FuncCall* Call = ocast<FuncCall*>(FA->Site);
			if (!Call->IsConstructorCall &&
				!(Call->CalledFunc && FuncNeedsRVO(Call->CalledFunc)) &&
				FA->Site->Ty->GetKind() == TypeKind::RECORD
				) {
				llvm::Value* LLTempStorage = CreateTempAlloca(LLSite->getType());
				Builder.CreateStore(LLSite, LLTempStorage);
				LLSite = LLTempStorage;
			}
		}

		if (Site->Ty->GetKind() == TypeKind::POINTER &&
			Site->isNot(AstKind::THIS_REF)) {
			// Auto-dereferencing
			LLSite = CreateLoad(LLSite, "deref");
		}

		if (FA->RefKind == IdentRef::FUNCS) {
			// a.b()
			return LLSite;
		} else {
			// a.b
			return CreateStructGEP(LLSite, FA->VarRef->FieldIdx);
		}
	}

	// TODO!!
	return nullptr;
}

llvm::Value* june::IRGen::GenFuncCall(llvm::Value* LLAddr, FuncCall* Call) {

	if (Call->CalledFunc) {
		if (Call->CalledFunc->is(AstKind::GENERIC_FUNC_DECL)) {
			GenGenericFuncDecl(ocast<GenericFuncDecl*>(Call->CalledFunc), Call->TypeBindingId);
		} else {
			GenFuncDecl(Call->CalledFunc);
		}
	}
 	
	if (Call->CalledFunc && Call->CalledFunc->LLVMIntrinsicID) {
		return GenLLVMIntrinsicCall(Call);
	}

	if (Call->IsConstructorCall && !LLAddr) {
		// Need to create a temporary object
		LLAddr = CreateTempAlloca(GenType(Call->Ty));
	}

	if (Call->IsConstructorCall && !Call->CalledFunc) {

		// Generating a default constructor "call"!
		llvm::Value* LLThisBackup = LLThis;
		LLThis = LLAddr;

		std::unordered_set<u32> FieldIndexesWithVals;
		for (u32 i = 0; i < Call->Args.size(); i++) {
			FieldIndexesWithVals.insert(i);
			llvm::Value* LLFieldAddr = CreateStructGEP(LLAddr, i);
			GenAssignment(LLFieldAddr, Call->Args[i]);
		}

		for (FuncCall::NamedArg& NamedArg : Call->NamedArgs) {
			FieldIndexesWithVals.insert(NamedArg.VarRef->FieldIdx);
			llvm::Value* LLFieldAddr = CreateStructGEP(LLAddr, NamedArg.VarRef->FieldIdx);
			GenAssignment(LLFieldAddr, NamedArg.AssignValue);
		}
		RecordDecl* Record = Call->Ty->AsRecordType()->Record;
		for (VarDecl* Field : Record->FieldsByIdxOrder) {
			if (FieldIndexesWithVals.find(Field->FieldIdx) == FieldIndexesWithVals.end()) {
				llvm::Value* LLFieldAddr = CreateStructGEP(LLAddr, Field->FieldIdx);
				GenVarDecl(LLFieldAddr, Field);
			}
		}

		LLThis = LLThisBackup;
		return LLAddr;
	}

	// Adding arguments
	u32 ArgIndex = 0;
	llvm::SmallVector<llvm::Value*, 2> LLArgs;
	bool RVO = false;
	u32 NumArgs = Call->Args.size() + Call->NamedArgs.size();
	if (Call->CalledFunc) {
		RVO = FuncNeedsRVO(Call->CalledFunc);
		if (Call->CalledFunc->Record) {
			++NumArgs;
		}
		if (RVO) {
			++NumArgs;
		}
	}
	
	LLArgs.resize(NumArgs);

	if (Call->CalledFunc && Call->CalledFunc->Record) {
		
		if (Call->IsConstructorCall) {  // Record(...)
			LLArgs[ArgIndex++] = LLAddr;
		}
		// Calling a member function so need to pass in the
		// record pointer.
		else if (Call->Site->is(AstKind::IDENT_REF)) {
			// It is in the form: b(); so the only
			// valid explaination is it is a call
			// to another member function inside
			// the same record.
			LLArgs[ArgIndex++] = LLThis;
		} else {
			LLArgs[ArgIndex++] = GenNode(Call->Site);
		}
	}

	// The function being takes a reference to the returning
	// struct as an argument rather than returning the struct
	if (RVO) {
		if (!LLAddr) {
			// For whatever reason the user is ignoring the return
			// value of the structure so need to create it for them.
			LLAddr = CreateTempAlloca(GenType(Call->CalledFunc->RetTy));
		}

		LLArgs[ArgIndex++] = LLAddr;
	}

	for (u32 i = 0; i < Call->Args.size(); i++) {
		Expr* Arg = Call->Args[i];
		LLArgs[ArgIndex++] = GenRValue(Arg);
	}
	for (FuncCall::NamedArg& NamedArg : Call->NamedArgs) {
		LLArgs[NamedArg.VarRef->ParamIdx] = GenRValue(NamedArg.AssignValue);
	}

	llvm::Value* CallValue = nullptr;
	if (Call->CalledFunc) {
		llvm::Function* LLCalledFunc = Call->CalledFunc->LLAddress;
		if (Call->CalledFunc->is(AstKind::GENERIC_FUNC_DECL)) {
			GenericFuncDecl* GenFunc = ocast<GenericFuncDecl*>(Call->CalledFunc);
			LLCalledFunc = std::get<1>(GenFunc->BindingCache[Call->TypeBindingId]);
		}

		// -- DEBUG
		//llvm::outs() << "Calling Function with name: " << Call->CalledFunc->Name << '\n';
		//llvm::outs() << "Types passed to function:\n";
		//for (u32 i = 0; i < LLArgs.size(); i++) {
		//	llvm::outs() << LLValTypePrinter(LLArgs[i]) << '\n';
		//}
		//llvm::outs() << "Types expected by function:\n";
		//for (u32 i = 0; i < LLCalledFunc->arg_size(); i++) {
		//	llvm::outs() << LLValTypePrinter(LLCalledFunc->getArg(i)) << '\n';
		//}
		//llvm::outs() << '\n';
		
		CallValue = Builder.CreateCall(LLCalledFunc, LLArgs);
	} else {
		// Call must be on a variable
		llvm::Value* CallSite = CreateLoad(GenNode(Call->Site));
		CallValue =
			Builder.CreateCall(
			     llvm::cast<llvm::FunctionType>(CallSite->getType()->getPointerElementType()),
			     CallSite,
			     LLArgs);
	}

	EmitDebugLocation(Call);
	if (!Call->IsConstructorCall && !RVO) {
		return CallValue;
	} else {
		return LLAddr; // Returning the newly generated object
	}
}

llvm::Value* june::IRGen::GenBinaryOp(BinaryOp* BinOp) {
	switch (BinOp->Op) {
	case '=': {
		return GenAssignment(GenNode(BinOp->LHS), BinOp->RHS);
	}
	//
	// Arithmetic
	//
	case '+': {
		llvm::Value* LLLHS = GenRValue(BinOp->LHS);
		llvm::Value* LLRHS = GenRValue(BinOp->RHS);

		if (BinOp->Ty->GetKind() == TypeKind::POINTER) {
			llvm::Value* PtrAddr = BinOp->LHS->Ty->GetKind() == TypeKind::POINTER ? LLLHS : LLRHS;
			llvm::Value* Add     = BinOp->LHS->Ty->GetKind() == TypeKind::POINTER ? LLRHS : LLLHS;

			llvm::SmallVector<llvm::Value*, 1> GEPAdd = { Add };
			return CreateInBoundsGEP(PtrAddr, GEPAdd);
		} else {
			if (BinOp->Ty->isInt()) {
				return Builder.CreateAdd(LLLHS, LLRHS);
			}
			return Builder.CreateFAdd(LLLHS, LLRHS);
		}
	}
	case '-': {
		llvm::Value* LLLHS = GenRValue(BinOp->LHS);
		llvm::Value* LLRHS = GenRValue(BinOp->RHS);

		if (BinOp->Ty->GetKind() == TypeKind::POINTER) {
			// Pointer arithmetic.

			llvm::Value* PtrAddr = LLLHS;
			llvm::Value* Sub = Builder.CreateNeg(LLRHS);

			llvm::SmallVector<llvm::Value*, 1> GEPAdd = { Sub };
			return CreateInBoundsGEP(PtrAddr, GEPAdd);
		} else {
			if (BinOp->Ty->isInt()) {
				return Builder.CreateSub(LLLHS, LLRHS);
			}
			return Builder.CreateFSub(LLLHS, LLRHS);
		}
	}
	case '*': {
		llvm::Value* LLLHS = GenRValue(BinOp->LHS);
		llvm::Value* LLRHS = GenRValue(BinOp->RHS);
		if (BinOp->Ty->isInt()) {
			return Builder.CreateMul(LLLHS, LLRHS);
		}
		return Builder.CreateFMul(LLLHS, LLRHS);
	}
	case '/': {
		llvm::Value* LLLHS = GenRValue(BinOp->LHS);
		llvm::Value* LLRHS = GenRValue(BinOp->RHS);
		if (BinOp->Ty->isInt()) {
			if (BinOp->Ty->isSigned()) {
				return Builder.CreateSDiv(LLLHS, LLRHS);
			} else {
				return Builder.CreateUDiv(LLLHS, LLRHS);
			}
		}
		return Builder.CreateFDiv(LLLHS, LLRHS);
	}
	case '%': {
		llvm::Value* LLLHS = GenRValue(BinOp->LHS);
		llvm::Value* LLRHS = GenRValue(BinOp->RHS);
		if (BinOp->Ty->isSigned()) {
			return Builder.CreateSRem(LLLHS, LLRHS);
		}
		return Builder.CreateURem(LLLHS, LLRHS);
	}
	case TokenKind::PLUS_EQ: { // +=
		llvm::Value* LLLHS = GenNode(BinOp->LHS);
		llvm::Value* LLRHS = GenRValue(BinOp->RHS);

		if (BinOp->Ty->GetKind() == TypeKind::POINTER) {
			llvm::SmallVector<llvm::Value*, 1> LLIdx = { LLRHS };
			llvm::Value* V = CreateInBoundsGEP(CreateLoad(LLLHS), LLIdx);
			Builder.CreateStore(V, LLLHS);
			return V;
		} else {
			llvm::Value* LLLHSRV = CreateLoad(LLLHS);
			llvm::Value* V = BinOp->Ty->isInt() ? Builder.CreateAdd(LLLHSRV, LLRHS)
				                                : Builder.CreateFAdd(LLLHSRV, LLRHS);
			Builder.CreateStore(V, LLLHS);
			return V;
		}
	}
	case TokenKind::MINUS_EQ: { // -=
		llvm::Value* LLLHS = GenNode(BinOp->LHS);
		llvm::Value* LLRHS = GenRValue(BinOp->RHS);

		if (BinOp->Ty->GetKind() == TypeKind::POINTER) {
			llvm::SmallVector<llvm::Value*, 1> LLIdx = { Builder.CreateNeg(LLRHS) };
			llvm::Value* V = CreateInBoundsGEP(CreateLoad(LLLHS), LLIdx);
			Builder.CreateStore(V, LLLHS);
			return V;
		} else {
			llvm::Value* LLLHSRV = CreateLoad(LLLHS);
			llvm::Value* V = BinOp->Ty->isInt() ? Builder.CreateSub(LLLHSRV, LLRHS)
												: Builder.CreateFSub(LLLHSRV, LLRHS);
			Builder.CreateStore(V, LLLHS);
			return V;
		}
	}
	case TokenKind::STAR_EQ: { // *=
		llvm::Value* LLLHS = GenNode(BinOp->LHS);
		llvm::Value* LLRHS = GenRValue(BinOp->RHS);
		llvm::Value* LLLHSRV = CreateLoad(LLLHS);
		llvm::Value* V = BinOp->Ty->isInt() ? Builder.CreateMul(LLLHSRV, LLRHS)
			                                : Builder.CreateFMul(LLLHSRV, LLRHS);
		Builder.CreateStore(V, LLLHS);
		return V;
	}
	case TokenKind::SLASH_EQ: { // /=
		llvm::Value* LLLHS = GenNode(BinOp->LHS);
		llvm::Value* LLRHS = GenRValue(BinOp->RHS);
		llvm::Value* LLLHSRV = CreateLoad(LLLHS);
		llvm::Value* V;
		if (BinOp->Ty->isInt()) {
			V = BinOp->Ty->isSigned() ? Builder.CreateSDiv(LLLHSRV, LLRHS)
			                          : Builder.CreateUDiv(LLLHSRV, LLRHS);
		} else {
			V = Builder.CreateFDiv(LLLHSRV, LLRHS);
		}
		Builder.CreateStore(V, LLLHS);
		return V;
	}
	case TokenKind::MOD_EQ: { // %=
		llvm::Value* LLLHS = GenNode(BinOp->LHS);
		llvm::Value* LLRHS = GenRValue(BinOp->RHS);
		llvm::Value* LLLHSRV = CreateLoad(LLLHS);
		llvm::Value* V = BinOp->Ty->isSigned() ? Builder.CreateSRem(LLLHSRV, LLRHS)
			                                   : Builder.CreateURem(LLLHSRV, LLRHS);
		Builder.CreateStore(V, LLLHS);
		return V;
	}
	//
	// Bitwise
	//
	case '&': {
		llvm::Value* LLLHS = GenRValue(BinOp->LHS);
		llvm::Value* LLRHS = GenRValue(BinOp->RHS);
		return Builder.CreateAnd(LLLHS, LLRHS);
	}
	case '^': {
		llvm::Value* LLLHS = GenRValue(BinOp->LHS);
		llvm::Value* LLRHS = GenRValue(BinOp->RHS);
		return Builder.CreateXor(LLLHS, LLRHS);
	}
	case '|': {
		llvm::Value* LLLHS = GenRValue(BinOp->LHS);
		llvm::Value* LLRHS = GenRValue(BinOp->RHS);
		return Builder.CreateOr(LLLHS, LLRHS);
	}
	case TokenKind::LT_LT: { // <<
		llvm::Value* LLLHS = GenRValue(BinOp->LHS);
		llvm::Value* LLRHS = GenRValue(BinOp->RHS);
		return Builder.CreateShl(LLLHS, LLRHS);
	}
	case TokenKind::GT_GT: { // >>
		llvm::Value* LLLHS = GenRValue(BinOp->LHS);
		llvm::Value* LLRHS = GenRValue(BinOp->RHS);
		return Builder.CreateLShr(LLLHS, LLRHS);
	}
	case TokenKind::AMP_EQ: { // &=
		llvm::Value* LLLHS = GenNode(BinOp->LHS);
		llvm::Value* LLRHS = GenRValue(BinOp->RHS);
		llvm::Value* LLLHSRV = CreateLoad(LLLHS);
		llvm::Value* V = Builder.CreateAnd(LLLHSRV, LLRHS);
		Builder.CreateStore(V, LLLHS);
		return V;
	}
	case TokenKind::CRT_EQ: { // ^=
		llvm::Value* LLLHS = GenNode(BinOp->LHS);
		llvm::Value* LLRHS = GenRValue(BinOp->RHS);
		llvm::Value* LLLHSRV = CreateLoad(LLLHS);
		llvm::Value* V = Builder.CreateXor(LLLHSRV, LLRHS);
		Builder.CreateStore(V, LLLHS);
		return V;
	}
	case TokenKind::BAR_EQ: { // |=
		llvm::Value* LLLHS = GenNode(BinOp->LHS);
		llvm::Value* LLRHS = GenRValue(BinOp->RHS);
		llvm::Value* LLLHSRV = CreateLoad(LLLHS);
		llvm::Value* V = Builder.CreateOr(LLLHSRV, LLRHS);
		Builder.CreateStore(V, LLLHS);
		return V;
	}
	case TokenKind::LT_LT_EQ: { // <<=
		llvm::Value* LLLHS = GenNode(BinOp->LHS);
		llvm::Value* LLRHS = GenRValue(BinOp->RHS);
		llvm::Value* LLLHSRV = CreateLoad(LLLHS);
		llvm::Value* V = Builder.CreateShl(LLLHSRV, LLRHS);
		Builder.CreateStore(V, LLLHS);
		return V;
	}
	case TokenKind::GT_GT_EQ: { // >>=
		llvm::Value* LLLHS = GenNode(BinOp->LHS);
		llvm::Value* LLRHS = GenRValue(BinOp->RHS);
		llvm::Value* LLLHSRV = CreateLoad(LLLHS);
		llvm::Value* V = Builder.CreateLShr(LLLHSRV, LLRHS);
		Builder.CreateStore(V, LLLHS);
		return V;
	}
	//
	// Conditionals
	//
	case TokenKind::EQ_EQ: {
		llvm::Value* LLLHS = GenRValue(BinOp->LHS);
		llvm::Value* LLRHS = GenRValue(BinOp->RHS);
		if (BinOp->LHS->Ty->isFloat() || BinOp->RHS->Ty->isFloat())
			return Builder.CreateFCmpUEQ(LLLHS, LLRHS);
		return Builder.CreateICmpEQ(LLLHS, LLRHS);
	}
	case TokenKind::EXL_EQ: {
		llvm::Value* LLLHS = GenRValue(BinOp->LHS);
		llvm::Value* LLRHS = GenRValue(BinOp->RHS);
		if (BinOp->LHS->Ty->isFloat() || BinOp->RHS->Ty->isFloat())
			return Builder.CreateFCmpUNE(LLLHS, LLRHS);
		return Builder.CreateICmpNE(LLLHS, LLRHS);
	}
	case '<': {
		llvm::Value* LLLHS = GenRValue(BinOp->LHS);
		llvm::Value* LLRHS = GenRValue(BinOp->RHS);
	
		if (BinOp->LHS->Ty->isInt()) {
			if (BinOp->LHS->Ty->isSigned()) {
				return Builder.CreateICmpSLT(LLLHS, LLRHS);
			} else {
				return Builder.CreateICmpULT(LLLHS, LLRHS);
			}
		}
		return Builder.CreateFCmpULT(LLLHS, LLRHS);
	}
	case '>': {
		llvm::Value* LLLHS = GenRValue(BinOp->LHS);
		llvm::Value* LLRHS = GenRValue(BinOp->RHS);

		if (BinOp->LHS->Ty->isInt()) {
			if (BinOp->LHS->Ty->isSigned()) {
				return Builder.CreateICmpSGT(LLLHS, LLRHS);
			} else {
				return Builder.CreateICmpUGT(LLLHS, LLRHS);
			}
		}
		return Builder.CreateFCmpUGT(LLLHS, LLRHS);
	}
	case TokenKind::LT_EQ: {
		llvm::Value* LLLHS = GenRValue(BinOp->LHS);
		llvm::Value* LLRHS = GenRValue(BinOp->RHS);

		if (BinOp->LHS->Ty->isInt()) {
			if (BinOp->LHS->Ty->isSigned()) {
				return Builder.CreateICmpSLE(LLLHS, LLRHS);
			} else {
				return Builder.CreateICmpULE(LLLHS, LLRHS);
			}
		}
		return Builder.CreateFCmpULE(LLLHS, LLRHS);
	}
	case TokenKind::GT_EQ: {
		llvm::Value* LLLHS = GenRValue(BinOp->LHS);
		llvm::Value* LLRHS = GenRValue(BinOp->RHS);

		if (BinOp->LHS->Ty->isInt()) {
			if (BinOp->LHS->Ty->isSigned()) {
				return Builder.CreateICmpSGE(LLLHS, LLRHS);
			} else {
				return Builder.CreateICmpUGE(LLLHS, LLRHS);
			}
		}
		return Builder.CreateFCmpUGE(LLLHS, LLRHS);
	}
	case TokenKind::AMP_AMP: { // &&

		// See: https://github.com/llvm/llvm-project/blob/839ac62c5085d895d3165bc5024db623a7a78813/clang/lib/CodeGen/CGExprScalar.cpp
		// VisitBinLAnd

		// ... We gen the nodes lower on the tree first
		//     then after returning back up from the
		//     children node emission we calculate the very
		//     last conidition which gets fed to the PHI node.
		//
		//     It only reaches this last condition block if it
		//     suceeded all children LHS of '&&' operator.


		//   P1 && P2 && P3
		//
		//
		//           &&
		//          /  \
		//         &&   P3  <- Only evaluted in the end after children.
		//        /  \
		//       P1   P2

		llvm::BasicBlock* LLEndBB     = llvm::BasicBlock::Create(LLContext, "and.end", LLFunc);
		llvm::BasicBlock* LLLHSTrueBB = llvm::BasicBlock::Create(LLContext, "and.lhs.true", LLFunc);
		
		// Generate children
		GenBranchOnCond(BinOp->LHS, LLLHSTrueBB, LLEndBB);

		// All children blocks result in false if they
		// arrive from those blocks.
		llvm::PHINode* LLResPHINode = llvm::PHINode::Create(
			llvm::Type::getInt1Ty(LLContext), 2 /* At least 2 but can add more */,
			"cond.res", LLEndBB);
		for (llvm::pred_iterator PI = llvm::pred_begin(LLEndBB),
			                     PE = llvm::pred_end(LLEndBB);
			PI != PE; ++PI) {
			LLResPHINode->addIncoming(llvm::ConstantInt::getFalse(LLContext), *PI);
		}

		// Now dealing with the final RHS.
		// Basically if we made it here there is
		// only one condition left to check!
		Builder.SetInsertPoint(LLLHSTrueBB);
		llvm::Value* LLRHSCondV = GenCond(BinOp->RHS);
		// Need to re-obtain the last block since the condiition might have
		// added more blocks.
		LLLHSTrueBB = Builder.GetInsertBlock();
		
		Builder.CreateBr(LLEndBB);
		Builder.SetInsertPoint(LLEndBB);
		LLResPHINode->addIncoming(LLRHSCondV, LLLHSTrueBB);

		return LLResPHINode;
	}
	case TokenKind::BAR_BAR: { // ||
		
		llvm::BasicBlock* LLEndBB      = llvm::BasicBlock::Create(LLContext, "or.end", LLFunc);
		llvm::BasicBlock* LLLHSFalseBB = llvm::BasicBlock::Create(LLContext, "or.lhs.false", LLFunc);

		// Generate children
		GenBranchOnCond(BinOp->LHS, LLEndBB, LLLHSFalseBB);

		llvm::PHINode* LLResPHINode = llvm::PHINode::Create(
			llvm::Type::getInt1Ty(LLContext), 2 /* At least 2 but can add more */,
			"cond.res", LLEndBB);
		for (llvm::pred_iterator PI = llvm::pred_begin(LLEndBB),
			                     PE = llvm::pred_end(LLEndBB);
			PI != PE; ++PI) {
			LLResPHINode->addIncoming(llvm::ConstantInt::getTrue(LLContext), *PI);
		}

		Builder.SetInsertPoint(LLLHSFalseBB);
		llvm::Value* LLRHSCondV = GenCond(BinOp->RHS);
		// Need to re-obtain the last block since the condiition might have
		// added more blocks.
		LLLHSFalseBB = Builder.GetInsertBlock();
		
		Builder.CreateBr(LLEndBB);
		Builder.SetInsertPoint(LLEndBB);
		LLResPHINode->addIncoming(LLRHSCondV, LLLHSFalseBB);

		return LLResPHINode;
	}
	default:
		assert(!"Unimplemented GenBinaryOP()");
		return nullptr;
	}
}

llvm::Value* june::IRGen::GenUnaryOp(UnaryOp* UOP) {
	switch (UOP->Op) {
	case TokenKind::PLUS_PLUS: case TokenKind::POST_PLUS_PLUS: {
		llvm::Value* LLVal  = GenNode(UOP->Val);
		llvm::Value* LLRVal = CreateLoad(LLVal);
		llvm::Value* IncRes;
		if (UOP->Ty->GetKind() == TypeKind::POINTER) {
			// Pointer arithmetic, adds 1.
			llvm::SmallVector<llvm::Value*, 1> LLIdx = { GetLLInt64(1,  LLContext) };
			IncRes = CreateInBoundsGEP(LLRVal, LLIdx);
		} else {
			llvm::Value* LLOne = nullptr;
			switch (UOP->Val->Ty->GetKind()) {
			case TypeKind::I8: case TypeKind::C8:   LLOne = GetLLInt8(1, LLContext); break;
			case TypeKind::U8:                      LLOne = GetLLUInt8(1, LLContext); break;
			case TypeKind::I16: case TypeKind::C16: LLOne = GetLLInt16(1, LLContext); break;
			case TypeKind::U16:                     LLOne = GetLLUInt16(1, LLContext); break;
			case TypeKind::I32: case TypeKind::C32: LLOne = GetLLInt32(1, LLContext); break;
			case TypeKind::U32:                     LLOne = GetLLUInt32(1, LLContext); break;
			case TypeKind::I64:                     LLOne = GetLLInt64(1, LLContext); break;
			case TypeKind::U64:                     LLOne = GetLLUInt64(1, LLContext); break;
			default: assert(!"unimplementd!");
			}
			IncRes = Builder.CreateAdd(LLRVal, LLOne);
		}
		Builder.CreateStore(IncRes, LLVal);
		return UOP->Op == TokenKind::PLUS_PLUS ? IncRes : LLRVal;
	}
	case TokenKind::MINUS_MINUS: case TokenKind::POST_MINUS_MINUS: {
		llvm::Value* LLVal  = GenNode(UOP->Val);
		llvm::Value* LLRVal = CreateLoad(LLVal);
		llvm::Value* IncRes;
		if (UOP->Ty->GetKind() == TypeKind::POINTER) {
			// Pointer arithmetic, subs 1.
			llvm::SmallVector<llvm::Value*, 1> LLIdx = { GetLLInt64(-1,  LLContext) };
			IncRes = CreateInBoundsGEP(LLRVal, LLIdx);
		} else {
			llvm::Value* LLOne = nullptr;
			switch (UOP->Val->Ty->GetKind()) {
			case TypeKind::I8: case TypeKind::C8:   LLOne = GetLLInt8(1, LLContext); break;
			case TypeKind::U8:                      LLOne = GetLLUInt8(1, LLContext); break;
			case TypeKind::I16: case TypeKind::C16: LLOne = GetLLInt16(1, LLContext); break;
			case TypeKind::U16:                     LLOne = GetLLUInt16(1, LLContext); break;
			case TypeKind::I32: case TypeKind::C32: LLOne = GetLLInt32(1, LLContext); break;
			case TypeKind::U32:                     LLOne = GetLLUInt32(1, LLContext); break;
			case TypeKind::I64:                     LLOne = GetLLInt64(1, LLContext); break;
			case TypeKind::U64:                     LLOne = GetLLUInt64(1, LLContext); break;
			default: assert(!"unimplementd!");
			}
			IncRes = Builder.CreateSub(LLRVal, LLOne);
		}
		Builder.CreateStore(IncRes, LLVal);
		return UOP->Op == TokenKind::MINUS_MINUS ? IncRes : LLRVal;
	}
	case '-': {
		llvm::Value* LLVal = GenRValue(UOP->Val);
		if (UOP->Val->Ty->isInt()) {
			return Builder.CreateNeg(LLVal);
		} else {
			return Builder.CreateFNeg(LLVal);
		}
	}
	case '+':
		// unary is merely semantics
		//
		// The node is still needed for analysis
		// though.
		return GenRValue(UOP->Val);
	case '&':
		if (UOP->Val->is(AstKind::IDENT_REF) || UOP->Val->is(AstKind::FIELD_ACCESSOR)) {
			IdentRef* IRef = ocast<IdentRef*>(UOP->Val);
			if (IRef->RefKind == IdentRef::FUNCS) {
				FuncDecl* Func = (*IRef->FuncsRef)[0];
				GenFuncDecl(Func);
				return Func->LLAddress;
			}
		}

		// When GenRValue is called it makes sure
		// not to shave off the pointer value for
		// this operator. Because of that all this
		// needs to do is return the l-value.
		return GenNode(UOP->Val);
	case '*':
		return CreateLoad(GenNode(UOP->Val));
	case '!':
		if (UOP->Val->Ty->GetKind() == TypeKind::POINTER) {
			return Builder.CreateIsNull(GenRValue(UOP->Val));
		} else {
			return Builder.CreateNot(GenRValue(UOP->Val));
		}
	default:
		assert(!"Unimplemented GenUnaryOp()");
		return nullptr;
	}
}

llvm::Value* june::IRGen::GenNumberLiteral(NumberLiteral* Number) {
	switch (Number->Ty->GetKind()) {
	case TypeKind::I8:  
	case TypeKind::C8:  return GetLLInt8(Number->SignedIntValue , LLContext);
	case TypeKind::I16:
	case TypeKind::C16: return GetLLInt16(Number->SignedIntValue, LLContext);
	case TypeKind::I32:
	case TypeKind::C32: return GetLLInt32(Number->SignedIntValue, LLContext);
	case TypeKind::I64: return GetLLInt64(Number->SignedIntValue, LLContext);
	case TypeKind::U8:  return GetLLUInt8(Number->UnsignedIntValue, LLContext);
	case TypeKind::U16: return GetLLUInt16(Number->UnsignedIntValue, LLContext);
	case TypeKind::U32: return GetLLUInt32(Number->UnsignedIntValue, LLContext);
	case TypeKind::U64: return GetLLUInt64(Number->UnsignedIntValue, LLContext);
	case TypeKind::F32:
		return llvm::ConstantFP::get(LLContext, llvm::APFloat(Number->F32Value));
	case TypeKind::F64:
		return llvm::ConstantFP::get(LLContext, llvm::APFloat(Number->F64Value));
	default:
		assert(!"Unimplemented GenNumberLiteral() case");
		return nullptr;
	}
}

llvm::Value* june::IRGen::GenArray(Array* Arr, llvm::Value* LLArrAddr) {

	FixedArrayType* DestTy = GetArrayDestTy(Arr);

	if (Arr->CastTy && Arr->CastTy->GetKind() == TypeKind::POINTER) {
		// Must generate an array for a pointer
		// 1. If the array is foldable, create a global array and return
		//    the global array so that it can be pointed to.
		// 2. Otherwise create a local array on the heap and
		//    return the address of that to be pointed to.

		// TODO: Pretty sure this logic is actually broken since the
		// global array generated and then pointed to every single time
		// would be the same global array. This Pointing to a global array
		// should really only be done when the destination pointer is a contant.
		if (Arr->IsFoldable) {
			return MakeGlobalFixedArray(GenType(DestTy), GenConstArrayForFixedArray(Arr, DestTy));
		} else {
			// Creating a temporary array that the pointer can point to.
			LLArrAddr = CreateTempAlloca(GenType(DestTy));
			// Not foldable so must GEP into the indexes to fill.
			FillFixedArrayViaGEP(Arr, LLArrAddr, DestTy);
			return LLArrAddr;
		}
	} else {
		if (!LLArrAddr) {
			LLArrAddr = CreateTempAlloca(GenType(DestTy));
		}
		
		if (Arr->IsFoldable) {
			llvm::GlobalVariable* LLGVar
				= MakeGlobalFixedArray(GenType(DestTy), GenConstArrayForFixedArray(Arr, DestTy));

			// For the sake of efficiency we memcpy the array over
			// into the destination.
			Type* BaseType = DestTy->AsFixedArrayType()->GetBaseType();
			u64 TotalLinearLength = DestTy->AsFixedArrayType()->GetTotalLinearLength();

			// TODO: Not really sure llvm::MaybeAlign() is correct
			llvm::MaybeAlign LLAlignment = llvm::MaybeAlign();
			Builder.CreateMemCpy(
				LLArrAddr, LLAlignment,
				LLGVar, LLAlignment,
				TotalLinearLength * SizeOfTypeInBytes(GenType(BaseType))
			);
		} else {
			// Not foldable so must GEP into the indexes to fill.
			FillFixedArrayViaGEP(Arr, LLArrAddr, DestTy);
		}
	}

	return LLArrAddr;
}

llvm::Constant* june::IRGen::GenConstArrayForFixedArray(Array* Arr, FixedArrayType* DestTy) {
	u32 NumElements = DestTy->Length;

	llvm::SmallVector<llvm::Constant*, 4> LLElements;
	LLElements.reserve(NumElements);

	bool ElmsAreArrs = Arr->Ty->AsFixedArrayType()->ElmTy->GetKind() == TypeKind::FIXED_ARRAY;
	for (u32 i = 0; i < NumElements; i++) {
		if (i < Arr->NumElements) {
			Expr* Elm = Arr->GetElement(i);
			if (ElmsAreArrs) {
				LLElements.push_back(
					GenConstArrayForFixedArray(ocast<Array*>(Elm),
						DestTy->ElmTy->AsFixedArrayType()));
			} else {
				LLElements.push_back(llvm::cast<llvm::Constant>(GenRValue(Elm)));
			}
		} else {
			LLElements.push_back(GenZeroedValue(DestTy->ElmTy));
		}
	}

	llvm::ArrayType* LLArrType =
		llvm::cast<llvm::ArrayType>(GenType(DestTy));
	return llvm::ConstantArray::get(LLArrType, LLElements);
}

void june::IRGen::FillFixedArrayViaGEP(Array* Arr, llvm::Value* LLArr, FixedArrayType* DestTy) {
	u32 NumElements = DestTy->Length;

	bool ElmsAreArrs = Arr->Ty->AsFixedArrayType()->ElmTy->GetKind() == TypeKind::FIXED_ARRAY;
	for (u32 i = 0; i < NumElements; i++) {
		llvm::Value* LLAddrAtIndex = GetArrayIndexAddress(LLArr, GetLLInt32(i, LLContext));
		if (i < Arr->NumElements) {
			Expr* Elm = Arr->GetElement(i);
			if (!ElmsAreArrs) {
				Builder.CreateStore(GenRValue(Elm), LLAddrAtIndex);
			} else {
				FillFixedArrayViaGEP(
					ocast<Array*>(Elm), LLAddrAtIndex, DestTy->ElmTy->AsFixedArrayType());
			}
		} else {
			GenDefaultValue(DestTy->ElmTy, LLAddrAtIndex);
		}
	}
}

llvm::Value* june::IRGen::GenArrayAccess(ArrayAccess* AA) {

	llvm::Value* LLSite  = GenNode(AA->Site);

	if (AA->Site->Ty->GetKind() == TypeKind::FIXED_ARRAY) {
		llvm::Value* LLIndex = GenRValue(AA->Index);
		return GetArrayIndexAddress(LLSite, LLIndex);
	} else if (AA->Site->Ty->GetKind() == TypeKind::POINTER) {
		LLSite = CreateLoad(LLSite);
		llvm::Value* LLIndex = GenRValue(AA->Index);
		return CreateGEP(LLSite, LLIndex);
	} else if (AA->Site->Ty->GetKind() == TypeKind::TUPLE) {
		u32 Idx = ocast<NumberLiteral*>(AA->Index)->UnsignedIntValue;
		return CreateStructGEP(LLSite, Idx);
	} else {
		assert(!"Unreachable!");
		return nullptr;
	}
}

llvm::Value* june::IRGen::GenTypeCast(TypeCast* Cast) {
	return GenCast(Cast->ToTy, Cast->Val->Ty, GenRValue(Cast->Val));
}

llvm::Value* june::IRGen::GenHeapAllocType(HeapAllocType* HeapAlloc) {
	if (HeapAlloc->TypeToAlloc->GetKind() == TypeKind::FIXED_ARRAY) {
		FixedArrayType* ArrTy = HeapAlloc->TypeToAlloc->AsFixedArrayType();

		FixedArrayType* ArrTyItr = ArrTy;
		llvm::Value* LLTotalLinearLength = GenRValue(ArrTyItr->LengthAsExpr);
		while (ArrTyItr->ElmTy->GetKind() == TypeKind::FIXED_ARRAY) {
			ArrTyItr = ArrTyItr->ElmTy->AsFixedArrayType();
			LLTotalLinearLength =
				Builder.CreateMul(LLTotalLinearLength, GenRValue(ArrTyItr->LengthAsExpr));
		}
		
		llvm::Value* LLArrStartPtr = GenMalloc(GenType(ArrTy->GetBaseType()), LLTotalLinearLength);
		
		Type* ArrBaseTy = ArrTy->GetBaseType();
		if (ArrBaseTy->GetKind() == TypeKind::RECORD) {
			GenRecordArrayObjsInitCalls(ArrTy, LLArrStartPtr, LLTotalLinearLength);
		}

		return LLArrStartPtr;
	} else {
		return GenMalloc(GenType(HeapAlloc->TypeToAlloc), nullptr);
	}
}

llvm::Value* june::IRGen::GenTernaryCond(TernaryCond* Ternary) {
	llvm::Value* LLCond = GenCond(Ternary->Cond);
	llvm::Value* LLVal1 = GenRValue(Ternary->Val1);
	llvm::Value* LLVal2 = GenRValue(Ternary->Val2);
	return Builder.CreateSelect(LLCond, LLVal1, LLVal2);
}

llvm::Value* june::IRGen::GenTuple(Tuple* Tup, llvm::Value* LLAddr) {
	if (!LLAddr) {
		LLAddr = CreateTempAlloca(GenType(Tup->Ty));
	}

	for (u32 i = 0; i < Tup->Values.size(); i++) {
		llvm::Value* LLValAddr = CreateStructGEP(LLAddr, i);
		GenAssignment(LLValAddr, Tup->Values[i]);
	}

	return LLAddr;
}

llvm::Value* june::IRGen::GenAssignment(llvm::Value* LLAddr, Expr* Val) {
	llvm::Value* LLRValToStore = nullptr;
	if (Val->Kind == AstKind::ARRAY) {
		llvm::Value* LLArr = GenArray(ocast<Array*>(Val), LLAddr);
		if (Val->CastTy) {
			// Still need to cast to ensure the array meets the requirements
			// of its destination.
			llvm::Value* LLRVal = GenCast(Val->CastTy, Val->Ty, LLArr);
			if (Val->CastTy->GetKind() == TypeKind::POINTER) {
				// Storing the array address into the pointer.
				LLRValToStore = LLRVal;
			}
		}
	} else if (Val->Kind == AstKind::FUNC_CALL) {
		FuncCall* Call = ocast<FuncCall*>(Val);
		if (Call->IsConstructorCall || 
			(Call->CalledFunc && FuncNeedsRVO(Call->CalledFunc))
			) {
			GenFuncCall(LLAddr, Call);
		} else {
			LLRValToStore = GenRValue(Val);
		}
	} else if (Val->Kind == AstKind::TUPLE) {
		GenTuple(ocast<Tuple*>(Val), LLAddr);
	} else {
		LLRValToStore = GenRValue(Val);
	}
	if (LLRValToStore) {
		Builder.CreateStore(LLRValToStore, LLAddr);
		EmitDebugLocation(Val);
	}
	return LLAddr;
}

void june::IRGen::GenBlock(llvm::BasicBlock* LLBB, LexScope& Scope) {
	if (LLBB) {
		GenBranchIfNotTerm(LLBB);
		Builder.SetInsertPoint(LLBB);
	}
	for (AstNode* Stmt : Scope.Stmts) {
		GenNode(Stmt);
	}
}

llvm::Type* june::IRGen::GenType(Type* Ty) {
	return june::GenType(Context, Ty);
}

llvm::Value* june::IRGen::GenCast(Type* ToType, Type* FromType, llvm::Value* LLVal) {
	
	llvm::Type* LLCastType = GenType(ToType);

	switch (ToType->GetKind()) {
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
		//  --- TO Integers ---
		if (FromType->isInt()) {
			// Int to Int
			if (ToType->MemSize() < FromType->MemSize()) {
				// Signed and unsigned downcasting use trunc
				return Builder.CreateTrunc(LLVal, LLCastType);
			} else {
				if (ToType->isSigned()) {
					// Signed upcasting
					return Builder.CreateSExt(LLVal, LLCastType);
				} else {
					// Unsigned upcasting
					return Builder.CreateZExt(LLVal, LLCastType);
				}
			}
		} else if (FromType->isFloat()) {
			// Floating to Int
			if (ToType->isSigned()) {
				return Builder.CreateFPToSI(LLVal, LLCastType);
			} else {
				return Builder.CreateFPToUI(LLVal, LLCastType);
			}
		} else if (FromType->GetKind() == TypeKind::POINTER) {
			// Ptr to Int
			return Builder.CreatePtrToInt(LLVal, LLCastType);
		}
		goto missing_cast_case_lab;
	case TypeKind::F32:
	case TypeKind::F64:
		//  --- TO Floating ---
		if (FromType->isFloat()) {
			// Float to Float
			if (ToType->MemSize() > FromType->MemSize()) {
				// Upcasting float
				return Builder.CreateFPExt(LLVal, LLCastType);
			} else {
				// Downcasting float
				return Builder.CreateFPTrunc(LLVal, LLCastType);
			}
		} else if (FromType->isInt()) {
			// Int to Float
			if (FromType->isSigned()) {
				return Builder.CreateSIToFP(LLVal, LLCastType);
			} else {
				return Builder.CreateUIToFP(LLVal, LLCastType);
			}
		}
		goto missing_cast_case_lab;
	case TypeKind::POINTER:
		//  --- TO Pointers ---
		if (FromType->GetKind() == TypeKind::FIXED_ARRAY) {
			// Fixed-Array to Pointer
			return GetArrayAsPtr1Nesting(LLVal);
		} else if (FromType->GetKind() == TypeKind::POINTER) {
			// Pointer to Pointer
			return Builder.CreateBitCast(LLVal, LLCastType);
		} else if (FromType->GetKind() == TypeKind::NULLPTR) {
			return LLVal; // Already handled during generation
		} else if (FromType->isInt()) {
			// Int to Ptr
			return Builder.CreateIntToPtr(LLVal, LLCastType);
		}
		goto missing_cast_case_lab;
	case TypeKind::FIXED_ARRAY:
		if (FromType->GetKind() == TypeKind::FIXED_ARRAY)
			return LLVal; // Handled during generation
		goto missing_cast_case_lab;
	default:
		missing_cast_case_lab:
		assert(!"Missing cast case");
		return nullptr;
	}
}

inline llvm::Value* june::IRGen::CreateLoad(llvm::Value* LLAddr, const c8* Name) {
	return Builder.CreateLoad(LLAddr->getType()->getPointerElementType(), LLAddr, Name);
}

inline llvm::Value* june::IRGen::CreateAlloca(Type* Ty, const c8* Name) {
	return Builder.CreateAlloca(GenType(Ty), nullptr, Name);
}

void june::IRGen::GenDefaultValue(Type* Ty, llvm::Value* LLAddr) {
	if (Ty->GetKind() == TypeKind::RECORD) {
		RecordDecl* Record = Ty->AsRecordType()->Record;
		if (Record->FieldsHaveAssignment) {
			GenDefaultRecordInitCall(Record, LLAddr);
			return;
		}
	} else if (Ty->GetKind() == TypeKind::TUPLE) {
		if (GenDefaultTupleValue(Ty->AsTupleType(), LLAddr)) {
			return;
		}
	} else if (Ty->GetKind() == TypeKind::FIXED_ARRAY) {
		FixedArrayType* ArrTy = Ty->AsFixedArrayType();
		Type* ArrBaseTy = ArrTy->GetBaseType();
		if (ArrBaseTy->GetKind() == TypeKind::RECORD) {
			llvm::Value* LLArrStartPtr = GetArrayAsPtrGeneral(LLAddr, ArrTy->GetNestingLevel() + 1);
			llvm::Value* LLTotalLinearLength = GetLLUInt32(ArrTy->GetTotalLinearLength(), LLContext);
			GenRecordArrayObjsInitCalls(ArrTy, LLArrStartPtr, LLTotalLinearLength);
			return;
		}
	}
	Builder.CreateStore(GenZeroedValue(Ty), LLAddr);
}

bool june::IRGen::GenDefaultTupleValue(TupleType* TupleTy, llvm::Value* LLAddr) {
	bool RecordsNeedDefaultInitCall = false;
	u32 IdxCount = 0;
	for (Type* ValTy : TupleTy->SubTypes) {
		if (ValTy->GetKind() == TypeKind::RECORD) {
			RecordDecl* Record = ValTy->AsRecordType()->Record;
			if (Record->FieldsHaveAssignment) {
				GenDefaultRecordInitCall(Record, CreateStructGEP(LLAddr, IdxCount));
				RecordsNeedDefaultInitCall = true;
			}
		} else if (ValTy->GetKind() == TypeKind::TUPLE) {
			RecordsNeedDefaultInitCall
				|= GenDefaultTupleValue(ValTy->AsTupleType(), CreateStructGEP(LLAddr, IdxCount));
		}
		++IdxCount;
	}
	return RecordsNeedDefaultInitCall;
}

void june::IRGen::GenRecordArrayObjsInitCalls(FixedArrayType* ArrTy,
	                                          llvm::Value* LLArrStartPtr,
	                                          llvm::Value* LLTotalLinearLength) {

	// Looping through the array and calling the initialization
	// function for each element.

	llvm::BasicBlock* BeforeLoopBB = Builder.GetInsertBlock();
	llvm::Value* LLEndOfArrPtr = CreateInBoundsGEP(LLArrStartPtr, { LLTotalLinearLength });

	llvm::BasicBlock* LoopBB    = llvm::BasicBlock::Create(LLContext, "arr.objconstr.loop", LLFunc);
	llvm::BasicBlock* LoopEndBB = llvm::BasicBlock::Create(LLContext, "arr.objconstr.end", LLFunc);

	Builder.CreateBr(LoopBB);
	Builder.SetInsertPoint(LoopBB);

	RecordType* RecordTy = ArrTy->GetBaseType()->AsRecordType();
	// Pointer used to traverse through the array
	llvm::PHINode* LLArrPtr = Builder.CreatePHI(llvm::PointerType::get(GenType(RecordTy), 0), 0, "obj.loop.ptr");

	// Incoming value to the start of the array from the incoming block
	LLArrPtr->addIncoming(LLArrStartPtr, BeforeLoopBB);

	GenDefaultRecordInitCall(RecordTy->Record, LLArrPtr);

	// Move to the next element in the array
	llvm::Value* LLNextElementPtr = CreateInBoundsGEP(LLArrPtr, { GetLLUInt32(1, LLContext) });

	// Checking if all objects have been looped over
	llvm::Value* LLLoopEndCond = Builder.CreateICmpEQ(LLNextElementPtr, LLEndOfArrPtr);
	Builder.CreateCondBr(LLLoopEndCond, LoopEndBB, LoopBB);

	// The value must come from the block that 'LLNextCount' is created
	// in which would be whatever the current block is.
	llvm::BasicBlock* LLCurBlock = Builder.GetInsertBlock();
	LLArrPtr->addIncoming(LLNextElementPtr, LLCurBlock);

	// End of loop
	Builder.SetInsertPoint(LoopEndBB);
}

llvm::Constant* june::IRGen::GenZeroedValue(Type* Ty) {
	switch (Ty->GetKind()) {
	case TypeKind::I8:  case TypeKind::C8:  return GetLLInt8(0, LLContext);
	case TypeKind::U8:                      return GetLLUInt8(0, LLContext);
	case TypeKind::I16: case TypeKind::C16: return GetLLInt16(0, LLContext);
	case TypeKind::U16:                     return GetLLUInt16(0, LLContext);
	case TypeKind::I32: case TypeKind::C32: return GetLLInt32(0, LLContext);
	case TypeKind::U32:                     return GetLLUInt32(0, LLContext);
	case TypeKind::I64:                     return GetLLInt64(0, LLContext);
	case TypeKind::U64:                     return GetLLUInt64(0, LLContext);
	case TypeKind::F32:
		return llvm::ConstantFP::get(LLContext, llvm::APFloat((float)0.0F));
	case TypeKind::F64:
		return llvm::ConstantFP::get(LLContext, llvm::APFloat((double)0.0));
	case TypeKind::BOOL:
		return llvm::ConstantInt::getFalse(LLContext);
	case TypeKind::POINTER:
	case TypeKind::FUNCTION:
		return llvm::Constant::getNullValue(GenType(Ty));
	case TypeKind::FIXED_ARRAY:
		return llvm::ConstantAggregateZero::get(GenType(Ty));
	case TypeKind::RECORD:
	case TypeKind::TUPLE:
		return llvm::ConstantAggregateZero::get(GenType(Ty));
	default:
		assert(!"Failed to implement GenZeroedValue() value for type");
		return nullptr;
	}
}

void june::IRGen::GenBranchIfNotTerm(llvm::BasicBlock* LLBB, LexScope* ScopeBeingEnded) {
	// Avoiding back-to-back branching
	llvm::BasicBlock* CurBB = Builder.GetInsertBlock();
	if (!CurBB->getTerminator()) {
		// Unconditionally branch
		llvm::Instruction* LLInst = Builder.CreateBr(LLBB);
		if (EmitDebugInfo) {
			if (ScopeBeingEnded)
				GetDIEmitter()->EmitDebugLocation(LLInst, ScopeBeingEnded->EndLoc);
		}
	}
}

void june::IRGen::GenSetInsertBlock(llvm::BasicBlock* LLBB, LexScope* ScopeBeingEnded) {
	GenBranchIfNotTerm(LLBB, ScopeBeingEnded);
	Builder.SetInsertPoint(LLBB);
}

llvm::GlobalVariable* june::IRGen::MakeGlobalVar(std::string& Name, llvm::Type* LLTy) {
	LLModule.getOrInsertGlobal(Name, LLTy);
	return LLModule.getNamedGlobal(Name);
}

llvm::GlobalVariable* june::IRGen::MakeGlobalFixedArray(llvm::Type* LLDestTy, llvm::Constant* LLArr) {
	// TODO: Hand over to mangler
	std::string LLName = "__gA.";
	LLName += std::to_string(Context.NumGeneratedGlobalArrays++);

	llvm::GlobalVariable* LLGVar = MakeGlobalVar(LLName, LLDestTy);
	LLGVar->setInitializer(LLArr);

	if (DisplayLLVMIR) {
		LLGVar->print(llvm::outs());
		llvm::outs() << '\n';
	}
	return LLGVar;
}

u64 june::IRGen::SizeOfTypeInBytes(llvm::Type* LLType) {
	const llvm::DataLayout& LLDataLayout = LLModule.getDataLayout();
	llvm::TypeSize LLTypeSize = LLDataLayout.getTypeSizeInBits(LLType);
	return LLTypeSize.getFixedSize() / 8;
}

llvm::Value* june::IRGen::GetArrayAsPtr1Nesting(llvm::Value* LLArr) {
	return CreateInBoundsGEP(LLArr,
		{ GetLLUInt32(0, LLContext), GetLLUInt32(0, LLContext) });
}

llvm::Value* june::IRGen::GetArrayAsPtrGeneral(llvm::Value* LLArr, u32 NestingLevel) {
	llvm::SmallVector<llvm::Value*, 3> LLIdxs;
	for (u32 i = 0; i < NestingLevel + 1; i++) {
		LLIdxs.push_back(GetLLUInt32(0, LLContext));
	}
	return CreateInBoundsGEP(LLArr, LLIdxs);
}

inline llvm::Value* june::IRGen::CreateInBoundsGEP(llvm::Value* LLAddr, llvm::ArrayRef<llvm::Value*> IdxList) {
	return Builder.CreateInBoundsGEP(LLAddr->getType()->getScalarType()->getPointerElementType(),
		LLAddr, IdxList);
}

inline llvm::Value* june::IRGen::CreateStructGEP(llvm::Value* LLAddr, u32 Idx) {
	return Builder.CreateConstInBoundsGEP2_32(
		LLAddr->getType()->getScalarType()->getPointerElementType(), LLAddr, 0, Idx);
}

inline llvm::Value* june::IRGen::CreateGEP(llvm::Value* LLAddr, llvm::ArrayRef<llvm::Value*> IdxList) {
	return Builder.CreateGEP(LLAddr->getType()->getScalarType()->getPointerElementType(), LLAddr, IdxList);
}

inline llvm::Value* june::IRGen::GetArrayIndexAddress(llvm::Value* LLArr, llvm::Value* LLIndex) {
	return CreateInBoundsGEP(
		LLArr,
		{ GetLLUInt32(0, LLContext), LLIndex });
}

llvm::Value* june::IRGen::GetAddressOfVar(VarDecl* Var) {
	if (Var->ParamIdx != -1 && Var->Ty->GetKind() == TypeKind::FIXED_ARRAY) {
		return CreateLoad(Var->LLAddress);
	} else if (Var->FieldIdx != -1) {
		// LLThis refers to a member
		// pointer within a member function
		// so it can be used retrieve the field.

		return CreateStructGEP(LLThis, Var->FieldIdx);
	} else {
		if (Var->IsGlobal) {
			GenGlobalVarDecl(Var);
		}

		return Var->LLAddress;
	}
}

void june::IRGen::GenBranchOnCond(Expr* Cond, llvm::BasicBlock* LLTrueBB, llvm::BasicBlock* LLFalseBB) {

	// See: https://github.com/llvm/llvm-project/blob/839ac62c5085d895d3165bc5024db623a7a78813/clang/lib/CodeGen/CodeGenFunction.cpp
	// EmitBranchOnBoolExpr

	if (Cond->is(AstKind::BINARY_OP)) {
		BinaryOp* BinOp = ocast<BinaryOp*>(Cond);

		// Binary operators in the form:  a && b
		if (BinOp->Op == TokenKind::AMP_AMP) {
			
			// a and b    <= if a is true go to the new 'LLLHSTrueBB' otherwise go to false block

			llvm::BasicBlock* LLLHSTrueBB = llvm::BasicBlock::Create(LLContext, "and.lhs.true", LLFunc);
			GenBranchOnCond(BinOp->LHS, LLLHSTrueBB, LLFalseBB);
			
			Builder.SetInsertPoint(LLLHSTrueBB);
			GenBranchOnCond(BinOp->RHS, LLTrueBB, LLFalseBB);
			return;
		}
		// Binary operators in the form:  a || b
		else if (BinOp->Op == TokenKind::BAR_BAR) {
			
			// a or b    <= if a is true don't check b.

			llvm::BasicBlock* LLLHSFalseBB = llvm::BasicBlock::Create(LLContext, "or.lhs.false", LLFunc);
			GenBranchOnCond(BinOp->LHS, LLTrueBB, LLLHSFalseBB);

			Builder.SetInsertPoint(LLLHSFalseBB);
			GenBranchOnCond(BinOp->RHS, LLTrueBB, LLFalseBB);
			return;
		}
	}

	llvm::Value* LLCond = GenCond(Cond);
	EmitDebugLocation(Cond);
	Builder.CreateCondBr(LLCond, LLTrueBB, LLFalseBB);
}

llvm::Value* june::IRGen::GenCond(Expr* Cond) {
	llvm::Value* LLVal = GenRValue(Cond);
	if (Cond->Ty->GetKind() == TypeKind::POINTER)
		return Builder.CreateIsNotNull(LLVal);
	return LLVal;
}

llvm::Value* june::IRGen::CreateTempAlloca(llvm::Type* LLTy) {
	llvm::BasicBlock* BackupInsertBlock = Builder.GetInsertBlock();
	// The address does not exist so it needs to be created.
	llvm::BasicBlock* LLEntryBlock = &LLFunc->getEntryBlock();
	if (LLEntryBlock->getInstList().empty()) {
		Builder.SetInsertPoint(LLEntryBlock);
	} else {
		Builder.SetInsertPoint(&LLEntryBlock->getInstList().front());
	}
	llvm::Value* LLAddr = Builder.CreateAlloca(LLTy);
	Builder.SetInsertPoint(BackupInsertBlock);
	return LLAddr;
}

void june::IRGen::GenDefaultRecordInitCall(RecordDecl* Record, llvm::Value* LLAddr) {
	auto it = Context.DefaultRecordInitFuncs.find(Record);
	if (it != Context.DefaultRecordInitFuncs.end()) {
		Builder.CreateCall(it->second, LLAddr);
		return;
	}

	llvm::Type* LLStructPtrTy = llvm::PointerType::get(Record->LLStructTy, 0);

	// Need to create the declaration for the default init func
	llvm::FunctionType* LLFuncType =
		llvm::FunctionType::get(llvm::Type::getVoidTy(LLContext),
			{ LLStructPtrTy }, false);

	llvm::Function* LLFunc = llvm::Function::Create(
		LLFuncType,
		llvm::Function::ExternalLinkage, // publically visible
		"__june.record.init",
		LLModule
	);

	llvm::BasicBlock* LLEntryBlock = llvm::BasicBlock::Create(LLContext, "entry.block", LLFunc);
	llvm::BasicBlock* BackupBasicBlock = Builder.GetInsertBlock();
	Builder.SetInsertPoint(LLEntryBlock);
	llvm::Value* LLStructPtrAddr = Builder.CreateAlloca(LLStructPtrTy);
	Builder.CreateStore(LLFunc->getArg(0), LLStructPtrAddr);
	
	llvm::Value* PrevLLThis = LLThis;
	LLThis = CreateLoad(LLStructPtrAddr, "this");

	for (VarDecl* Field : Record->FieldsByIdxOrder) {
		llvm::Value* LLFieldAddr = CreateStructGEP(LLThis, Field->FieldIdx);
		if (Field->Assignment) {
			GenAssignment(LLFieldAddr, Field->Assignment);
		} else {
			GenDefaultValue(Field->Ty, LLFieldAddr);
		}
	}

	Builder.CreateRetVoid();
	
	LLThis = PrevLLThis;

	if (DisplayLLVMIR) {
		LLFunc->print(llvm::outs());
		llvm::outs() << '\n';
	}


	Builder.SetInsertPoint(BackupBasicBlock);
	Context.DefaultRecordInitFuncs.insert({ Record, LLFunc });
	Builder.CreateCall(LLFunc, LLAddr);

}

llvm::Value* june::IRGen::GenMalloc(llvm::Type* LLType, llvm::Value* LLArrSize) {

	llvm::Value* LLMalloc = llvm::CallInst::CreateMalloc(
		Builder.GetInsertBlock(),                              // llvm::BasicBlock *InsertAtEnd
		llvm::Type::getInt64Ty(LLContext),                     // llvm::Type* IntPtrTy
		LLType,                                                // llvm::Type* AllocTy
		GetLLUInt64(SizeOfTypeInBytes(LLType), LLContext),     // llvm::Value* AllocSize
		LLArrSize,
		nullptr,
		""
	);
	Builder.Insert(LLMalloc);

	return LLMalloc;
}

// For reference:
// https://github.com/llvm/llvm-project/blob/main/clang/lib/CodeGen/CGBuiltin.cpp
// https://github.com/google/swiftshader/blob/master/src/Reactor/LLVMReactor.cpp
llvm::Value* june::IRGen::GenLLVMIntrinsicCall(FuncCall* Call) {
	switch (Call->CalledFunc->LLVMIntrinsicID) {
	case llvm::Intrinsic::memcpy: {
		llvm::Align LLAlignment = llvm::Align();
		return Builder.CreateMemCpy(
			GenRValue(Call->Args[0]), LLAlignment,
			GenRValue(Call->Args[1]), LLAlignment,
			GenRValue(Call->Args[2])
		);
	}
	case llvm::Intrinsic::sin: {
		llvm::Value* Arg0 = GenRValue(Call->Args[0]);
		llvm::Function* LLSinFunc = llvm::Intrinsic::getDeclaration(
			&LLModule, llvm::Intrinsic::sin, { Arg0->getType() });
		return Builder.CreateCall(LLSinFunc, { Arg0 });
	}
	case llvm::Intrinsic::cos: {
		llvm::Value* Arg0 = GenRValue(Call->Args[0]);
		llvm::Function* LLSinFunc = llvm::Intrinsic::getDeclaration(
			&LLModule, llvm::Intrinsic::cos, { Arg0->getType() });
		return Builder.CreateCall(LLSinFunc, { Arg0 });
	}
	default:
		assert(!"Failed to implement llvm intrinsic call!");
		break;
	}
}

june::FixedArrayType* june::IRGen::GetArrayDestTy(Array* Arr) {
	FixedArrayType* DestTy = Arr->Ty->AsFixedArrayType();
	if (Arr->CastTy) {
		if (Arr->CastTy->GetKind() == TypeKind::FIXED_ARRAY) {
			DestTy = Arr->CastTy->AsFixedArrayType();
		} else {
			DestTy = FixedArrayType::Create(
				           Arr->CastTy->AsContainerType()->ElmTy,
				           DestTy->Length,
				           Context);
		}
	}
	return DestTy;
}

llvm::Constant* june::IRGen::GenGlobalConstVal(VarDecl* Global) {
	Type* Ty = Global->Ty;
	if (Ty->GetKind() == TypeKind::RECORD || Ty->GetKind() == TypeKind::TUPLE) {
		// TODO: For now im just zero initializing
		//       the struct but if all the fields are
		//       foldable then it should create a non-zeroed
		//       constant struct
		return GenZeroedValue(Ty);
	} else if (!Global->Assignment) {
		return GenZeroedValue(Ty);
	} else {
		if (Global->Assignment->IsFoldable) {
			if (Global->Assignment->is(AstKind::ARRAY)) {

				Array* Arr = ocast<Array*>(Global->Assignment);
				
				if (Global->Ty->GetKind() == TypeKind::POINTER) {
					// The destination is a pointer so a global array needs
					// to be created first, then that global array needs
					// to be pointed to the pointer value of the global.
					llvm::Value* LLGArr = GenArray(Arr, nullptr);
					return llvm::cast<llvm::Constant>(GetArrayAsPtr1Nesting(LLGArr));
				} else if (Global->Ty->GetKind() == TypeKind::FIXED_ARRAY) {
					return GenConstArrayForFixedArray(
						ocast<Array*>(Global->Assignment), GetArrayDestTy(Arr));
				}
			}
			return llvm::cast<llvm::Constant>(GenRValue(Global->Assignment));
		} else {
			// Not foldable so it recieves a default value and
			// it initialized later
			return GenZeroedValue(Ty);
		}
	}
}

bool june::IRGen::FuncNeedsRVO(FuncDecl* Func) {
	// Valid reasons for using RVO
	// 1. The structure is big
	// 2. The structure has a destructor
	if (Func->RetTy->GetKind() != TypeKind::RECORD &&
		Func->RetTy->GetKind() != TypeKind::TUPLE) {
		return false;
	}
	// TODO: Come up with a better size indication.
	//       Honestly, it should probably be system dependent?
	const llvm::StructLayout* LLStructLayout = LLModule.getDataLayout().getStructLayout(
		llvm::cast<llvm::StructType>(GenType(Func->RetTy)));
	if (LLStructLayout->getSizeInBytes() > 8) {
		return true;
	}
	return false;
}

void june::IRGen::EmitDebugLocation(AstNode* Node) {
	if (EmitDebugInfo) {
		GetDIEmitter()->EmitDebugLocation(Builder, Node);
	}
}

june::DebugInfoEmitter* june::IRGen::GetDIEmitter(Decl* D) {
	return D->FU->DIEmitter;
}

june::DebugInfoEmitter* june::IRGen::GetDIEmitter() {
	assert(CFunc && "Should only obtain the debug emitter in this context when inside a function");
	return CFunc->FU->DIEmitter;
}

void june::IRGen::GenStoreRVOStructRes(Expr* Assignment) {
	llvm::Value* LLRVOStructAddr;
	if (LLThis) {
		// Must be the second parameter
		LLRVOStructAddr = LLFunc->getArg(1);
	} else {
		LLRVOStructAddr = LLFunc->getArg(0);
	}

	llvm::Value* LLStructAssignment = GenNode(Assignment);

	llvm::StructType* LLStructTy = llvm::cast<llvm::StructType>(
		LLStructAssignment->getType()->getPointerElementType());

	const llvm::StructLayout* LLStructLayout = LLModule.getDataLayout().getStructLayout(LLStructTy);
	llvm::Align LLAlignment = LLStructLayout->getAlignment();
	
	Builder.CreateMemCpy(
		LLRVOStructAddr   , LLAlignment,
		LLStructAssignment, LLAlignment,
		SizeOfTypeInBytes(LLStructTy)
	);
}
