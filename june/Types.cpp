#include "Types.h"

#include <assert.h>

#include "Ast.h"
#include "JuneContext.h"

bool june::Type::is(Type* T) const {
	const Type* ThisUnboxed = UnboxGeneric();
	Type* ThatUnboxed = T->UnboxGeneric();
	if (ThisUnboxed != this || ThatUnboxed != T) {
		return ThisUnboxed->is(ThatUnboxed);
	}
	return this == T;
}

june::Type* june::Type::GetIntTypeBasedOnSize(u32 S, bool Signed, JuneContext& C) {
	switch (S) {
	case 1: return Signed ? C.I8Type  : C.U8Type;
	case 2: return Signed ? C.I16Type : C.U16Type;
	case 4: return Signed ? C.I32Type : C.U32Type;
	case 8: return Signed ? C.I64Type : C.U64Type;
	default:
		assert(!"Bad memory size");
		return nullptr;
	}
}

june::Type* june::Type::GetFloatTypeBasedOnSize(u32 S, JuneContext& C) {
	switch (S) {
	case 4: return C.F32Type;
	case 8: return C.F64Type;
	default:
		assert(!"Bad memory size");
		return nullptr;
	}
}

june::TypeKind june::Type::GetKind() const {
	return UnboxGeneric()->Kind;
}

bool june::Type::isInt() {
	switch (GetKind()) {
	case TypeKind::I8:
	case TypeKind::I16:
	case TypeKind::I32:
	case TypeKind::I64:
	case TypeKind::U8:
	case TypeKind::U16:
	case TypeKind::U32:
	case TypeKind::U64:
		// Characters get included so math can
		// be performed on them
	case TypeKind::C8:
	case TypeKind::C16:
	case TypeKind::C32:
		return true;
	default:
		return false;
	};
}

bool june::Type::isFloat() {
	TypeKind K = GetKind();
	return K == TypeKind::F32 || K == TypeKind::F64;
}

bool june::Type::isSigned() {
	switch (GetKind()) {
	case TypeKind::I8:
	case TypeKind::I16:
	case TypeKind::I32:
	case TypeKind::I64:
	case TypeKind::C8:
	case TypeKind::C16:
	case TypeKind::C32:
	case TypeKind::F32:
	case TypeKind::F64:
		return true;
	default:
		return false;
	};
}

bool june::Type::isNumber() {
	switch (GetKind()) {
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
	case TypeKind::F32:
	case TypeKind::F64:
		return true;
	default:
		return false;
	};
}

std::string june::Type::ToStr() const {
	switch (Kind) {
	case TypeKind::I8:        return "i8";
	case TypeKind::I16:       return "i16";
	case TypeKind::I32:       return "i32";
	case TypeKind::I64:       return "i64";
	case TypeKind::U8:        return "u8";
	case TypeKind::U16:       return "u16";
	case TypeKind::U32:       return "u32";
	case TypeKind::U64:       return "u64";
	case TypeKind::C8:        return "c8";
	case TypeKind::C16:       return "c16";
	case TypeKind::C32:       return "c32";
	case TypeKind::F32:       return "f32";
	case TypeKind::F64:       return "f64";
	case TypeKind::VOID:      return "void";
	case TypeKind::BOOL:      return "bool";
	case TypeKind::NULLPTR:   return "null";
	case TypeKind::ERROR:     return "error";
	case TypeKind::UNDEFINED: return "undefined";
	default:
		assert(!"Unhandled ToStr() for type");
		return "";
	};
}

u32 june::Type::MemSize() {
	switch (GetKind()) {
	case TypeKind::I8:
	case TypeKind::U8:
	case TypeKind::C8:
		return 1;
	case TypeKind::I16:
	case TypeKind::U16:
	case TypeKind::C16:
		return 2;
	case TypeKind::I32:
	case TypeKind::U32:
	case TypeKind::C32:
		return 4;
	case TypeKind::I64:
	case TypeKind::U64:
		return 8;
	case TypeKind::F32: return 4;
	case TypeKind::F64: return 8;
	default:
		assert(!"Missing memory size for type");
		return 0;
	};
}

const june::Type* june::Type::UnboxGeneric() const {
	if (Kind == TypeKind::GENERIC_TYPE) {
		Type* BoundTy = ocast<const GenericType*>(this)->BoundTy;
		if (BoundTy) return BoundTy;
	}
	return this;
}

june::Type* june::Type::UnboxGeneric() {
	if (Kind == TypeKind::GENERIC_TYPE)
		return ocast<GenericType*>(this)->BoundTy;
	return this;
}

june::PointerType* june::Type::AsPointerType() {
	assert(GetKind() == TypeKind::POINTER && "Not a pointer type");
	return ocast<PointerType*>(UnboxGeneric());
}

june::FixedArrayType* june::Type::AsFixedArrayType() {
	assert(GetKind() == TypeKind::FIXED_ARRAY && "Not a fixed array type");
	return ocast<FixedArrayType*>(UnboxGeneric());
}

june::ContainerType* june::Type::AsContainerType() {
	return ocast<ContainerType*>(UnboxGeneric());
}

june::RecordType* june::Type::AsRecordType() {
	assert(GetKind() == TypeKind::RECORD && "Not a record type");
	return ocast<RecordType*>(UnboxGeneric());
}

june::FunctionType* june::Type::AsFunctionType() {
	assert(GetKind() == TypeKind::FUNCTION && "Not a function type");
	return ocast<FunctionType*>(UnboxGeneric());
}

june::TupleType* june::Type::AsTupleType() {
	assert(GetKind() == TypeKind::TUPLE && "Not a tuple type");
	return ocast<TupleType*>(UnboxGeneric());
}

june::GenericType* june::Type::AsGenericType() {
	assert(Kind == TypeKind::GENERIC_TYPE && "Not a generic type");
	return ocast<GenericType*>(this);
}

//===-------------------------------===//
// Container Type
//===-------------------------------===//

june::Type* june::ContainerType::GetBaseType() const {
	if (ElmTy->GetKind() == GetKind())
		return ElmTy->AsContainerType()->GetBaseType();
	return ElmTy;
}

u32 june::ContainerType::GetNestingLevel() const {
	if (ElmTy->GetKind() == GetKind())
		return ElmTy->AsContainerType()->GetNestingLevel() + 1;
	return 0;
}

//===-------------------------------===//
// Pointer Type
//===-------------------------------===//

june::PointerType* june::PointerType::Create(Type* ElmTy, JuneContext& C) {
	PointerType* PT = C.GetCachedPointerType(ElmTy);
	if (PT) return PT;
	// TODO: Futher caching for newer types?
	return QuickCreate(ElmTy); // Not in cache just create a new one
}

bool june::PointerType::is(Type* T) const {
	if (T->GetKind() != TypeKind::POINTER) return false;
	return T->AsPointerType()->ElmTy->is(ElmTy);
}

std::string june::PointerType::ToStr() const {
	return ElmTy->ToStr() + "*";
}

june::PointerType* june::PointerType::QuickCreate(Type* ElmTy) {
	PointerType* PT = new PointerType;
	PT->ElmTy = ElmTy;
	return PT;
}

//===-------------------------------===//
// Fixed Array Type
//===-------------------------------===//

june::FixedArrayType* june::FixedArrayType::Create(Type* ElmTy, u32 Length, JuneContext& C) {
	// TODO: Consider caching techniques
	FixedArrayType* AT = new FixedArrayType;
	AT->ElmTy = ElmTy;
	AT->Length = Length;
	return AT;
}

u64 june::FixedArrayType::GetTotalLinearLength() const {
	if (ElmTy->GetKind() == TypeKind::FIXED_ARRAY)
		return Length * ElmTy->AsFixedArrayType()->GetTotalLinearLength();
	return Length;
}

bool june::FixedArrayType::is(Type* T) const {
	if (T->GetKind() != TypeKind::FIXED_ARRAY) return false;
	FixedArrayType* AT = T->AsFixedArrayType();
	if (Length != AT->Length) return false;
	return ElmTy->is(AT->ElmTy);
}

std::string june::FixedArrayType::ToStr() const {
	const FixedArrayType* AT = this;
	std::string S = GetBaseType()->ToStr();
	// TODO: Fix the print to not print DimSize if the expression
	// has not been calculated
	while (AT) {
		S += "[" + std::to_string(AT->Length) + "]";
		if (AT->ElmTy->GetKind() == TypeKind::FIXED_ARRAY)
			AT = AT->ElmTy->AsFixedArrayType();
		else AT = nullptr;
	}
	return S;
}

//===-------------------------------===//
// Record Type
//===-------------------------------===//

bool june::RecordType::is(Type* T) const {
	if (T->GetKind() != TypeKind::RECORD) return false;
	if (!Record) return this == T;
	return T->AsRecordType()->Record == Record;
}

std::string june::RecordType::ToStr() const {
	return Record->Name.Text.str();
}

//===-------------------------------===//
// Function Type
//===-------------------------------===//

june::FunctionType* june::FunctionType::Create(Type* RetTy, llvm::SmallVector<Type*, 4>& ParamTypes) {
	FunctionType* FuncTy = new FunctionType;
	FuncTy->RetTy = RetTy;
	FuncTy->ParamTypes = std::move(ParamTypes);
	return FuncTy;
}

bool june::FunctionType::is(Type* T) const {
	if (T->GetKind() != TypeKind::FUNCTION) return false;
	FunctionType* FT = T->AsFunctionType();
	if (RetTy->isNot(FT->RetTy)) return false;
	if (ParamTypes.size() != FT->ParamTypes.size()) return false;
	for (u32 i = 0; i < ParamTypes.size(); i++) {
		if (ParamTypes[i]->isNot(FT->ParamTypes[i])) {
			return false;
		}
	}
	return true;
}

std::string june::FunctionType::ToStr() const {
	return ArgsToStr() + " -> " + RetTy->ToStr();
}

std::string june::FunctionType::ArgsToStr() const {
	std::string s = "(";
	for (u32 i = 0; i < ParamTypes.size(); i++) {
		s += ParamTypes[i]->ToStr();
		if (i + 1 != ParamTypes.size()) {
			s += ", ";
		}
	}
	return s + ")";
}

//===-------------------------------===//
// Tuple Type
//===-------------------------------===//

june::TupleType* june::TupleType::Create(llvm::SmallVector<Type*, 4>& SubTypes) {
	TupleType* TupleTy = new TupleType;
	TupleTy->SubTypes = std::move(SubTypes);
	return TupleTy;
}

bool june::TupleType::is(Type* T) const {
	if (T->GetKind() != TypeKind::TUPLE) return false;
	TupleType* TT = T->AsTupleType();
	if (SubTypes.size() != TT->SubTypes.size()) return false;
	for (u32 i = 0; i < SubTypes.size(); i++) {
		if (SubTypes[i]->isNot(TT->SubTypes[i])) {
			return false;
		}
	}
	return true;
}

std::string june::TupleType::ToStr() const {
	std::string s = "(";
	for (u32 i = 0; i < SubTypes.size(); i++) {
		s += SubTypes[i]->ToStr();
		if (i + 1 != SubTypes.size()) {
			s += ", ";
		}
	}
	return s + ")";
}

//===-------------------------------===//
// Generic Type
//===-------------------------------===//

std::string june::GenericType::ToStr() const {
	if (BoundTy) {
		return std::string("<") + std::string(Name.Text.str()) + ">=" + BoundTy->ToStr();
	}
	return std::string(Name.Text.str());
}

void june::GenericType::Bind(Type* TyToBind) {
	assert((!TyToBind || !TyToBind->isGeneric()) && "Forgot to unbox the type before binding.");
	BoundTy = TyToBind;
}
