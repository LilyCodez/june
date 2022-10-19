#include "JuneContext.h"

#include <llvm/IR/Module.h>
#include <llvm/IR/Intrinsics.h>
#include <llvm/IR/DIBuilder.h>

#include "Types.h"
#include "Tokens.h"
#include "TypeBinding.h"

constexpr june::HexLUT::HexLUT() : LUT() {
	LUT['0'] = true;
	LUT['1'] = true;
	LUT['2'] = true;
	LUT['3'] = true;
	LUT['4'] = true;
	LUT['5'] = true;
	LUT['6'] = true;
	LUT['7'] = true;
	LUT['8'] = true;
	LUT['9'] = true;
	LUT['a'] = true;
	LUT['b'] = true;
	LUT['c'] = true;
	LUT['d'] = true;
	LUT['e'] = true;
	LUT['f'] = true;
	LUT['A'] = true;
	LUT['B'] = true;
	LUT['C'] = true;
	LUT['D'] = true;
	LUT['E'] = true;
	LUT['F'] = true;
}

// Satisfying external linkage
june::HexLUT june::HEX_LUT;

june::JuneContext::JuneContext()
	:
	I8Type(new Type(TypeKind::I8)),
	I16Type(new Type(TypeKind::I16)),
	I32Type(new Type(TypeKind::I32)),
	I64Type(new Type(TypeKind::I64)),
	U8Type(new Type(TypeKind::U8)),
	U16Type(new Type(TypeKind::U16)),
	U32Type(new Type(TypeKind::U32)),
	U64Type(new Type(TypeKind::U64)),
	C8Type(new Type(TypeKind::C8)),
	C16Type(new Type(TypeKind::C16)),
	C32Type(new Type(TypeKind::C32)),
	F32Type(new Type(TypeKind::F32)),
	F64Type(new Type(TypeKind::F64)),
	VoidType(new Type(TypeKind::VOID)),
	ErrorType(new Type(TypeKind::ERROR)),
	BoolType(new Type(TypeKind::BOOL)),
	NullType(new Type(TypeKind::NULLPTR)),
	UndefinedType(new Type(TypeKind::UNDEFINED)),

	LLContext(*new llvm::LLVMContext),
	LLJuneModule(*new llvm::Module("June Module", LLContext)),

	BinaryOpsPrecedence({
		{ '*', 9 },
		{ '/', 9 },
		{ '%', 9 },

		{ '+', 8 },
		{ '-', 8 },

		{ TokenKind::LT_LT, 7 }, // <<
		{ TokenKind::GT_GT, 7 }, // >>
		
		{ '<'      , 6 },
		{ '>'      , 6 },
		{ TokenKind::LT_EQ, 6 }, // <=
		{ TokenKind::GT_EQ, 6 }, // >=

		{ TokenKind::EQ_EQ , 5 }, // ==
		{ TokenKind::EXL_EQ, 5 }, // !=

		{ '&', 4 },

		{ '^', 3 },

		{ '|', 2 },

		{ TokenKind::AMP_AMP, 1 }, // &&
		{ TokenKind::BAR_BAR, 1 }, // ||
		
		}),

	MainIdentifier(Identifier("main")),
	LengthIdentifier(Identifier("length")),

	LLVMIntrinsicsTable({
		{ Identifier("memcpy"), llvm::Intrinsic::IndependentIntrinsics::memcpy },
		{ Identifier("sin"), llvm::Intrinsic::IndependentIntrinsics::sin       },
		{ Identifier("cos"), llvm::Intrinsic::IndependentIntrinsics::cos       },
		}),

	TokenKeywordMap(*new llvm::DenseMap<llvm::StringRef, u16>
		(__TK_KEYWORD_END__ - __TK_KEYWORD_START__)),
	TokenKwKindToStringMap(*new llvm::DenseMap<u16, llvm::StringRef >
		(__TK_KEYWORD_END__ - __TK_KEYWORD_START__))
{
}

june::JuneContext::~JuneContext() {
	delete I8Type;
	delete I16Type;
	delete I32Type;
	delete I64Type;
	delete U8Type;
	delete U16Type;
	delete U32Type;
	delete U64Type;
	delete C8Type;
	delete C16Type;
	delete C32Type;
	delete F32Type;
	delete F64Type;
	delete VoidType;
	delete ErrorType;
	delete BoolType;
	delete NullType;
	delete UndefinedType;
	delete &LLJuneModule;
	delete &LLContext;
}

void june::JuneContext::Init(bool EmitDebugInfo) {
	
	TokenKeywordMap.insert({ "i8"    , TokenKind::KW_TYPE_I8     });
	TokenKeywordMap.insert({ "i16"   , TokenKind::KW_TYPE_I16    });
	TokenKeywordMap.insert({ "i32"   , TokenKind::KW_TYPE_I32    });
	TokenKeywordMap.insert({ "i64"   , TokenKind::KW_TYPE_I64    });
	TokenKeywordMap.insert({ "u8"    , TokenKind::KW_TYPE_U8     });
	TokenKeywordMap.insert({ "u16"   , TokenKind::KW_TYPE_U16    });
	TokenKeywordMap.insert({ "u32"   , TokenKind::KW_TYPE_U32    });
	TokenKeywordMap.insert({ "u64"   , TokenKind::KW_TYPE_U64    });
	TokenKeywordMap.insert({ "osint" , TokenKind::KW_TYPE_OSINT  });
	TokenKeywordMap.insert({ "osuint", TokenKind::KW_TYPE_OSUINT });
	TokenKeywordMap.insert({ "c8"    , TokenKind::KW_TYPE_C8     });
	TokenKeywordMap.insert({ "c16"   , TokenKind::KW_TYPE_C16    });
	TokenKeywordMap.insert({ "c32"   , TokenKind::KW_TYPE_C32    });
	TokenKeywordMap.insert({ "f32"   , TokenKind::KW_TYPE_F32    });
	TokenKeywordMap.insert({ "f64"   , TokenKind::KW_TYPE_F64    });
	TokenKeywordMap.insert({ "bool"  , TokenKind::KW_TYPE_BOOL   });
	TokenKeywordMap.insert({ "void"  , TokenKind::KW_TYPE_VOID   });

	TokenKeywordMap.insert({ "in"      , TokenKind::KW_IN        });
	TokenKeywordMap.insert({ "this"    , TokenKind::KW_THIS      });
	TokenKeywordMap.insert({ "new"     , TokenKind::KW_NEW       });
	TokenKeywordMap.insert({ "cast"    , TokenKind::KW_CAST      });
	TokenKeywordMap.insert({ "if"      , TokenKind::KW_IF        });
	TokenKeywordMap.insert({ "else"    , TokenKind::KW_ELSE      });
	TokenKeywordMap.insert({ "continue", TokenKind::KW_CONTINUE  });
	TokenKeywordMap.insert({ "break"   , TokenKind::KW_BREAK     });
	TokenKeywordMap.insert({ "import"  , TokenKind::KW_IMPORT    });
	TokenKeywordMap.insert({ "sizeof"  , TokenKind::KW_SIZEOF    });
	TokenKeywordMap.insert({ "true"    , TokenKind::KW_TRUE      });
	TokenKeywordMap.insert({ "false"   , TokenKind::KW_FALSE     });
	TokenKeywordMap.insert({ "record"  , TokenKind::KW_RECORD    });
	TokenKeywordMap.insert({ "null"    , TokenKind::KW_NULL      });
	TokenKeywordMap.insert({ "comptime", TokenKind::KW_COMPTIME  });
	TokenKeywordMap.insert({ "native"  , TokenKind::KW_NATIVE    });
	TokenKeywordMap.insert({ "return"  , TokenKind::KW_RETURN    });
	TokenKeywordMap.insert({ "loop"    , TokenKind::KW_LOOP      });

	for (const auto& pair : TokenKeywordMap) {
		TokenKwKindToStringMap.insert({ pair.second, pair.first });
	}

	auto CreatePointersForCache = [&](Type* BaseTy) {
		Type* ItrElmTy = BaseTy;
		for (u32 i = 0; i <= 3; i++) {
			PointerType* PtrTy = new PointerType;
			PtrTy->ElmTy = ItrElmTy;
			StandardPointerCache.insert({ ItrElmTy, PtrTy });
			ItrElmTy = PtrTy;
		}
	};
	CreatePointersForCache(I8Type);
	CreatePointersForCache(I16Type);
	CreatePointersForCache(I32Type);
	CreatePointersForCache(I64Type);
	CreatePointersForCache(U8Type);
	CreatePointersForCache(U16Type);
	CreatePointersForCache(U32Type);
	CreatePointersForCache(U64Type);
	CreatePointersForCache(F32Type);
	CreatePointersForCache(F64Type);
	CreatePointersForCache(VoidType);

	VoidPtrType = StandardPointerCache[VoidType];

	if (EmitDebugInfo) {
		llvm::DIBuilder DBuilder = llvm::DIBuilder(LLJuneModule);
		DITyI8   = DBuilder.createBasicType("i8" , 8 , llvm::dwarf::DW_ATE_signed);
		DITyI16  = DBuilder.createBasicType("i16", 16, llvm::dwarf::DW_ATE_signed);
		DITyI32  = DBuilder.createBasicType("i32", 32, llvm::dwarf::DW_ATE_signed);
		DITyI64  = DBuilder.createBasicType("i64", 64, llvm::dwarf::DW_ATE_signed);
		DITyU8   = DBuilder.createBasicType("u8" , 8 , llvm::dwarf::DW_ATE_unsigned);
		DITyU16  = DBuilder.createBasicType("u16", 16, llvm::dwarf::DW_ATE_unsigned);
		DITyU32  = DBuilder.createBasicType("u32", 32, llvm::dwarf::DW_ATE_unsigned);
		DITyU64  = DBuilder.createBasicType("u64", 64, llvm::dwarf::DW_ATE_unsigned);
		DITyC8   = DBuilder.createBasicType("c8", 8, llvm::dwarf::DW_ATE_signed_char);
		DITyC16  = DBuilder.createBasicType("c16", 16, llvm::dwarf::DW_ATE_signed);
		DITyC32  = DBuilder.createBasicType("c32", 32, llvm::dwarf::DW_ATE_signed);
		DITyBool = DBuilder.createBasicType("bool", 8, llvm::dwarf::DW_ATE_boolean);
		DITyF32  = DBuilder.createBasicType("f32" , 32, llvm::dwarf::DW_ATE_float);
		DITyF64  = DBuilder.createBasicType("f64" , 64, llvm::dwarf::DW_ATE_float);
	}
}

u16 june::JuneContext::GetKeywordKind(llvm::StringRef Text) const {
	auto it = TokenKeywordMap.find(Text);
	if (it != TokenKeywordMap.end()) {
		return it->second;
	}
	return 0;
}

llvm::StringRef june::JuneContext::GetKwAsString(u32 TokenKind) const {
	return TokenKwKindToStringMap[TokenKind];
}

void june::JuneContext::RequestGen(Decl* D) {
	if (D->GenRequestedAlready) return;
	QuededDeclsToGen.push(DeclGen{ {}, D});
	D->GenRequestedAlready = true;
}

u32 june::JuneContext::RequestGen(TypeBindList& Bindings, GenericFuncDecl* GenFunc) {
	u32 BindingId = GetBindingsId(GenFunc, Bindings);
	if (BindingId == INVALID_BINDING_ID) {
		BindingId = (u32)GenFunc->BindingCache.size();
		GenFunc->BindingCache.push_back(std::make_tuple(std::move(Bindings), nullptr));
		QuededDeclsToGen.push(DeclGen{ BindingId, GenFunc });
	}
	return BindingId;
}

june::PointerType* june::JuneContext::GetCachedPointerType(Type* ElmTy) const {
	auto it = StandardPointerCache.find(ElmTy);
	if (it != StandardPointerCache.end()) {
		return it->second;
	}
	return nullptr;
}

void june::JuneContext::RequestComptimeGen(ComptimeValue CV) {
	ComptimeValues.push(CV);
}
