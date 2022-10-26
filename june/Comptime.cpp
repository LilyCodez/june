#include "Comptime.h"

#include "Types.h"
#include "Analysis.h"
#include "IRGen.h"
#include "JuneContext.h"

june::ComptimeGen::ComptimeGen(JuneContext& context)
	: Context(context) {
}

void june::ComptimeGen::Compute(ComptimeValue& CV) {

	switch (CV.P) {
	case ComptimePurpose::ARRAY_DIM_SIZE:
		ComputeArrayDimSize(CV);
		break;
	}
}

void june::ComptimeGen::ComputeArrayDimSize(ComptimeValue& CV) {

	FixedArrayType* AT = reinterpret_cast<FixedArrayType*>(CV.Payload);

	Analysis A(Context, CV.Log, true);
	A.CheckNode(AT->LengthAsExpr);

	if (CV.Log.HasError) {
		// Error already reported during analysis.
		return;
	}

	if (!AT->LengthAsExpr->IsComptimeCompat) {
		CV.Log.BeginError(AT->LengthAsExpr->Loc,
			"Array's declared length must be able to be computed at compilation time");
		CV.Log.EndError();
		return;
	}

	// TODO: Wrong LLModule. Need to pass it a module pertaining to comptime values
	IRGen Gen(Context, false, false);
	llvm::Constant* LLLength = llvm::cast<llvm::Constant>(Gen.GenNode(AT->LengthAsExpr));

	if (!AT->LengthAsExpr->Ty->isInt()) {
		CV.Log.BeginError(AT->LengthAsExpr->Loc, "Array's declared length must be an integer");
		CV.Log.EndError();
		return;
	}
	llvm::ConstantInt* LLLengthAsInt = llvm::cast<llvm::ConstantInt>(LLLength);
	if (LLLengthAsInt->isNegative()) {
		CV.Log.BeginError(AT->LengthAsExpr->Loc, "Declared length of an array cannot be negative");
		CV.Log.EndError();
		return;
	}

	AT->Length = LLLengthAsInt->getZExtValue();

	if (AT->Length == 0) {
		CV.Log.BeginError(AT->LengthAsExpr->Loc, "Declared length of an array cannot be zero");
		CV.Log.EndError();
	}
}
