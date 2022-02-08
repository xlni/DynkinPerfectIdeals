newPackage(
    "DynkinPerfectIdeals",
    Version => "1.0",
    Date => "January 24, 2022",
    Authors => {
	{Name => "Xianglong Ni",
	    Email => "xlni@berkeley.edu",
	    HomePage => "https://math.berkeley.edu/~xlni/"
	    }
	},
    Headline => "(conjecturally) generic examples of perfect resolutions",
    AuxiliaryFiles => true,
    DebuggingMode => false
    )

export {
    "LieAlgebraCache",
    "fillBracket",
    "Jacobi",
    "name",
    "newRep",
    "Ltog",
    "L0tog",
    "LieAlgebraRep",
    "newLieAlgebra",
    "LieAlgebra",
    "lieAlgebra",
    "action",
    "actionHT",
    "checkRep",
    "generate",
    "subRep",
    "quotientRep",
    "alg",
    "gl",
    "igl",
    "tr",
    "wedgeDiag",
    "isl",
    "sl",
    "psl",
    "completeIrrepAction",
    "extendMap",
    "trivialRep",
    "invariants",
    "equivariantMaps",
    "glLie",
    "soLie",
    "slLie",
    "glStandard",
    "schurRep",
    "adjointRep",
    "tensorRep",
    "dualRep",
    "bracket",
    "repFromGradedAction",
    "completeGradedAction",
    "parametricAction",
    "adj",
    "extremalRep",
    "genericBigrade",
    "genericMultigrade",
    "topComplex",
    "genericGorIndexing",
    "lengthThreeVars",
    "subAlgebra",
    "safeInc",
    "algebra",
    "Sign",
    "defectLieAlgebraDual",
    "formatLookup",
    "mapInfo"
    }

needsPackage "SchurFunctors"

------------------------------------------------
-- Cache for storing Lie algebra computations --
------------------------------------------------

LieAlgebraCache = new MutableHashTable;

---------------------
-- Auxiliary files --
---------------------

--wedgeDiag, working with reps, etc.
load "./DynkinPerfectIdeals/BasicMethods.m2"

--initializing Lie algebra data
load "./DynkinPerfectIdeals/LieAlgebras.m2"

--actually constructing the resolutions
load "./DynkinPerfectIdeals/GenericResolutions.m2"

end
