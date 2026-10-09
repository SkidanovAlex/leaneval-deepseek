import Mathlib
import Submission.Work.SSGRoute.ZDataTwo.Mu2LocalNormXor
import Submission.Work.SSGRoute.ZDataTwo.exists_level_localNormSubgroup_eq
import Submission.Work.SSGRoute.ZDataTwo.isLocalNorm_mul_of_localPowClass_eq_one
import Submission.Work.SSGRoute.ZDataTwo.Mu2InvolutionForm
import Submission.Work.HilbertSymbolGeneral.hilbertReciprocityTwo
import Submission.Work.HilbertSymbolGeneral.localNorm_forall
import Submission.Work.HilbertSymbolGeneral.canonicalAPI
import Submission.Work.HilbertSymbolGeneral.quadLevel_finrank_eq_two_of_notMem
import Submission.Work.SSGRoute.grunwald_surjective_two
import Submission.Work.SSGRoute.exists_kummerChar_of_additive_locConst
import Submission.NK.NUV2.ARL.HR.CyclotomicTransferAux
import Submission.NK.UchidaKummer.Approximation.isKummerSurjective_of_weakApproximation
import Submission.Work.LocalFields.card_decompositionGroup
import Submission.Work.LocalFields.finrank_completion_eq_card_decompositionGroup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The arithmetic dependencies of the `μ₂` local Tate system with archimedean terms

This module only re-exports (by import) the modules in which the arithmetic vocabulary consumed by
`Submission/Work/SSGRoute/ZDataTwo/mu2LocalTateSystemWithArch.lean` lives: the local class field
theory of a completion (`ArtinReciprocity`, the norm index theorem), the Grünwald/Kummer
surjectivity, the global product formula (`HilbertReciprocityTwo`) and the elementary
local-norm bridges already proved in this directory.  It exists so that delegated statements can
declare their `depends_on` entirely inside `Submission/Work`.
-/
