import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.fracCoprimeId_relNorm
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.fracCoprimeId_spanUnit
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.mem_idealCoprimeGroupId_iff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `P(𝔪)·𝔑(𝔪) ⊆ I(𝔪)`

The first assertion of Lang's norm index inequality: the principal ray `P(𝔪) = principalRayId 𝔪` and
the norm group `𝔑(𝔪) = normRayId 𝔪` are both contained in the group `I(𝔪) = idealCoprimeGroupId 𝔪`
of fractional ideals coprime to `𝔪`.

This is the conjunction `≤`-part of the target statement `langCyclicRelIndexId`.  The two
generators are handled by `fracCoprimeId_spanUnit` (a unit congruent to `1` modulo `𝔪` is a local
unit at every `𝔭 | 𝔪`) and `fracCoprimeId_relNorm` (the relative norm of an ideal coprime to
`𝔪·𝓞 L` is coprime to `𝔪`), together with the characterisation
`mem_idealCoprimeGroupId_iff` of `I(𝔪)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField nonZeroDivisors
open NumberField IsDedekindDomain

noncomputable section

namespace Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus

open NK.CFTLib.ArtinReciprocityIdeal

/-- **`P(𝔪)·𝔑(𝔪) ⊆ I(𝔪)`.** -/
theorem conjunctOneId {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L]
    (𝔪 : Ideal (NumberField.RingOfIntegers K)) (h𝔪 : 𝔪 ≠ ⊥) :
    (NK.CFTLib.ArtinReciprocityIdeal.principalRayId 𝔪 ⊔
      NK.CFTLib.ArtinReciprocityIdeal.normRayId (K := K) (L := L) 𝔪) ≤
      NK.CFTLib.ArtinReciprocityIdeal.idealCoprimeGroupId 𝔪 := by
  rw [sup_le_iff]
  constructor
  · rw [NK.CFTLib.ArtinReciprocityIdeal.principalRayId, Subgroup.closure_le]
    rintro A ⟨a, ha, rfl⟩
    exact (mem_idealCoprimeGroupId_iff 𝔪 (NK.CFTLib.ArtinReciprocityIdeal.spanUnit a)).mpr
      (fracCoprimeId_spanUnit 𝔪 h𝔪 ha)
  · rw [NK.CFTLib.ArtinReciprocityIdeal.normRayId, Subgroup.closure_le]
    rintro A ⟨I, hI, hcop, rfl⟩
    exact (mem_idealCoprimeGroupId_iff 𝔪 _).mpr (fracCoprimeId_relNorm (K := K) (L := L) 𝔪 hI hcop)

end Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus
