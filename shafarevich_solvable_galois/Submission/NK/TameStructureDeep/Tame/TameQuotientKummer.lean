/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `TameQuotientKummer` at every place, unconditionally

The first named classical input of the local-structure residual,
`NK.TameStructureDeep.TameQuotientKummer p q κ K'` (`Residual.lean`), is the pair

* `isTameInertia` — NSW (7.5.7) Corollary, Iwasawa: `I_κ/V_κ` is the maximal closed normal
  pro-cyclic subgroup of `G_κ^{tr}`, and
* `frobenius_iff` — NSW (12.1.8) Lemma, Iwasawa: a normalised Frobenius is exactly a tame
  Frobenius lift.

Both are **theorems** of this chapter at every place (`p = ringChar` of the residue field,
`q = residueCard K 𝔭`), so `TameQuotientKummer` needs no hypothesis.  With this, the reduced
residual of the chapter has exactly one unproved field, `abelianisation` (Shimizu's lemma, i.e.
local class field theory); see `NK.TameStructureDeep.Tame.tameQuotientKummer_adicCompletion_residueChar`.
-/
import Mathlib
import Submission.NK.TameStructureDeep.Tame.tameInertiaInput_adicCompletion_residueChar
import Submission.NK.TameStructureDeep.Tame.wildInertiaSubgroup_eq_correctedWildInertia
import Submission.NK.TameStructureDeep.Tame.CorrectedResidual
import Submission.NK.TameStructureDeep.Residual
import Submission.NK.LocalTame.All
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical

namespace NK.TameStructureDeep.Tame

noncomputable section

variable {K : Type*} [Field K] [NumberField K]
variable (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {K' : Type*}
  [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K']

/-- **`TameQuotientKummer` at every place, unconditionally** (`p = ringChar` of the residue field,
`q = residueCard K 𝔭`): the structure of the tame quotient — `I_κ/V_κ` maximal closed normal
pro-cyclic in `G_κ^{tr}` — together with the Frobenius normalisation NSW (12.1.8) in both
directions. -/
theorem tameQuotientKummer_adicCompletion_residueChar :
    NK.TameStructureDeep.TameQuotientKummer (resCharAt 𝔭)
      (NK.LocalStructure.residueCard K 𝔭) (𝔭.adicCompletion K) K' := by
  obtain ⟨π, hπ⟩ := exists_isUniformizerAt 𝔭
  have hTI := tameInertiaInput_adicCompletion_residueChar (K := K) (K' := K') 𝔭
  refine ⟨hTI.hp, hTI.isTameInertia, fun x => ?_⟩
  have heq : NK.LocalTame.wildInertiaSubgroup (κ := 𝔭.adicCompletion K) (K' := K')
      (resCharAt 𝔭) =
      correctedWildInertia (κ := 𝔭.adicCompletion K) (K' := K') (resCharAt 𝔭)
        (π : 𝔭.adicCompletion K) := wildInertiaSubgroup_eq_correctedWildInertia 𝔭 hπ
  rw [heq]
  exact isFrobeniusFor_iff_isTameFrobeniusLift 𝔭 hπ

/-- **The reduced residual, from Shimizu's lemma alone.**  Since `TameQuotientKummer` is a theorem
at every place (`Tame.tameQuotientKummer_adicCompletion_residueChar`), the four-field residual
`NK.TameStructureDeep.TameRamificationResidual` needs only its `abelianisation` field: the
statement `G_κ^{tr,ab} ≅ Ẑ × μ_{q-1}` of Shimizu, arXiv:2009.10431, Lemma 2.1 (local class field
theory).  Consequently everything the chapter's boundary theorems
(`localStructureData_of_residual`, `localStructureData_of`) ask for beyond local CFT is proved. -/
theorem tameRamificationResidual_of_abelianisation
    (hAb : Nonempty
      (NK.LocalTame.tameAbelianization (κ := 𝔭.adicCompletion K) (K' := K') (resCharAt 𝔭) ≃*
        (NK.LocalAnabelian.Zhat ×
          Multiplicative (ZMod (NK.LocalStructure.residueCard K 𝔭 - 1))))) :
    NK.TameStructureDeep.TameRamificationResidual (resCharAt 𝔭)
      (NK.LocalStructure.residueCard K 𝔭) (𝔭.adicCompletion K) K' :=
  let h := tameQuotientKummer_adicCompletion_residueChar (K := K) (K' := K') 𝔭
  ⟨h.hp, h.isTameInertia, h.frobenius_iff, hAb⟩

end

end NK.TameStructureDeep.Tame
