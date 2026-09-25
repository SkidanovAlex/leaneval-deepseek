import Mathlib
import Submission.NK.CFTLib.pRank

/-!
# The vocabulary of the Roquette rank bound

`NK.CFTLib.finrank_normQuotient_le` bounds the `𝔽_p`-dimension of
`𝔽_p ⊗[ℤ] normQuotient F K`, where

`normQuotient F K = (Fˣ ∩ N_{K/F} 𝕀 K) / N_{K/F} Kˣ`.

This file collects the subgroups used in the splitting of that quotient into a "unit part" and a
"class-group part", together with the notation for the `𝔽_p`-dimension.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct IsMulCommutative
open NumberField IsDedekindDomain
open CategoryTheory

noncomputable section

namespace NK.CFTLib

open NK.GlobalCFT

variable (F K : Type*) [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]

/-- The units of `𝓞 F`, as a subgroup of `Fˣ`. -/
noncomputable def unitsInF : Subgroup Fˣ :=
  (Units.map (algebraMap (𝓞 F) F).toMonoidHom).range

/-- The subgroup `N_{K/F} Kˣ · (Fˣ ∩ 𝓞_Fˣ ∩ N_{K/F} 𝕀 K)` of `Fˣ`: the "unit part" of
`normPrincipalPreimage F K`. -/
noncomputable def normUnitPreimage [FiniteDimensional F K] : Subgroup Fˣ :=
  unitsNormSubgroup F K ⊔ (unitsInF F ⊓ normPrincipalPreimage F K)

/-- The image of the unit part `normUnitPreimage F K` in the quotient `normQuotient F K`. -/
noncomputable def normQuotientUnitImage [FiniteDimensional F K] :
    AddSubgroup (normQuotient F K) :=
  (((normUnitPreimage F K).subgroupOf (normPrincipalPreimage F K))).toAddSubgroup.map
    (QuotientAddGroup.mk' ((unitsNormSubgroup F K).subgroupOf
      (normPrincipalPreimage F K)).toAddSubgroup)

/-- The image of the unit part is normal in `normQuotient F K`, being a subgroup of a commutative
group. -/
instance normQuotientUnitImage_normal [FiniteDimensional F K] :
    (normQuotientUnitImage F K).Normal :=
  AddSubgroup.Normal.mk fun n hn g => by
    have h : g + n + -g = n := by rw [add_comm g n, add_assoc, add_neg_cancel, add_zero]
    rw [h]
    exact hn

/-- The "class-group part" `normQuotient F K ⧸ normQuotientUnitImage F K`, realised as the range
of the quotient map (a subtype of `normQuotient F K`, hence an additive commutative group). -/
noncomputable def normQuotientClPart [FiniteDimensional F K] : Type _ :=
  (QuotientAddGroup.mk' (normQuotientUnitImage F K)).range

end NK.CFTLib
