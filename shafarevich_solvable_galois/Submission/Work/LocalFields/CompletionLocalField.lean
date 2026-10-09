/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The completion of a number field is a local field

Combining the two facts about the reduction map `𝓞 K → κ_v` (`residueMap_surjective` and
`residueMap_ker`) we obtain the canonical isomorphism `𝓞 K ⧸ v ≃+* κ_v`, finiteness of the
residue field `κ_v`, and hence that the `v`-adic completion `K_v` is a non-archimedean local
field in the sense of `Work.LocalFields.IsLocalField`.

## Main results

* `Work.LocalFields.residueEquiv` : `𝓞 K ⧸ v ≃+* κ_v`.
* `Work.LocalFields.Finite_residueFieldOf` : `κ_v` is finite.
* `Work.LocalFields.instIsLocalFieldCompletion` : `IsLocalField K_v`.
* `Work.LocalFields.natCard_residueFieldOf` : `#κ_v = N(v)`.
-/
import Submission.Work.LocalFields.Residue
import Submission.Work.LocalFields.residueMap_surjective
import Submission.Work.LocalFields.residueMap_ker
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.LocalFields

open scoped NumberField Valued WithZero

variable {K : Type*} [Field K] [NumberField K] (v : FinitePrime K)

/-- The canonical isomorphism `𝓞 K ⧸ v ≃+* κ_v` between the residue field of the number field
`K` at the finite prime `v` and the residue field of the completion `K_v`. -/
noncomputable def residueEquiv : (𝓞 K ⧸ v.asIdeal) ≃+* residueFieldOf K v :=
  (Ideal.quotEquivOfEq (residueMap_ker v)).symm.trans
    (RingHom.quotientKerEquivOfSurjective (residueMap_surjective v))

/-- The residue field `κ_v` of the completion of a number field at a finite prime is finite:
it is a quotient of the finite ring `𝓞 K ⧸ v`. -/
instance Finite_residueFieldOf : Finite (residueFieldOf K v) :=
  Finite.of_injective (residueEquiv v).symm (residueEquiv v).symm.injective

noncomputable instance : Fintype (residueFieldOf K v) := Fintype.ofFinite _

/-- The number of elements of the residue field `κ_v` is the norm `N(v)` of the prime. -/
theorem natCard_residueFieldOf : Nat.card (residueFieldOf K v) = residueCard K v := by
  rw [← Nat.card_congr (residueEquiv v).toEquiv]
  rfl

/-- The completion of a number field at a finite prime is a non-archimedean local field. -/
instance instIsLocalFieldCompletion : IsLocalField (Completion K v) where
  rankOne := ⟨inferInstance⟩
  complete := inferInstance
  compactInteger := by
    haveI : IsDiscreteValuationRing 𝒪[Completion K v] :=
      inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers K))
    exact (Valued.integer.properSpace_iff_compactSpace_integer (K := Completion K v)
      (Γ₀ := ℤᵐ⁰)).mp
      ((Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
        (K := Completion K v) (Γ₀ := ℤᵐ⁰)).mpr ⟨inferInstance, inferInstance, inferInstance⟩)

end Work.LocalFields
