import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Submission.Work.LocalFields.residueMap_ker
import Submission.Work.LocalFields.residueMap_surjective
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
