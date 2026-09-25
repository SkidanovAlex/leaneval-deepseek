import Mathlib
import Submission.NK.Chebotarev.Basic

namespace NK.Reconstruct

open NumberField

/-- **The commutation of two Galois automorphisms on rings of integers, from commutation on the
fields.**  Let `L ⊆ N ⊆ M` be number fields with `ρ ∈ Gal(M/L)` and `τ ∈ Gal(N/L)`.  If `ρ` and
`τ` agree on `N` (i.e. `ρ (algebraMap N M x) = algebraMap N M (τ x)` for all `x : N`), then their
actions on the rings of integers commute with the canonical map `𝓞 N → 𝓞 M`:
`galRestrict ρ (i y) = i (galRestrict τ y)` for all `y ∈ 𝓞 N`. -/
theorem galRestrict_commutes_of_field_commutes
    {L N M : Type*} [Field L] [NumberField L] [Field N] [NumberField N] [Field M] [NumberField M]
    [Algebra L N] [Algebra L M] [Algebra N M] [IsScalarTower L N M]
    [FiniteDimensional L N] [FiniteDimensional L M] [FiniteDimensional N M]
    {ρ : Gal(M/L)} {τ : Gal(N/L)}
    (hfield : ∀ x : N, ρ (algebraMap N M x) = algebraMap N M (τ x)) :
    ∀ y : NumberField.RingOfIntegers N,
      galRestrict (NumberField.RingOfIntegers L) L M (NumberField.RingOfIntegers M) ρ
          (algebraMap (NumberField.RingOfIntegers N) (NumberField.RingOfIntegers M) y)
        = algebraMap (NumberField.RingOfIntegers N) (NumberField.RingOfIntegers M)
            (galRestrict (NumberField.RingOfIntegers L) L N (NumberField.RingOfIntegers N) τ y) := by
  intro y
  apply_fun (algebraMap (NumberField.RingOfIntegers M) M)
  · rw [algebraMap_galRestrict_apply (A := NumberField.RingOfIntegers L)
        (B := NumberField.RingOfIntegers M) ρ]
    rw [← IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers N)
        (NumberField.RingOfIntegers M) M]
    rw [← IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers N)
        (NumberField.RingOfIntegers M) M]
    rw [IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers N) N M]
    rw [IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers N) N M]
    rw [algebraMap_galRestrict_apply (A := NumberField.RingOfIntegers L)
        (B := NumberField.RingOfIntegers N) τ]
    exact hfield _
  · exact IsIntegralClosure.algebraMap_injective (NumberField.RingOfIntegers M) ℤ M

end NK.Reconstruct
