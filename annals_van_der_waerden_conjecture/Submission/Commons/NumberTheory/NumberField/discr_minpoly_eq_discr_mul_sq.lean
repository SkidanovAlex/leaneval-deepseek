import Mathlib
import Submission.Commons.Polynomial.discr_map_int
import Submission.Commons.NumberTheory.NumberField.abs_discr_ge_23_of_finrank_three_of_discr_neg

open Polynomial
open scoped NumberField

namespace Commons.NumberTheory.NumberField

/-- For an algebraic integer `θ` whose minimal polynomial over `ℤ` has degree equal to `[K : ℚ]`
(so that `θ` is a primitive element of the number field `K`), the discriminant of the minimal
polynomial of `θ` differs from the field discriminant of `K` by a perfect square.

Indeed `discr (minpoly ℤ θ)` is the discriminant of the `ℤ`-basis `1, θ, …, θ^{n-1}` of `ℤ[θ]`,
and the index `[O_K : ℤ[θ]]` contributes the square factor. -/
theorem discr_minpoly_eq_discr_mul_sq {K : Type*} [Field K] [NumberField K]
    (θ : NumberField.RingOfIntegers K)
    (hdeg : (minpoly ℤ θ).natDegree = Module.finrank ℚ K) :
    ∃ m : ℤ, Polynomial.discr (minpoly ℤ θ) = (NumberField.discr K) * m ^ 2 := by
  classical
  have hint : IsIntegral ℤ θ := Algebra.IsIntegral.isIntegral θ
  -- The minimal polynomial over `ℤ` maps to the minimal polynomial over `ℚ`.
  have hmap : (minpoly ℤ θ).map (algebraMap ℤ ℚ) = minpoly ℚ (θ : K) :=
    (minpoly.isIntegrallyClosed_eq_field_fractions ℚ K hint).symm
  have hmono : (minpoly ℤ θ).Monic := minpoly.monic hint
  -- `discr` of the `ℤ`-minimal polynomial is the same as that of the `ℚ`-minimal polynomial.
  have hdiscr_map : Polynomial.discr (minpoly ℚ (θ : K)) =
      ((Polynomial.discr (minpoly ℤ θ) : ℤ) : ℚ) := by
    rw [← hmap]
    exact Commons.Polynomial.discr_map_int (minpoly ℤ θ) hmono
  -- Hence `θ` is a primitive element of `K`.
  have hdegQ : (minpoly ℚ (θ : K)).natDegree = Module.finrank ℚ K := by
    rw [← hmap]
    rw [Polynomial.natDegree_map_eq_of_injective (f := algebraMap ℤ ℚ)
      (Int.cast_injective (α := ℚ))]
    exact hdeg
  have hintQ : IsIntegral ℚ (θ : K) := Algebra.IsSeparable.isIntegral ℚ (θ : K)
  have hgen : IntermediateField.adjoin ℚ ({(θ : K)} : Set K) = ⊤ := by
    refine IntermediateField.eq_of_le_of_finrank_eq (le_top) ?_
    rw [IntermediateField.finrank_top', IntermediateField.adjoin.finrank hintQ]
    exact hdegQ
  -- Apply the field-level statement for primitive elements.
  obtain ⟨m, hm⟩ := polynomial_discr_eq_mul_field_discr_sq (K := K) (α := θ) hgen
  refine ⟨m, ?_⟩
  have hQ : ((Polynomial.discr (minpoly ℤ θ) : ℤ) : ℚ) =
      ((m ^ 2 * NumberField.discr K : ℤ) : ℚ) := by
    rw [← hdiscr_map, hm]
    push_cast
    ring
  have hInt : Polynomial.discr (minpoly ℤ θ) = m ^ 2 * NumberField.discr K :=
    Int.cast_injective hQ
  rw [hInt]
  ring

end Commons.NumberTheory.NumberField
