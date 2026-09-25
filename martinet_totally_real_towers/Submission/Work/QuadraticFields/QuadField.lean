import Mathlib
import Submission.Commons.FieldTheory.Adjoin.finrank_adjoin_sq_eq_two_pow
import Submission.Commons.FieldTheory.Galois.isGalois_of_finrank_eq_two
import Submission.Commons.NumberTheory.NumberField.discr_dvd_of_isIntegral_basis

/-!
# Quadratic and multiquadratic fields inside `AlgebraicClosure ℚ`

This file sets up the concrete objects of the quadratic-field chapter: the quadratic field
`ℚ(√a)` for a rational number `a`, the multiquadratic field `ℚ(√a : a ∈ s)` for a finite set
`s` of rational numbers, and their basic properties (real/complex nature, degree, normality,
Galoisness).

Everything is built inside a fixed algebraic closure `Ω = AlgebraicClosure ℚ`, so that all the
fields occurring in the subsequent genus-theory arguments are comparable subfields of one field.

## Main definitions

* `Work.QuadraticFields.sqrtVal`: a chosen square root of `a : ℚ` in `AlgebraicClosure ℚ`.
* `Work.QuadraticFields.quadField`: the quadratic field `ℚ(√a)`.
* `Work.QuadraticFields.multiQuad`: the multiquadratic field `ℚ(√a : a ∈ s)`.

## Main results

* `sqrtVal_sq`, `eq_or_eq_neg_sqrtVal`, `quadField_le_multiQuad`, `prod_sqrtVal_mem`,
  `quadField_prod_le_multiQuad`, `multiQuad_finrank`, `multiQuad_isGalois`, `quadField_finrank`,
  `quadField_isGalois`.
-/

namespace Work.QuadraticFields

set_option autoImplicit false

open Polynomial

open scoped _root_.NumberField

noncomputable section

/-- A chosen square root of `a : ℚ` in the algebraic closure of `ℚ`. -/
def sqrtVal (a : ℚ) : AlgebraicClosure ℚ :=
  Classical.choose (IsAlgClosed.exists_root
    (X ^ 2 - C (algebraMap ℚ (AlgebraicClosure ℚ) a) : (AlgebraicClosure ℚ)[X])
    (by rw [Polynomial.degree_X_pow_sub_C (by norm_num : (0 : ℕ) < 2)]; norm_num))

theorem sqrtVal_sq (a : ℚ) :
    sqrtVal a ^ 2 = algebraMap ℚ (AlgebraicClosure ℚ) a := by
  have h := Classical.choose_spec (IsAlgClosed.exists_root
    (X ^ 2 - C (algebraMap ℚ (AlgebraicClosure ℚ) a) : (AlgebraicClosure ℚ)[X])
    (by rw [Polynomial.degree_X_pow_sub_C (by norm_num : (0 : ℕ) < 2)]; norm_num))
  simpa only [sqrtVal, Polynomial.IsRoot, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] using h

theorem sqrtVal_ne_zero {a : ℚ} (ha : a ≠ 0) : sqrtVal a ≠ 0 := by
  intro h
  have h2 := sqrtVal_sq a
  rw [h, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at h2
  have h3 : algebraMap ℚ (AlgebraicClosure ℚ) a = algebraMap ℚ (AlgebraicClosure ℚ) 0 := by
    rw [map_zero]; exact h2.symm
  exact ha ((algebraMap ℚ (AlgebraicClosure ℚ)).injective h3)

/-- The two square roots of `a` are the chosen one and its negative. -/
theorem eq_or_eq_neg_sqrtVal {a : ℚ} {y : AlgebraicClosure ℚ}
    (hy : y ^ 2 = algebraMap ℚ (AlgebraicClosure ℚ) a) :
    y = sqrtVal a ∨ y = -sqrtVal a := by
  have h := sqrtVal_sq a
  have hmul : (y - sqrtVal a) * (y + sqrtVal a) = 0 := by
    have : y ^ 2 - (sqrtVal a) ^ 2 = 0 := by rw [hy, h, sub_self]
    linear_combination this
  rcases mul_eq_zero.mp hmul with h1 | h2
  · left; linear_combination h1
  · right; linear_combination h2

/-- The quadratic field `ℚ(√a)`. -/
def quadField (a : ℚ) : IntermediateField ℚ (AlgebraicClosure ℚ) :=
  IntermediateField.adjoin ℚ ({sqrtVal a} : Set (AlgebraicClosure ℚ))

/-- The multiquadratic field `ℚ(√a : a ∈ s)`. -/
def multiQuad (s : Finset ℚ) : IntermediateField ℚ (AlgebraicClosure ℚ) :=
  IntermediateField.adjoin ℚ (sqrtVal '' (s : Set ℚ))

theorem sqrtVal_mem_quadField (a : ℚ) :
    sqrtVal a ∈ (quadField a : Set (AlgebraicClosure ℚ)) :=
  IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton (sqrtVal a))

theorem sqrtVal_mem_multiQuad {s : Finset ℚ} {a : ℚ} (ha : a ∈ s) :
    sqrtVal a ∈ (multiQuad s : Set (AlgebraicClosure ℚ)) :=
  IntermediateField.subset_adjoin ℚ _ (Set.mem_image_of_mem _ ha)

theorem multiQuad_mono {s t : Finset ℚ} (h : s ⊆ t) : multiQuad s ≤ multiQuad t := by
  rw [multiQuad, IntermediateField.adjoin_le_iff]
  rintro y ⟨a, ha, rfl⟩
  exact sqrtVal_mem_multiQuad (h ha)

theorem quadField_le_multiQuad {s : Finset ℚ} {a : ℚ} (ha : a ∈ s) :
    quadField a ≤ multiQuad s := by
  rw [quadField, IntermediateField.adjoin_le_iff]
  rintro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  exact sqrtVal_mem_multiQuad ha

/-- The product of the chosen square roots is a square root of the product. -/
theorem prod_sqrtVal_sq (s : Finset ℚ) :
    (∏ a ∈ s, sqrtVal a) ^ 2
      = algebraMap ℚ (AlgebraicClosure ℚ) (∏ a ∈ s, a) := by
  rw [← Finset.prod_pow]
  rw [Finset.prod_congr rfl (fun a _ => sqrtVal_sq a), map_prod]

theorem prod_sqrtVal_mem_multiQuad (s : Finset ℚ) :
    (∏ a ∈ s, sqrtVal a) ∈ (multiQuad s : Set (AlgebraicClosure ℚ)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [multiQuad]
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact mul_mem (sqrtVal_mem_multiQuad (Finset.mem_insert_self a s))
        (multiQuad_mono (Finset.subset_insert a s) ih)

theorem prod_sqrtVal_eq_or_neg (s : Finset ℚ) :
    (∏ a ∈ s, sqrtVal a) = sqrtVal (∏ a ∈ s, a) ∨
      (∏ a ∈ s, sqrtVal a) = -sqrtVal (∏ a ∈ s, a) :=
  eq_or_eq_neg_sqrtVal (prod_sqrtVal_sq s)

/-- The quadratic field of the product of the entries is contained in the multiquadratic field. -/
theorem quadField_prod_le_multiQuad (s : Finset ℚ) :
    quadField (∏ a ∈ s, a) ≤ multiQuad s := by
  rw [quadField, IntermediateField.adjoin_le_iff]
  rintro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  rcases prod_sqrtVal_eq_or_neg s with h | h
  · rw [← h]; exact prod_sqrtVal_mem_multiQuad s
  · have h' := prod_sqrtVal_mem_multiQuad s
    rw [h] at h'
    simpa using neg_mem h'

theorem quadField_finiteDimensional (a : ℚ) : FiniteDimensional ℚ ↥(quadField a) := by
  refine IntermediateField.finiteDimensional_adjoin ?_
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  apply IsIntegral.of_pow (R := ℚ) (B := AlgebraicClosure ℚ) (n := 2) (by norm_num)
  rw [sqrtVal_sq]
  exact isIntegral_algebraMap

theorem multiQuad_finiteDimensional (s : Finset ℚ) : FiniteDimensional ℚ ↥(multiQuad s) := by
  have hfin : (sqrtVal '' (s : Set ℚ) : Set (AlgebraicClosure ℚ)).Finite :=
    s.finite_toSet.image _
  refine IntermediateField.finiteDimensional_adjoin ?_
  rintro x ⟨a, _, rfl⟩
  apply IsIntegral.of_pow (R := ℚ) (B := AlgebraicClosure ℚ) (n := 2) (by norm_num)
  rw [sqrtVal_sq]
  exact isIntegral_algebraMap

instance quadField_numberField (a : ℚ) : NumberField ↥(quadField a) := by
  haveI := quadField_finiteDimensional a
  exact NumberField.of_module_finite ℚ ↥(quadField a)

instance multiQuad_numberField (s : Finset ℚ) : NumberField ↥(multiQuad s) := by
  haveI := multiQuad_finiteDimensional s
  exact NumberField.of_module_finite ℚ ↥(multiQuad s)

end

end Work.QuadraticFields
