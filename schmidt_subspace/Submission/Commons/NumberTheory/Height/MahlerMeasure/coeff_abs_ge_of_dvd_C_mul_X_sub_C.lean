import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Normed.Ring.Lemmas

namespace Commons.NumberTheory.Height.MahlerMeasure

open Polynomial

/-- Let `a b : ℤ` with `b > 0`, `a ≠ 0`, and let `B ∈ ℤ[X]` be nonzero and divisible by
`(b·X - a)^l`. Then `B` has a coefficient of absolute value at least `(max |a| b)^l`. -/
theorem coeff_abs_ge_of_dvd_C_mul_X_sub_C (a : ℤ) (b : ℕ) (hb : 0 < b) (ha : a ≠ 0)
    (l : ℕ) {B : Polynomial ℤ} (hB : B ≠ 0)
    (hdvd : (Polynomial.C (b : ℤ) * Polynomial.X - Polynomial.C a) ^ l ∣ B) :
    ∃ k : ℕ, k ≤ B.natDegree ∧ (max a.natAbs b) ^ l ≤ (B.coeff k).natAbs := by
  -- Write the linear factor as `A = b·X - a`.  Its constant coefficient is `-a ≠ 0`
  -- and its leading coefficient is `b ≠ 0`, so the same is true of `A ^ l`.
  set A : Polynomial ℤ := Polynomial.C (b : ℤ) * Polynomial.X - Polynomial.C a with hAdef
  obtain ⟨Q, hQ⟩ := hdvd
  have hQne : Q ≠ 0 := by rintro rfl; exact hB (by rw [hQ, mul_zero])
  have hA0 : A.coeff 0 = -a := by
    rw [hAdef, Polynomial.coeff_sub, Polynomial.coeff_C_mul_X, Polynomial.coeff_C]
    norm_num
  have hA1 : A.coeff 1 = (b : ℤ) := by
    rw [hAdef, Polynomial.coeff_sub, Polynomial.coeff_C_mul_X, Polynomial.coeff_C]
    norm_num
  have hAle : A.natDegree ≤ 1 := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [hAdef, Polynomial.coeff_sub, Polynomial.coeff_C_mul_X, Polynomial.coeff_C]
    simp only [show N ≠ 1 by omega, show N ≠ 0 by omega, if_false, sub_zero]
  have hAdeg : A.natDegree = 1 :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hAle (by rw [hA1]; omega)
  have hAlc : A.leadingCoeff = (b : ℤ) := by rw [Polynomial.leadingCoeff, hAdeg, hA1]
  have hA0pow : (A ^ l).coeff 0 = (-a) ^ l := by
    rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_pow,
      ← Polynomial.coeff_zero_eq_eval_zero (p := A), hA0]
  have hA0ne : (A ^ l).coeff 0 ≠ 0 := by
    rw [hA0pow]
    exact pow_ne_zero _ (neg_ne_zero.mpr ha)
  have hAtrail : (A ^ l).natTrailingDegree = 0 := by
    rw [Polynomial.natTrailingDegree_eq_zero]
    exact Or.inr hA0ne
  -- The lowest nonzero coefficient of `B = A^l * Q` is `(-a)^l * (lowest coeff of Q)`.
  have hcoeff : B.coeff Q.natTrailingDegree = (-a) ^ l * Q.coeff Q.natTrailingDegree := by
    have h1 := Polynomial.coeff_mul_natTrailingDegree_add_natTrailingDegree (p := A ^ l) (q := Q)
    rw [hAtrail, zero_add] at h1
    rw [hQ, h1, Polynomial.trailingCoeff_eq_coeff_zero hA0ne, hA0pow]
    rfl
  have hQcoeff_ne : Q.coeff Q.natTrailingDegree ≠ 0 :=
    Polynomial.coeff_natTrailingDegree_ne_zero.mpr hQne
  have hBcoeff_ne : B.coeff Q.natTrailingDegree ≠ 0 := by
    rw [hcoeff]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr ha)) hQcoeff_ne
  have ht_le : Q.natTrailingDegree ≤ B.natDegree := Polynomial.le_natDegree_of_ne_zero hBcoeff_ne
  have htrail_bound : a.natAbs ^ l ≤ (B.coeff Q.natTrailingDegree).natAbs := by
    rw [hcoeff, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_neg]
    calc a.natAbs ^ l = a.natAbs ^ l * 1 := (mul_one _).symm
      _ ≤ a.natAbs ^ l * (Q.coeff Q.natTrailingDegree).natAbs :=
          Nat.mul_le_mul_left _ (Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hQcoeff_ne))
  have hQlc_ne : Q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQne
  have hlead_eq : B.coeff B.natDegree = (b : ℤ) ^ l * Q.leadingCoeff := by
    rw [Polynomial.coeff_natDegree, hQ, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_pow, hAlc]
  have hlead_bound : b ^ l ≤ (B.coeff B.natDegree).natAbs := by
    rw [hlead_eq, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
    calc b ^ l = b ^ l * 1 := (mul_one _).symm
      _ ≤ b ^ l * (Q.leadingCoeff).natAbs :=
          Nat.mul_le_mul_left _ (Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hQlc_ne))
  by_cases hcase : a.natAbs ≤ b
  · exact ⟨B.natDegree, le_rfl, by rw [max_eq_right hcase]; exact hlead_bound⟩
  · rw [not_le] at hcase
    exact ⟨Q.natTrailingDegree, ht_le, by rw [max_eq_left (le_of_lt hcase)]; exact htrail_bound⟩

end Commons.NumberTheory.Height.MahlerMeasure