import Mathlib.Algebra.Order.Star.Real
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.RingTheory.Binomial

open Polynomial Finset

namespace Commons.Analysis.Analytic

/-- The descending Pochhammer polynomial over `ℤ`, evaluated (via scalar multiplication)
at a real number, is the product `∏_{j<n} (a - j)`. -/
lemma descPochhammer_int_smeval_eq_prod (a : ℝ) (n : ℕ) :
    (descPochhammer ℤ n).smeval a = ∏ j ∈ Finset.range n, (a - (j : ℝ)) := by
  rw [← eval₂_smulOneHom_eq_smeval (R := ℤ) (S := ℝ) (descPochhammer ℤ n) a]
  rw [eval₂_eq_eval_map]
  rw [descPochhammer_map]
  exact descPochhammer_eval_eq_prod_range n a

/-- The generalized binomial coefficient `Ring.choose a n` for a real `a` is the
descending Pochhammer product divided by `n!`. -/
lemma ring_choose_eq_prod_div (a : ℝ) (n : ℕ) :
    Ring.choose a n = (∏ j ∈ Finset.range n, (a - (j : ℝ))) / (n.factorial : ℝ) := by
  have h := Ring.descPochhammer_eq_factorial_smul_choose a n
  rw [descPochhammer_int_smeval_eq_prod] at h
  rw [h, nsmul_eq_mul]
  field_simp

/-- Absolute value of `Ring.choose a n` as a product of the individual ratios. -/
lemma ring_choose_abs_eq_prod (a : ℝ) (n : ℕ) :
    |Ring.choose a n| = ∏ j ∈ Finset.range n, |a - (j : ℝ)| / ((j : ℝ) + 1) := by
  rw [ring_choose_eq_prod_div, abs_div, abs_prod,
    abs_of_pos (by exact_mod_cast Nat.factorial_pos n),
    Nat.factorial_eq_prod_range_add_one n, Nat.cast_prod, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl ?_
  intro j _
  rw [Nat.cast_add, Nat.cast_one]

/-- Each factor of the product representation is bounded by `2 * |a| + 2`. -/
lemma ring_choose_factor_le (a : ℝ) (j : ℕ) :
    |a - (j : ℝ)| / ((j : ℝ) + 1) ≤ 2 * |a| + 2 := by
  rw [div_le_iff₀ (by positivity)]
  have h1 : |a - (j : ℝ)| ≤ |a| + |(j : ℝ)| := by
    simpa using abs_sub_le a 0 (j : ℝ)
  have h3 : |(j : ℝ)| = (j : ℝ) := abs_of_nonneg (Nat.cast_nonneg j)
  rw [h3] at h1
  have h2 : (0 : ℝ) ≤ |a| := abs_nonneg a
  have h4 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  nlinarith [h1, h2, h4]

/-- Exponential bound for the generalized binomial coefficients of a real number. -/
lemma ring_choose_abs_le (a : ℝ) (n : ℕ) :
    |Ring.choose a n| ≤ (2 * |a| + 2) ^ n := by
  rw [ring_choose_abs_eq_prod]
  calc ∏ j ∈ Finset.range n, |a - (j : ℝ)| / ((j : ℝ) + 1)
      ≤ ∏ _j ∈ Finset.range n, (2 * |a| + 2) := by
        apply Finset.prod_le_prod
        · intro j _
          positivity
        · intro j _
          exact ring_choose_factor_le a j
    _ = (2 * |a| + 2) ^ n := by rw [Finset.prod_const, Finset.card_range]

theorem ring_choose_bound (a : ℝ) : ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, |Ring.choose a n| ≤ C ^ n :=
  ⟨2 * |a| + 2, by nlinarith [abs_nonneg a], ring_choose_abs_le a⟩

end Commons.Analysis.Analytic