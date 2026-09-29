import Mathlib

/-!
# Summability of a Gaussian (theta-type) series over `ℤ`

`Real.exp (-c * n^2)` is summable over `ℤ` for `c > 0` (the classical theta series),
and consequently so is `Real.exp (-a * (t * n + x)^2)` for `a > 0`, `t > 0`.

The route is the elementary inequality
`(t*n + x)^2 ≥ t^2 * n^2 / 2 - x^2`, i.e. `(t*n + x)^2 - (t^2*n^2/2 - x^2) = (t*n + 2*x)^2/2 ≥ 0`,
which bounds the affine Gaussian by a constant times the pure Gaussian.
-/

namespace Work.ResMath

open Real Filter

/-- The theta series `∑_{n : ℤ} exp (-c * n^2)` converges for `c > 0`. -/
lemma summable_exp_neg_mul_sq_int {c : ℝ} (hc : 0 < c) :
    Summable fun n : ℤ => Real.exp (-c * (n : ℝ) ^ 2) := by
  have hNat : Summable fun n : ℕ => Real.exp (-c * (n : ℝ) ^ 2) := by
    refine Summable.of_norm_bounded_eventually_nat (g := fun n : ℕ => Real.exp (-c * n)) ?_ ?_
    · simpa [mul_comm] using Real.summable_exp_nat_mul_iff.mpr (show -c < 0 by linarith)
    · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
      apply Real.exp_le_exp.mpr
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      nlinarith [sq_nonneg ((n : ℝ) - 1)]
  rw [summable_int_iff_summable_nat_and_neg]
  exact ⟨hNat, by simpa using hNat⟩

theorem summable_exp_neg_affine_sq (a x : ℝ) (ha : 0 < a) {t : ℕ} (ht : 0 < t) :
    Summable fun n : ℤ => Real.exp (-a * (t * (n : ℝ) + x) ^ 2) := by
  have ht1 : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hc : 0 < a * (t : ℝ) ^ 2 / 2 := by positivity
  refine Summable.of_norm_bounded
    (g := fun n : ℤ => Real.exp (a * x ^ 2) * Real.exp (-(a * (t : ℝ) ^ 2 / 2) * (n : ℝ) ^ 2))
    ?_ ?_
  · exact (summable_exp_neg_mul_sq_int hc).mul_left _
  · intro n
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _), ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h : 0 ≤ a * ((t : ℝ) * (n : ℝ) + 2 * x) ^ 2 := mul_nonneg ha.le (sq_nonneg _)
    nlinarith [h]

end Work.ResMath
