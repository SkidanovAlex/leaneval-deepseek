import Mathlib

namespace Work.A14D

/-- For `‖r‖ < 1`, the polynomially-weighted geometric series `∑ r ^ n * (n + 1) ^ k`
converges.  This is the standard fact that exponential decay beats polynomial growth,
obtained here by expanding `(n + 1) ^ k` binomially into `∑ i ≤ k, (k choose i) * n ^ i`
and using Mathlib's `summable_pow_mul_geometric_of_norm_lt_one` for each monomial. -/
lemma summable_pow_mul_add_one_pow (k : ℕ) {r : ℝ} (hr : ‖r‖ < 1) :
    Summable (fun n : ℕ => r ^ n * ((n : ℝ) + 1) ^ k) := by
  have hsum : Summable (fun n : ℕ =>
      ∑ i ∈ Finset.range (k + 1), (Nat.choose k i : ℝ) * ((n : ℝ) ^ i * r ^ n)) := by
    apply summable_sum
    intro i _
    exact (summable_pow_mul_geometric_of_norm_lt_one i hr).mul_left _
  refine hsum.congr fun n => ?_
  rw [add_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [one_pow, mul_one]
  ring

theorem powSeries_summable (a : ℕ → ℂ) {C R : ℝ} {k : ℕ} (hC : 0 ≤ C) (hR : 0 ≤ R)
    (ha : ∀ n : ℕ, ‖a n‖ ≤ C * R ^ n * ((n : ℝ) + 1) ^ k)
    {w : ℂ} (hw : R * ‖w‖ < 1) :
    Summable (fun n : ℕ => ‖a n * w ^ n‖) := by
  have hr1 : ‖R * ‖w‖‖ < 1 := by
    rw [Real.norm_of_nonneg (mul_nonneg hR (norm_nonneg w))]
    exact hw
  have hg : Summable (fun n : ℕ => C * ((R * ‖w‖) ^ n * ((n : ℝ) + 1) ^ k)) :=
    (summable_pow_mul_add_one_pow k hr1).mul_left C
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_ hg
  intro n
  rw [norm_mul, norm_pow]
  calc ‖a n‖ * ‖w‖ ^ n ≤ (C * R ^ n * ((n : ℝ) + 1) ^ k) * ‖w‖ ^ n := by
        gcongr
        exact ha n
    _ = C * ((R * ‖w‖) ^ n * ((n : ℝ) + 1) ^ k) := by
        rw [mul_pow]; ring

end Work.A14D
