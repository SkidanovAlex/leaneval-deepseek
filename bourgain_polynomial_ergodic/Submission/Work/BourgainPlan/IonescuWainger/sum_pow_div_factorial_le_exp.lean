import Mathlib

namespace Work.BourgainPlan.IonescuWainger

/-- For `1 ≤ r`, the truncated exponential sum `∑_{b ≤ r} b ^ (2r) / b!` is bounded by
`e * r ^ (2r)`.  Each term is at most `r ^ (2r) / b!` since `b ≤ r`, and the truncated
exponential series `∑_{b ≤ r} 1 / b!` is at most `e`. -/
theorem sum_pow_div_factorial_le_exp (r : ℕ) (hr : 1 ≤ r) :
    ∑ b ∈ Finset.range (r + 1), (b : ℝ) ^ (2 * r) / (b.factorial : ℝ)
      ≤ Real.exp 1 * (r : ℝ) ^ (2 * r) := by
  have hsum : ∑ b ∈ Finset.range (r + 1), (b : ℝ) ^ (2 * r) / (b.factorial : ℝ)
      ≤ (r : ℝ) ^ (2 * r) * ∑ b ∈ Finset.range (r + 1), 1 / (b.factorial : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun b hb => ?_
    have hbr : b ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    have hbR : (b : ℝ) ≤ (r : ℝ) := by exact_mod_cast hbr
    have hfac : (0 : ℝ) < (b.factorial : ℝ) := by exact_mod_cast b.factorial_pos
    have hpow : (b : ℝ) ^ (2 * r) ≤ (r : ℝ) ^ (2 * r) :=
      pow_le_pow_left₀ (Nat.cast_nonneg b) hbR (2 * r)
    rw [mul_one_div]
    exact div_le_div_of_nonneg_right hpow hfac.le
  have hexp : ∑ b ∈ Finset.range (r + 1), 1 / (b.factorial : ℝ) ≤ Real.exp 1 := by
    simpa using Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num) (r + 1)
  calc ∑ b ∈ Finset.range (r + 1), (b : ℝ) ^ (2 * r) / (b.factorial : ℝ)
      ≤ (r : ℝ) ^ (2 * r) * ∑ b ∈ Finset.range (r + 1), 1 / (b.factorial : ℝ) := hsum
    _ ≤ (r : ℝ) ^ (2 * r) * Real.exp 1 :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = Real.exp 1 * (r : ℝ) ^ (2 * r) := by ring

end Work.BourgainPlan.IonescuWainger
