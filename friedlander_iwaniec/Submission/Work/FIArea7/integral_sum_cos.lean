import Mathlib

open MeasureTheory intervalIntegral

namespace Work.FIArea7

/-- **Finite geometric sum against cosines.**  Interchanging the finite sum with the
interval integral and using `∫₀¹ x^{n-1} dx = 1/n` for `n ≥ 1`, the integral of the
polynomial `∑_{n=1}^{K} x^{n-1} cos(nα)` over `[0,1]` is the partial sum
`∑_{n=1}^{K} cos(nα)/n`. -/
theorem integral_sum_cos (α : ℝ) (K : ℕ) :
    (∫ x in (0:ℝ)..1, ∑ n ∈ Finset.Icc 1 K, x ^ (n - 1) * Real.cos ((n : ℝ) * α))
      = ∑ n ∈ Finset.Icc 1 K, Real.cos ((n : ℝ) * α) / (n : ℝ) := by
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hpow : (∫ x in (0:ℝ)..1, x ^ (n - 1)) = ((n : ℝ))⁻¹ := by
      rw [integral_pow]
      have hcast : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
        rw [Nat.cast_sub hn1]; ring
      rw [hcast, one_pow, zero_pow (by omega : n - 1 + 1 ≠ 0), sub_zero]
      rw [one_div]
    rw [intervalIntegral.integral_mul_const, hpow, div_eq_mul_inv]
    ring
  · intro n hn
    exact ((continuous_id.pow (n - 1)).mul continuous_const).intervalIntegrable _ _

end Work.FIArea7
