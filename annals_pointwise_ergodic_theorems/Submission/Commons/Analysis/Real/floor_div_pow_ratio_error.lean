import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Ring.Star

namespace Commons.Analysis.Real

/-- The error in approximating the ratio `(N / 2 ^ k) / N` by `2 ^ (-k)` is at most `1 / N`:
    `|⌊N / 2^k⌋ / N - 2^{-k}| ≤ 1 / N` for `N ≥ 1`.  This is the floor remainder estimate used
    in the dyadic telescoping decomposition of Cesàro averages. -/
theorem floor_div_pow_ratio_error (N k : ℕ) (hN : 1 ≤ N) :
    |(((N / 2 ^ k : ℕ) : ℝ) / (N : ℝ)) - ((2 : ℝ) ^ k)⁻¹| ≤ (N : ℝ)⁻¹ := by
  set q := N / 2 ^ k with hq
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have h2kpos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  have h2kne : (2 : ℝ) ^ k ≠ 0 := ne_of_gt h2kpos
  -- `q` is the floor of `N / 2^k` in the reals
  have hq_le : (q : ℝ) ≤ (N : ℝ) / (2 : ℝ) ^ k := by
    rw [le_div_iff₀ h2kpos]
    have hnat : q * 2 ^ k ≤ N := by
      rw [hq]; exact Nat.div_mul_le_self N (2 ^ k)
    calc (q : ℝ) * (2 : ℝ) ^ k = ((q * 2 ^ k : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (N : ℝ) := by exact_mod_cast hnat
  have hq_lt : (N : ℝ) / (2 : ℝ) ^ k < (q : ℝ) + 1 := by
    rw [div_lt_iff₀ h2kpos]
    have hnat : N < (q + 1) * 2 ^ k := by
      have h1 : N / 2 ^ k < q + 1 := by rw [hq]; exact Nat.lt_succ_self _
      exact (Nat.div_lt_iff_lt_mul (by positivity : 0 < 2 ^ k)).mp h1
    calc (N : ℝ) < ((q + 1) * 2 ^ k : ℕ) := by exact_mod_cast hnat
      _ = ((q : ℝ) + 1) * (2 : ℝ) ^ k := by push_cast; ring
  have hdiff : |(q : ℝ) - (N : ℝ) / (2 : ℝ) ^ k| ≤ 1 := by
    rw [abs_sub_le_iff]
    exact ⟨by linarith, by linarith⟩
  have hx : ((q : ℝ) / (N : ℝ)) - ((2 : ℝ) ^ k)⁻¹
      = (N : ℝ)⁻¹ * ((q : ℝ) - (N : ℝ) / (2 : ℝ) ^ k) := by
    field_simp
  rw [hx, abs_mul, abs_of_pos (inv_pos.mpr hNpos)]
  calc (N : ℝ)⁻¹ * |(q : ℝ) - (N : ℝ) / (2 : ℝ) ^ k| ≤ (N : ℝ)⁻¹ * 1 := by
        exact mul_le_mul_of_nonneg_left hdiff (le_of_lt (inv_pos.mpr hNpos))
    _ = (N : ℝ)⁻¹ := mul_one _

end Commons.Analysis.Real