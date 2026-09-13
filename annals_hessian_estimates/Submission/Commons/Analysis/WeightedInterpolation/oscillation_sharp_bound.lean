import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace Commons.Analysis.WeightedInterpolation

theorem oscillation_sharp_bound {n : ℕ} {D E K : ℝ} (hD : 0 < D) (hE : 0 < E) (hE1 : E ≤ 1)
    (hK : 0 < K) :
    D ^ n * (K * (E * D / 2 ^ (n + 1)) / (D - E * D / 2 ^ (n + 1)) ^ (n + 1)) ≤ E * K := by
  set c : ℝ := 2 ^ (n + 1) with hc
  have hc_pos : 0 < c := by rw [hc]; positivity
  have hc_ge2 : (2 : ℝ) ≤ c := by
    rw [hc]
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n + 1) := by
          apply pow_le_pow_right₀ (by norm_num)
          omega
  -- E / c ≤ 1/2
  have hEdiv : E / c ≤ 1 / 2 := by
    have h1 : E / c ≤ 1 / c := div_le_div_of_nonneg_right hE1 (le_of_lt hc_pos)
    have h2 : (1 : ℝ) / c ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hc_ge2
    linarith
  have hhalf : (1 : ℝ) / 2 ≤ 1 - E / c := by linarith
  have hbase_eq : D - E * D / c = D * (1 - E / c) := by ring
  have hbase : D / 2 ≤ D - E * D / c := by
    rw [hbase_eq]
    calc D / 2 = D * (1 / 2) := by ring
      _ ≤ D * (1 - E / c) := mul_le_mul_of_nonneg_left hhalf (le_of_lt hD)
  have hden_pos : 0 < D - E * D / c := by linarith
  -- key: (D/2)^(n+1) ≤ (D - E*D/c)^(n+1)
  have hM : (D / 2) ^ (n + 1) ≤ (D - E * D / c) ^ (n + 1) := by
    apply pow_le_pow_left₀ (by positivity) hbase
  have hM2 : D ^ (n + 1) / c ≤ (D - E * D / c) ^ (n + 1) := by
    have h := hM
    rw [div_pow, ← hc] at h
    exact h
  have hN_nonneg : 0 ≤ K * E * D ^ (n + 1) / c := by positivity
  have hMpos : 0 < D ^ (n + 1) / c := by positivity
  have hnum : D ^ n * (K * (E * D / c)) = K * E * D ^ (n + 1) / c := by
    calc D ^ n * (K * (E * D / c)) = K * E * (D ^ n * D) / c := by ring
      _ = K * E * D ^ (n + 1) / c := by rw [pow_succ]
  rw [← mul_div_assoc, hnum]
  calc (K * E * D ^ (n + 1) / c) / (D - E * D / c) ^ (n + 1)
      ≤ (K * E * D ^ (n + 1) / c) / (D ^ (n + 1) / c) :=
        div_le_div_of_nonneg_left hN_nonneg hMpos hM2
    _ = E * K := by
        rw [div_div_div_cancel_right₀ (ne_of_gt hc_pos)]
        rw [mul_div_assoc, div_self (by positivity : (D : ℝ) ^ (n + 1) ≠ 0)]
        ring

end Commons.Analysis.WeightedInterpolation