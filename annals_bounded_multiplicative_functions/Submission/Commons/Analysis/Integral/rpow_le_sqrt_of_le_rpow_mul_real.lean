import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Analysis.Integral

theorem rpow_le_sqrt_of_le_rpow_mul_real {p A B : ℝ} (hp : 2 ≤ p) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : A ≤ A ^ ((p - 2) / p) * B) : A ^ (1 / p) ≤ B ^ ((1 : ℝ) / 2) := by
  have hp0 : p ≠ 0 := by linarith
  rcases eq_or_lt_of_le hA with hA0 | hApos
  · -- Case A = 0
    rw [← hA0, Real.zero_rpow (div_ne_zero one_ne_zero hp0)]
    exact Real.rpow_nonneg hB _
  · -- Case A > 0
    have hcpos : 0 < A ^ ((p - 2) / p) := Real.rpow_pos_of_pos hApos _
    have h2p : (1 : ℝ) - (p - 2) / p = 2 / p := by
      field_simp
      ring
    have hAdiv : A ^ (2 / p) = A / A ^ ((p - 2) / p) := by
      rw [← h2p, Real.rpow_sub hApos, Real.rpow_one]
    -- Key inequality: A^(2/p) ≤ B
    have hle : A ^ (2 / p) ≤ B := by
      rw [hAdiv, div_le_iff₀ hcpos]
      calc A ≤ A ^ ((p - 2) / p) * B := h
        _ = B * A ^ ((p - 2) / p) := mul_comm _ _
    -- Raise both sides to the power 1/2
    have h1 : (A ^ (2 / p)) ^ ((1 : ℝ) / 2) ≤ B ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow (Real.rpow_nonneg hA _) hle (by norm_num)
    have hmul : (A ^ (2 / p)) ^ ((1 : ℝ) / 2) = A ^ (1 / p) := by
      rw [← Real.rpow_mul hA (2 / p) ((1 : ℝ) / 2)]
      congr 1
      field_simp
    rwa [hmul] at h1

end Commons.Analysis.Integral