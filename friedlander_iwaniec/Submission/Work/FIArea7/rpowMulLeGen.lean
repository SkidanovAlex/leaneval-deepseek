import Mathlib

namespace Work.FIArea7

theorem rpowMulLeGen {M B C a α ρ γ : ℝ} (hM : 1 ≤ M) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (hBb : B ≤ 2 * M) (hα : 0 ≤ α) (hρ : 0 ≤ ρ) (hγ : a * α + ρ ≤ γ) :
    (C * M ^ a) ^ α * B ^ ρ ≤ C ^ α * (2 : ℝ) ^ ρ * M ^ γ := by
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hM
  have hMa : (0 : ℝ) ≤ M ^ a := le_of_lt (Real.rpow_pos_of_pos hM0 a)
  have h1 : (C * M ^ a) ^ α = C ^ α * M ^ (a * α) := by
    rw [Real.mul_rpow hC hMa, ← Real.rpow_mul hM0.le a α]
  have h2 : B ^ ρ ≤ (2 : ℝ) ^ ρ * M ^ ρ := by
    calc B ^ ρ ≤ (2 * M) ^ ρ := Real.rpow_le_rpow hB hBb hρ
      _ = (2 : ℝ) ^ ρ * M ^ ρ := Real.mul_rpow (by norm_num) hM0.le
  have h4 : M ^ (a * α + ρ) ≤ M ^ γ := Real.rpow_le_rpow_of_exponent_le hM hγ
  calc (C * M ^ a) ^ α * B ^ ρ
      = (C ^ α * M ^ (a * α)) * B ^ ρ := by rw [h1]
    _ ≤ (C ^ α * M ^ (a * α)) * ((2 : ℝ) ^ ρ * M ^ ρ) :=
        mul_le_mul_of_nonneg_left h2 (mul_nonneg (Real.rpow_nonneg hC α) (Real.rpow_nonneg hM0.le _))
    _ = C ^ α * (2 : ℝ) ^ ρ * (M ^ (a * α) * M ^ ρ) := by ring
    _ = C ^ α * (2 : ℝ) ^ ρ * M ^ (a * α + ρ) := by rw [Real.rpow_add hM0]
    _ ≤ C ^ α * (2 : ℝ) ^ ρ * M ^ γ :=
        mul_le_mul_of_nonneg_left h4 (mul_nonneg (Real.rpow_nonneg hC α) (Real.rpow_nonneg (by norm_num) ρ))

end Work.FIArea7
