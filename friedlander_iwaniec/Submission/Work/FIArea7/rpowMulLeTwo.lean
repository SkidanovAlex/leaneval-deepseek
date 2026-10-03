import Mathlib

namespace Work.FIArea7

theorem rpowMulLeTwo {M Z B a α ρ γ : ℝ} (hM : 1 ≤ M) (hZ : 0 ≤ Z) (hZa : Z ≤ M ^ a)
    (hB : 0 ≤ B) (hBb : B ≤ 2 * M) (hα : 0 ≤ α) (hρ : 0 ≤ ρ) (hγ : a * α + ρ ≤ γ) :
    Z ^ α * B ^ ρ ≤ (2 : ℝ) ^ ρ * M ^ γ := by
  have hMpos : 0 < M := lt_of_lt_of_le one_pos hM
  have hstep : Z ^ α * B ^ ρ ≤ M ^ (a * α) * ((2 : ℝ) ^ ρ * M ^ ρ) := by
    have h1 : Z ^ α ≤ M ^ (a * α) := by
      have h := Real.rpow_le_rpow hZ hZa hα
      rwa [← Real.rpow_mul (le_of_lt hMpos) a α] at h
    have h2 : B ^ ρ ≤ (2 : ℝ) ^ ρ * M ^ ρ := by
      have h := Real.rpow_le_rpow hB hBb hρ
      rwa [Real.mul_rpow (by norm_num) (le_of_lt hMpos)] at h
    exact mul_le_mul h1 h2 (Real.rpow_nonneg hB ρ) (Real.rpow_nonneg (le_of_lt hMpos) _)
  calc Z ^ α * B ^ ρ ≤ M ^ (a * α) * ((2 : ℝ) ^ ρ * M ^ ρ) := hstep
    _ = (2 : ℝ) ^ ρ * M ^ (a * α + ρ) := by rw [Real.rpow_add hMpos]; ring
    _ ≤ (2 : ℝ) ^ ρ * M ^ γ :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hM hγ)
          (Real.rpow_nonneg (by norm_num) ρ)

end Work.FIArea7
