import Mathlib

namespace Work.HP.Q44Main

theorem m17_le_mix (M Z Δ : ℝ) (hM : 1 ≤ M) (hZ : 1 ≤ Z) (hΔ : 1 ≤ Δ)
    (hZ3 : M^(106:ℝ) * Δ ≤ Z^(3:ℝ)) :
    M^(17:ℝ) ≤ Z^((1:ℝ)/2) * Δ^((-1:ℝ)/6) := by
  have hM0 : (0:ℝ) ≤ M := by linarith
  have hΔ0 : (0:ℝ) ≤ Δ := by linarith
  have hΔpos : (0:ℝ) < Δ := by linarith
  have hZ0 : (0:ℝ) ≤ Z := by linarith
  have hLHS0 : (0:ℝ) ≤ M^(106:ℝ) * Δ :=
    mul_nonneg (Real.rpow_nonneg hM0 106) hΔ0
  have hstep : (M^(106:ℝ) * Δ)^((1:ℝ)/6) ≤ (Z^(3:ℝ))^((1:ℝ)/6) :=
    Real.rpow_le_rpow hLHS0 hZ3 (by norm_num)
  have hL : (M^(106:ℝ) * Δ)^((1:ℝ)/6) = M^((53:ℝ)/3) * Δ^((1:ℝ)/6) := by
    rw [Real.mul_rpow (Real.rpow_nonneg hM0 106) hΔ0]
    congr 1
    rw [← Real.rpow_mul hM0, show (106:ℝ) * ((1:ℝ)/6) = (53:ℝ)/3 by norm_num]
  have hR : (Z^(3:ℝ))^((1:ℝ)/6) = Z^((1:ℝ)/2) := by
    rw [← Real.rpow_mul hZ0, show (3:ℝ) * ((1:ℝ)/6) = (1:ℝ)/2 by norm_num]
  rw [hL, hR] at hstep
  have hprod : Δ^((1:ℝ)/6) * Δ^((-1:ℝ)/6) = 1 := by
    rw [← Real.rpow_add hΔpos, show (1:ℝ)/6 + (-1:ℝ)/6 = 0 by norm_num, Real.rpow_zero]
  have key : M^((53:ℝ)/3) ≤ Z^((1:ℝ)/2) * Δ^((-1:ℝ)/6) := by
    have h2 := mul_le_mul_of_nonneg_right hstep (Real.rpow_nonneg hΔ0 ((-1:ℝ)/6))
    rw [mul_assoc, hprod, mul_one] at h2
    exact h2
  exact le_trans (Real.rpow_le_rpow_of_exponent_le hM (by norm_num)) key

end Work.HP.Q44Main
