import Mathlib

namespace Work.HP.Q44Main

theorem min_compare_good2 (CL Z Δ M : ℝ) (hZ : 1 ≤ Z) (hΔ : 1 ≤ Δ) (hM : 1 ≤ M)
    (hCL : 0 < CL) (hZ3 : Z^(3:ℝ) ≤ M^(106:ℝ) * Δ) :
    CL * Z^(6:ℝ) * Δ^(3:ℝ) ≤
      CL * (Z^((9:ℝ)/2) * Δ^(2:ℝ) * (Z^((3:ℝ)/2) + Δ^((3:ℝ)/2)) * M^(53:ℝ)) := by
  have hZ0 : 0 ≤ Z := le_trans zero_le_one hZ
  have hΔ0 : 0 ≤ Δ := le_trans zero_le_one hΔ
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have hZpos : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hΔpos : 0 < Δ := lt_of_lt_of_le zero_lt_one hΔ
  -- From Z^3 ≤ M^106 * Δ, take the (1/2)-power: Z^(3/2) ≤ M^53 * Δ^(1/2).
  have key : Z^((3:ℝ)/2) ≤ M^(53:ℝ) * Δ^((1:ℝ)/2) := by
    have step := Real.rpow_le_rpow (Real.rpow_nonneg hZ0 3) hZ3 (by norm_num : (0:ℝ) ≤ 1/2)
    rw [Real.mul_rpow (Real.rpow_nonneg hM0 106) hΔ0] at step
    rw [← Real.rpow_mul hZ0 3 (1/2)] at step
    rw [← Real.rpow_mul hM0 106 (1/2)] at step
    have e1 : (3:ℝ) * (1/2) = 3/2 := by norm_num
    have e2 : (106:ℝ) * (1/2) = 53 := by norm_num
    rw [e1, e2] at step
    exact step
  have h1 : Z^(6:ℝ) = Z^((3:ℝ)/2) * Z^((9:ℝ)/2) := by
    rw [← Real.rpow_add hZpos]; norm_num
  have hA : Z^((3:ℝ)/2) * Z^((9:ℝ)/2) * Δ^(3:ℝ) ≤
      (M^(53:ℝ) * Δ^((1:ℝ)/2)) * Z^((9:ℝ)/2) * Δ^(3:ℝ) := by
    have t1 := mul_le_mul_of_nonneg_right key (Real.rpow_nonneg hZ0 ((9:ℝ)/2))
    have t2 := mul_le_mul_of_nonneg_right t1 (Real.rpow_nonneg hΔ0 (3:ℝ))
    exact t2
  have hB : (M^(53:ℝ) * Δ^((1:ℝ)/2)) * Z^((9:ℝ)/2) * Δ^(3:ℝ) =
      Z^((9:ℝ)/2) * Δ^((7:ℝ)/2) * M^(53:ℝ) := by
    have hΔe : Δ^((1:ℝ)/2) * Δ^(3:ℝ) = Δ^((7:ℝ)/2) := by
      rw [← Real.rpow_add hΔpos]; norm_num
    rw [show (M^(53:ℝ) * Δ^((1:ℝ)/2)) * Z^((9:ℝ)/2) * Δ^(3:ℝ)
          = Z^((9:ℝ)/2) * (Δ^((1:ℝ)/2) * Δ^(3:ℝ)) * M^(53:ℝ) by ring, hΔe]
  have hC : Z^((9:ℝ)/2) * Δ^((7:ℝ)/2) * M^(53:ℝ) ≤
      Z^((9:ℝ)/2) * Δ^(2:ℝ) * (Z^((3:ℝ)/2) + Δ^((3:ℝ)/2)) * M^(53:ℝ) := by
    have hΔe : Δ^((2:ℝ)) * Δ^((3:ℝ)/2) = Δ^((7:ℝ)/2) := by
      rw [← Real.rpow_add hΔpos]; norm_num
    have hC1 : Δ^((7:ℝ)/2) ≤ Δ^(2:ℝ) * (Z^((3:ℝ)/2) + Δ^((3:ℝ)/2)) := by
      rw [show Δ^(2:ℝ) * (Z^((3:ℝ)/2) + Δ^((3:ℝ)/2)) =
            Δ^(2:ℝ)*Z^((3:ℝ)/2) + Δ^(2:ℝ)*Δ^((3:ℝ)/2) by ring, hΔe]
      exact le_add_of_nonneg_left (mul_nonneg (Real.rpow_nonneg hΔ0 2) (Real.rpow_nonneg hZ0 _))
    have t1 := mul_le_mul_of_nonneg_left hC1 (Real.rpow_nonneg hZ0 ((9:ℝ)/2))
    have t2 := mul_le_mul_of_nonneg_right t1 (Real.rpow_nonneg hM0 (53:ℝ))
    calc Z^((9:ℝ)/2) * Δ^((7:ℝ)/2) * M^(53:ℝ)
        = (Z^((9:ℝ)/2) * Δ^((7:ℝ)/2)) * M^(53:ℝ) := by ring
      _ ≤ (Z^((9:ℝ)/2) * (Δ^(2:ℝ) * (Z^((3:ℝ)/2) + Δ^((3:ℝ)/2)))) * M^(53:ℝ) := t2
      _ = Z^((9:ℝ)/2) * Δ^(2:ℝ) * (Z^((3:ℝ)/2) + Δ^((3:ℝ)/2)) * M^(53:ℝ) := by ring
  have hmain : Z^(6:ℝ) * Δ^(3:ℝ) ≤
      Z^((9:ℝ)/2) * Δ^(2:ℝ) * (Z^((3:ℝ)/2) + Δ^((3:ℝ)/2)) * M^(53:ℝ) := by
    calc Z^(6:ℝ) * Δ^(3:ℝ)
        = Z^((3:ℝ)/2) * Z^((9:ℝ)/2) * Δ^(3:ℝ) := by rw [h1]
      _ ≤ (M^(53:ℝ) * Δ^((1:ℝ)/2)) * Z^((9:ℝ)/2) * Δ^(3:ℝ) := hA
      _ = Z^((9:ℝ)/2) * Δ^((7:ℝ)/2) * M^(53:ℝ) := hB
      _ ≤ Z^((9:ℝ)/2) * Δ^(2:ℝ) * (Z^((3:ℝ)/2) + Δ^((3:ℝ)/2)) * M^(53:ℝ) := hC
  calc CL * Z^(6:ℝ) * Δ^(3:ℝ)
      = CL * (Z^(6:ℝ) * Δ^(3:ℝ)) := by ring
    _ ≤ CL * (Z^((9:ℝ)/2) * Δ^(2:ℝ) * (Z^((3:ℝ)/2) + Δ^((3:ℝ)/2)) * M^(53:ℝ)) := by
        exact mul_le_mul_of_nonneg_left hmain (le_of_lt hCL)

end Work.HP.Q44Main
