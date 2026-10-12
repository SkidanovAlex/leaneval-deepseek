import Mathlib.Analysis.SpecialFunctions.Pow.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR.LatGreen

theorem rpow_neg_three_halves_mul_sqrt_pi_div_eq {a : ℝ} (ha : 0 < a) :
    (4 * Real.pi) ^ (-(3 / 2 : ℝ)) * Real.sqrt (Real.pi / a)
      = 1 / (8 * Real.pi * Real.sqrt a) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  -- `4 ^ (-3/2) = 1/8`
  have h4 : (4 : ℝ) ^ (-(3 / 2 : ℝ)) = 1 / 8 := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4)]
    rw [show (3 / 2 : ℝ) = (1 / 2) * 3 by norm_num,
      Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num [Real.sqrt_eq_rpow]
  -- `π ^ (-3/2) * π ^ (1/2) = π ^ (-1)`
  have hpi_pow : Real.pi ^ (-(3 / 2 : ℝ)) * Real.pi ^ (1 / 2 : ℝ) = Real.pi ^ (-1 : ℝ) := by
    rw [← Real.rpow_add hpi]
    norm_num
  have hpi_inv : Real.pi ^ (-1 : ℝ) = 1 / Real.pi := by
    rw [show (-1 : ℝ) = -(1 : ℝ) by norm_num, Real.rpow_neg hpi.le, Real.rpow_one,
      inv_eq_one_div]
  -- reduce the constant part
  have hkey : (4 * Real.pi) ^ (-(3 / 2 : ℝ)) * Real.sqrt Real.pi = 1 / (8 * Real.pi) := by
    calc
      (4 * Real.pi) ^ (-(3 / 2 : ℝ)) * Real.sqrt Real.pi
          = (4 : ℝ) ^ (-(3 / 2 : ℝ)) * Real.pi ^ (-(3 / 2 : ℝ)) *
              Real.pi ^ (1 / 2 : ℝ) := by
              rw [Real.mul_rpow (by norm_num) hpi.le, Real.sqrt_eq_rpow]
      _ = (4 : ℝ) ^ (-(3 / 2 : ℝ)) *
              (Real.pi ^ (-(3 / 2 : ℝ)) * Real.pi ^ (1 / 2 : ℝ)) := by ring
      _ = (1 / 8) * (1 / Real.pi) := by rw [h4, hpi_pow, hpi_inv]
      _ = 1 / (8 * Real.pi) := by ring
  rw [Real.sqrt_div hpi.le a]
  calc
    (4 * Real.pi) ^ (-(3 / 2 : ℝ)) * (Real.sqrt Real.pi / Real.sqrt a)
        = ((4 * Real.pi) ^ (-(3 / 2 : ℝ)) * Real.sqrt Real.pi) / Real.sqrt a := by ring
    _ = (1 / (8 * Real.pi)) / Real.sqrt a := by rw [hkey]
    _ = 1 / (8 * Real.pi * Real.sqrt a) := by field_simp

end Work.BoseFixR.LatGreen
