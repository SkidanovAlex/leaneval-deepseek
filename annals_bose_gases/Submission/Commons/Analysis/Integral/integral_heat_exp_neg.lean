import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.Analysis.Integral

open MeasureTheory Real
open scoped Topology

theorem integral_heat_exp_neg {c : ℝ} (hc : 0 < c) :
    (∫ t in Set.Ioi (0 : ℝ), (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * Real.exp (-(c / t)))
      = 1 / (8 * Real.pi * Real.sqrt c) := by
  have hsub := integral_comp_rpow_Ioi
    (g := fun y : ℝ => (4 * Real.pi * y) ^ (-(3 / 2 : ℝ)) * Real.exp (-(c / y)))
    (p := (-2 : ℝ)) (by norm_num)
  rw [← hsub]
  have hsimp :
      (∫ x in Set.Ioi (0:ℝ), (|(-2:ℝ)| * x ^ ((-2:ℝ) - 1)) •
        ((4*Real.pi * x ^ (-2:ℝ)) ^ (-(3/2:ℝ)) * Real.exp (-(c / x ^ (-2:ℝ)))))
      = ∫ x in Set.Ioi (0:ℝ), 2 * (4*Real.pi)^(-(3/2:ℝ)) * Real.exp (-(c*x^2)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    have hx' : (0:ℝ) < x := hx
    rw [smul_eq_mul, show |(-2:ℝ)| = 2 by norm_num, show ((-2:ℝ) - 1) = -3 by norm_num]
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (le_of_lt hx')]
    rw [show ((-2:ℝ)) * (-(3/2)) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    have hx2 : x ^ (-2:ℝ) = (x^2)⁻¹ := by rw [Real.rpow_neg (le_of_lt hx'), Real.rpow_two]
    rw [hx2]
    have hdiv : c / (x^2)⁻¹ = c * x^2 := by rw [div_eq_mul_inv, inv_inv]
    rw [hdiv]
    have h3 : x ^ (-3:ℝ) = (x^3)⁻¹ := by
      rw [Real.rpow_neg (le_of_lt hx'), show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    rw [h3]
    have hxne : x ≠ 0 := ne_of_gt hx'
    field_simp
  rw [hsimp]
  have hgauss : (∫ x in Set.Ioi (0:ℝ), Real.exp (-(c*x^2))) = Real.sqrt (Real.pi/c)/2 := by
    simpa only [neg_mul] using integral_gaussian_Ioi c
  have hkey : (4*Real.pi)^(-(3/2:ℝ)) * Real.sqrt (Real.pi/c) = 1/(8*Real.pi*Real.sqrt c) := by
    have hA : (4*Real.pi)^(-(3/2:ℝ)) = 1/(8*Real.pi*Real.sqrt Real.pi) := by
      rw [Real.rpow_neg (by positivity : (0:ℝ) ≤ 4*Real.pi), show (3:ℝ)/2 = 1 + 1/2 by norm_num,
          Real.rpow_add (by positivity : (0:ℝ) < 4*Real.pi), Real.rpow_one]
      rw [Real.rpow_div_two_eq_sqrt 1 (by positivity : (0:ℝ) ≤ 4*Real.pi), Real.rpow_one,
          Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4),
          show Real.sqrt (4:ℝ) = 2 by rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]]
      field_simp
      ring
    rw [hA, Real.sqrt_div Real.pi_pos.le c]
    have hπ : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
    have hc' : Real.sqrt c ≠ 0 := (Real.sqrt_pos.mpr hc).ne'
    have hπ' : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
  rw [integral_const_mul, hgauss]
  rw [show (2 * (4*Real.pi)^(-(3/2:ℝ))) * (Real.sqrt (Real.pi/c)/2)
        = (4*Real.pi)^(-(3/2:ℝ)) * Real.sqrt (Real.pi/c) from by ring]
  exact hkey

end Commons.Analysis.Integral