import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.SqrtKin

open MeasureTheory

/-- For `c > 0`, `∫_{t > 0} t^{-3} exp(-c/t) dt = c^{-2}`.

The substitution `y = 1/t` (change of variables `MeasureTheory.integral_comp_rpow_Ioi` with
exponent `-1`) turns the integral into `∫_{y > 0} y * exp(-c y) dy`, which is the Gamma integral
`∫_{y>0} y^{2-1} e^{-c y} dy = (1/c)^2 * Γ(2) = 1/c^2`. -/
theorem inv_cube_exp_div {c : ℝ} (hc : 0 < c) :
    ∫ t in Set.Ioi (0 : ℝ), t ^ (-(3 : ℝ)) * Real.exp (-(c / t)) = 1 / c ^ 2 := by
  -- The Gamma integral `∫_{y>0} y * exp (-(c*y)) = 1/c²`.
  have hbase : ∫ t in Set.Ioi (0 : ℝ), t * Real.exp (-(c * t)) = 1 / c ^ 2 := by
    have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (2 : ℝ)) (r := c) (by norm_num) hc
    simp only [show ((2 : ℝ) - 1) = 1 by norm_num, Real.rpow_one, Real.Gamma_two, mul_one] at h
    rw [h, Real.rpow_ofNat, one_div_pow]
  -- Change of variables `y = x^{-1}` in the integral over `Ioi 0`.
  have hcov := MeasureTheory.integral_comp_rpow_Ioi (fun y : ℝ => y * Real.exp (-(c * y)))
    (p := (-1 : ℝ)) (by norm_num)
  have key : ∫ x in Set.Ioi (0 : ℝ), x ^ (-(3 : ℝ)) * Real.exp (-(c / x)) =
      ∫ y in Set.Ioi (0 : ℝ), y * Real.exp (-(c * y)) := by
    rw [← hcov]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    have hx0 : 0 < x := hx
    rw [smul_eq_mul, abs_neg, abs_one, one_mul]
    have h1 : (-(3 : ℝ)) = (-1 : ℝ) + ((-1 : ℝ) + (-1 : ℝ)) := by norm_num
    have h2 : ((-1 : ℝ) - 1) = (-1 : ℝ) + (-1 : ℝ) := by norm_num
    rw [Real.rpow_neg_one x]
    rw [h1, Real.rpow_add hx0 (-1 : ℝ) ((-1 : ℝ) + (-1 : ℝ)),
        Real.rpow_add hx0 (-1 : ℝ) (-1 : ℝ), Real.rpow_neg_one x,
        h2, Real.rpow_add hx0 (-1 : ℝ) (-1 : ℝ), Real.rpow_neg_one x]
    rw [div_eq_mul_inv, mul_comm c x⁻¹]
    ring
  rw [key, hbase]

end Work.BoseBoxFock.SqrtKin
