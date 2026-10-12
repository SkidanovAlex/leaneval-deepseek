import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.Analysis.Integral

open MeasureTheory Set Real

/-- The substitution `t ↦ t⁻¹` turns the integral `∫₀^∞ t ^ (s-1) exp (-(c/t)) dt` into the
Euler-type integral `∫₀^∞ y ^ (-s-1) exp (-(c*y)) dy`. -/
theorem integral_rpow_exp_neg_div_Ioi {s c : ℝ} (hc : 0 < c) (hs : s < 0) :
    (∫ t in Set.Ioi (0 : ℝ), t ^ (s - 1) * Real.exp (-(c / t))) =
      c ^ s * Real.Gamma (-s) := by
  have hne : (-1 : ℝ) ≠ 0 := by norm_num
  have hsub := integral_comp_rpow_Ioi (fun y : ℝ => y ^ (-s - 1) * Real.exp (-(c * y))) hne
  have hpt : ∀ x ∈ Set.Ioi (0 : ℝ),
      (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) *
          ((x ^ (-1 : ℝ)) ^ (-s - 1) * Real.exp (-(c * x ^ (-1 : ℝ))))
        = x ^ (s - 1) * Real.exp (-(c / x)) := by
    intro x hx
    have hx0 : 0 < x := hx
    have hxle : 0 ≤ x := le_of_lt hx0
    rw [abs_neg, abs_one, one_mul]
    rw [← Real.rpow_mul hxle (-1) (-s - 1)]
    have e1 : (-1 : ℝ) * (-s - 1) = s + 1 := by ring
    rw [e1]
    have e2 : (-1 : ℝ) - 1 = -2 := by norm_num
    rw [e2]
    rw [show x ^ (-2 : ℝ) * (x ^ (s + 1) * Real.exp (-(c * x ^ (-1 : ℝ))))
          = (x ^ (-2 : ℝ) * x ^ (s + 1)) * Real.exp (-(c * x ^ (-1 : ℝ))) by ring]
    have e3 : (-2 : ℝ) + (s + 1) = s - 1 := by ring
    rw [← Real.rpow_add hx0 (-2) (s + 1), e3, div_eq_mul_inv, Real.rpow_neg_one]
  have key : (∫ t in Set.Ioi (0 : ℝ), t ^ (s - 1) * Real.exp (-(c / t)))
      = ∫ y in Set.Ioi (0 : ℝ), y ^ (-s - 1) * Real.exp (-(c * y)) := by
    rw [← hsub]
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    exact (hpt x hx).symm
  rw [key, integral_rpow_mul_exp_neg_mul_Ioi (a := -s) (r := c) (by linarith) hc]
  rw [one_div, Real.inv_rpow hc.le, ← Real.rpow_neg hc.le (-s), neg_neg]

theorem integral_heat_coulomb_three {a : ℝ} (ha : 0 < a) :
    (∫ t in Set.Ioi (0 : ℝ), (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * Real.exp (-(a ^ 2 / (4 * t))))
      = 1 / (4 * Real.pi * a) := by
  have hc : 0 < a ^ 2 / 4 := by positivity
  have hpt : ∀ t ∈ Set.Ioi (0 : ℝ),
      (4 * Real.pi * t) ^ (-(3 / 2 : ℝ)) * Real.exp (-(a ^ 2 / (4 * t)))
        = (4 * Real.pi) ^ (-(3 / 2 : ℝ)) *
            (t ^ (-(3 / 2 : ℝ)) * Real.exp (-(a ^ 2 / 4 / t))) := by
    intro t ht
    have ht0 : 0 < t := ht
    rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ 4 * Real.pi) (le_of_lt ht0)]
    rw [show a ^ 2 / (4 * t) = a ^ 2 / 4 / t by ring]
    ring
  have hinner : (∫ t in Set.Ioi (0 : ℝ), t ^ (-(3 / 2 : ℝ)) * Real.exp (-(a ^ 2 / 4 / t)))
      = (a ^ 2 / 4) ^ (-(1 / 2 : ℝ)) * Real.Gamma (1 / 2) := by
    have h := integral_rpow_exp_neg_div_Ioi (s := -(1 / 2 : ℝ)) (c := a ^ 2 / 4) hc (by norm_num)
    rw [show (-(3 / 2 : ℝ)) = -(1 / 2 : ℝ) - 1 by norm_num]
    simpa using h
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul, hinner]
  rw [Real.Gamma_one_half_eq]
  have hsqrtc : (a ^ 2 / 4) ^ (-(1 / 2 : ℝ)) = 2 / a := by
    have ha2 : 0 < a / 2 := by positivity
    rw [show a ^ 2 / 4 = (a / 2) ^ 2 by ring]
    rw [← Real.rpow_two, ← Real.rpow_mul (le_of_lt ha2) 2 (-(1 / 2 : ℝ))]
    rw [show (2 : ℝ) * (-(1 / 2)) = -1 by norm_num, Real.rpow_neg_one, inv_div]
  have hsqrtpi : (4 * Real.pi) ^ (-(3 / 2 : ℝ)) * Real.sqrt Real.pi = 1 / (8 * Real.pi) := by
    have hx : 0 ≤ 4 * Real.pi := by positivity
    have h4pi : Real.sqrt (4 * Real.pi) = 2 * Real.sqrt Real.pi := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4) Real.pi]
      congr 1
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [Real.rpow_neg hx (3/2), Real.rpow_div_two_eq_sqrt (3 : ℝ) hx, h4pi]
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [show (2 * Real.sqrt Real.pi) ^ 3 = 8 * Real.pi * Real.sqrt Real.pi by
      have hs : (Real.sqrt Real.pi) ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
      calc (2 * Real.sqrt Real.pi) ^ 3 = 8 * (Real.sqrt Real.pi) ^ 3 := by ring
        _ = 8 * ((Real.sqrt Real.pi) ^ 2 * Real.sqrt Real.pi) := by ring
        _ = 8 * (Real.pi * Real.sqrt Real.pi) := by rw [hs]
        _ = 8 * Real.pi * Real.sqrt Real.pi := by ring]
    field_simp
  rw [hsqrtc]
  rw [show (4 * Real.pi) ^ (-(3 / 2 : ℝ)) * (2 / a * Real.sqrt Real.pi)
        = ((4 * Real.pi) ^ (-(3 / 2 : ℝ)) * Real.sqrt Real.pi) * (2 / a) by ring]
  rw [hsqrtpi]
  field_simp
  ring

end Commons.Analysis.Integral