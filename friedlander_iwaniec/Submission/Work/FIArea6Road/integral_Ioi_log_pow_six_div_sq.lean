import Mathlib

namespace Work.FIArea6Road

open MeasureTheory

/-- The substitution `s = exp t` turns `∫_1^∞ (log s)^6 / s^2 ds` into
`∫_0^∞ t^6 e^{-t} dt`. -/
theorem integral_log_pow_six_div_sq_eq_gamma :
    ∫ s in Set.Ioi (1 : ℝ), (Real.log s) ^ (6 : ℕ) / s ^ 2
      = ∫ t in Set.Ioi (0 : ℝ), t ^ (6 : ℕ) * Real.exp (-t) := by
  have step1 : ∫ s in Set.Ioi (1 : ℝ), (Real.log s) ^ (6 : ℕ) / s ^ 2
      = ∫ s in Set.Ioi (1 : ℝ),
          s⁻¹ * ((Real.log s) ^ (6 : ℕ) * Real.exp (-(Real.log s))) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    have hx0 : 0 < x := lt_trans one_pos hx
    simp only [Real.exp_neg, Real.exp_log hx0, div_eq_mul_inv, pow_two, mul_inv]
    ring
  have step2 : (∫ s in Set.Ioi (1 : ℝ),
        s⁻¹ * ((Real.log s) ^ (6 : ℕ) * Real.exp (-(Real.log s))))
      = ∫ t in Set.Ioi (0 : ℝ), t ^ (6 : ℕ) * Real.exp (-t) := by
    have h := MeasureTheory.integral_comp_log_Ioi
      (fun y : ℝ => y ^ (6 : ℕ) * Real.exp (-y)) (show (0 : ℝ) < 1 by norm_num)
    simpa using h
  rw [step1, step2]

/-- `Γ 7 = 6! = 720`. -/
theorem Gamma_seven : Real.Gamma 7 = 720 := by
  rw [show (7 : ℝ) = ((6 : ℕ) : ℝ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
  norm_num

/-- `∫_0^∞ t^6 e^{-t} dt = Γ 7 = 720`, via Mathlib's Gamma integral. -/
theorem integral_rpow_six_mul_exp_neg :
    (∫ t in Set.Ioi (0 : ℝ), t ^ (6 : ℕ) * Real.exp (-t)) = 720 := by
  have hg := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (7 : ℝ)) (r := (1 : ℝ)) (by norm_num) (by norm_num)
  have hcongr : (∫ t in Set.Ioi (0 : ℝ), t ^ (6 : ℕ) * Real.exp (-t))
      = ∫ t in Set.Ioi (0 : ℝ), t ^ ((7 : ℝ) - 1) * Real.exp (-(1 * t)) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t _
    have hp : t ^ ((7 : ℝ) - 1) = t ^ (6 : ℕ) := by
      rw [show (7 : ℝ) - 1 = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    simp only [hp, show (-(1 * t) : ℝ) = -t by ring]
  rw [hcongr, hg, Gamma_seven]
  norm_num

theorem integral_Ioi_log_pow_six_div_sq :
    ∫ s in Set.Ioi (1 : ℝ), (Real.log s) ^ (6 : ℕ) / s ^ 2 = 720 := by
  rw [integral_log_pow_six_div_sq_eq_gamma, integral_rpow_six_mul_exp_neg]

end Work.FIArea6Road
