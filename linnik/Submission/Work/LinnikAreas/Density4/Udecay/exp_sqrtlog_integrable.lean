import Mathlib

namespace Work.LinnikAreas.Density4.Udecay

/-- Integrability of `u ↦ exp (-(c * sqrt u))` on `(0, ∞)`: substitute `u = x ^ 2`, reducing
to the classical Gamma-type integrability of `x ↦ x * exp (-c * x)`. -/
private lemma integrableOn_Ioi_exp_neg_sqrt {c : ℝ} (hc : 0 < c) :
    MeasureTheory.IntegrableOn (fun u : ℝ => Real.exp (-(c * Real.sqrt u))) (Set.Ioi 0) := by
  have hf : MeasureTheory.IntegrableOn (fun x : ℝ => x ^ (1:ℝ) * Real.exp (-(c * x)))
      (Set.Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1:ℝ)) (s := (1:ℝ)) (b := c)
      (by norm_num) (by norm_num) hc
    simpa using h
  refine (MeasureTheory.integrableOn_Ioi_comp_rpow_iff'
    (fun u : ℝ => Real.exp (-(c * Real.sqrt u))) (p := (2:ℝ)) (by norm_num)).mp ?_
  refine hf.congr_fun ?_ measurableSet_Ioi
  intro x hx
  simp only [smul_eq_mul]
  rw [show (2:ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two, Real.sqrt_sq hx.le]

/-- Integrability of `u ↦ exp (-(c * sqrt u)) * u` on `(0, ∞)`, by the same substitution
`u = x ^ 2`, reducing to the Gamma-type integrability of `x ↦ x ^ 3 * exp (-c * x)`. -/
private lemma integrableOn_Ioi_exp_neg_sqrt_mul_self {c : ℝ} (hc : 0 < c) :
    MeasureTheory.IntegrableOn (fun u : ℝ => Real.exp (-(c * Real.sqrt u)) * u) (Set.Ioi 0) := by
  have hf : MeasureTheory.IntegrableOn (fun x : ℝ => x ^ (3:ℝ) * Real.exp (-(c * x)))
      (Set.Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := (1:ℝ)) (s := (3:ℝ)) (b := c)
      (by norm_num) (by norm_num) hc
    simpa using h
  refine (MeasureTheory.integrableOn_Ioi_comp_rpow_iff'
    (fun u : ℝ => Real.exp (-(c * Real.sqrt u)) * u) (p := (2:ℝ)) (by norm_num)).mp ?_
  refine hf.congr_fun ?_ measurableSet_Ioi
  intro x hx
  simp only [smul_eq_mul]
  rw [show (2:ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two, Real.sqrt_sq hx.le]
  rw [show (3:ℝ) = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  ring

theorem exp_sqrtlog_integrable {c : ℝ} (hc : 0 < c) :
    MeasureTheory.IntegrableOn (fun t : ℝ => Real.exp (-(c * Real.sqrt (Real.log t))) / t) (Set.Ioi 1) ∧
    MeasureTheory.IntegrableOn (fun t : ℝ => Real.exp (-(c * Real.sqrt (Real.log t))) * Real.log t / t)
      (Set.Ioi 1) := by
  have h1 : MeasureTheory.IntegrableOn (fun u : ℝ => Real.exp (-(c * Real.sqrt u)))
      (Set.Ioi 0) := integrableOn_Ioi_exp_neg_sqrt hc
  have h2 : MeasureTheory.IntegrableOn (fun u : ℝ => Real.exp (-(c * Real.sqrt u)) * u)
      (Set.Ioi 0) := integrableOn_Ioi_exp_neg_sqrt_mul_self hc
  constructor
  · refine (MeasureTheory.integrableOn_comp_log_Ioi
      (fun u : ℝ => Real.exp (-(c * Real.sqrt u))) zero_lt_one).mpr (by simpa using h1)
      |>.congr_fun ?_ measurableSet_Ioi
    intro t ht
    simp only [smul_eq_mul, inv_mul_eq_div]
  · refine (MeasureTheory.integrableOn_comp_log_Ioi
      (fun u : ℝ => Real.exp (-(c * Real.sqrt u)) * u) zero_lt_one).mpr (by simpa using h2)
      |>.congr_fun ?_ measurableSet_Ioi
    intro t ht
    simp only [smul_eq_mul, inv_mul_eq_div]

end Work.LinnikAreas.Density4.Udecay
