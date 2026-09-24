import Mathlib

namespace Work.NumberTheory.Chen.APSwitchUpper

/-- Antiderivative used for `integral_L2lo`. -/
private noncomputable def L2loF (u : ℝ) : ℝ :=
  -18/(u + 4)^2 + 9/(u + 4) + (15/4)*Real.log (u + 4) - (13/12)*Real.log u

/-- The derivative of `L2loF`, written in partial-fraction form. -/
private noncomputable def L2log (u : ℝ) : ℝ :=
  36/(u+4)^3 - 9/(u+4)^2 + (15/4)/(u+4) - (13/12)/u

private lemma hasDerivAt_L2loF (x : ℝ) (hx0 : x ≠ 0) (hx4 : x + 4 ≠ 0) :
    HasDerivAt L2loF (L2log x) x := by
  unfold L2loF L2log
  have hbase : HasDerivAt (fun u : ℝ => u + 4) 1 x := by
    simpa using (hasDerivAt_id x).add_const 4
  have hden : ((x+4)^2 : ℝ) ≠ 0 := by positivity
  have h1 : HasDerivAt (fun u : ℝ => -18/(u + 4)^2) _ x :=
    (hasDerivAt_const x (-18:ℝ)).div (hbase.pow 2) hden
  have h2 : HasDerivAt (fun u : ℝ => 9/(u + 4)) ((0 * (x+4) - 9 * 1) / (x+4)^2) x :=
    (hasDerivAt_const x (9:ℝ)).div hbase hx4
  have h3 : HasDerivAt (fun u : ℝ => (15/4)*Real.log (u + 4)) ((15/4)*(1/(x+4))) x :=
    (hbase.log hx4).const_mul (15/4)
  have h4 : HasDerivAt (fun u : ℝ => (13/12)*Real.log u) ((13/12)*(x⁻¹)) x :=
    ((Real.hasDerivAt_log hx0).const_mul (13/12))
  refine ((h1.add h2).add h3 |>.sub h4).congr_deriv ?_
  field_simp
  ring

private lemma continuousOn_L2log :
    ContinuousOn L2log (Set.Icc (2:ℝ) 4) := by
  unfold L2log
  have hpoly : ContinuousOn (fun u : ℝ => u + 4) (Set.Icc (2:ℝ) 4) :=
    (continuous_id.add continuous_const).continuousOn
  have hz4 : ∀ x ∈ Set.Icc (2:ℝ) 4, x + 4 ≠ 0 := fun x hx => by linarith [hx.1]
  have hz0 : ∀ x ∈ Set.Icc (2:ℝ) 4, x ≠ 0 := fun x hx => by linarith [hx.1]
  have hc1 : ContinuousOn (fun u : ℝ => (36:ℝ)/(u+4)^3) (Set.Icc 2 4) :=
    ContinuousOn.div continuousOn_const (hpoly.pow 3) (fun x hx => pow_ne_zero 3 (hz4 x hx))
  have hc2 : ContinuousOn (fun u : ℝ => (9:ℝ)/(u+4)^2) (Set.Icc 2 4) :=
    ContinuousOn.div continuousOn_const (hpoly.pow 2) (fun x hx => pow_ne_zero 2 (hz4 x hx))
  have hc3 : ContinuousOn (fun u : ℝ => (15/4:ℝ)/(u+4)) (Set.Icc 2 4) :=
    ContinuousOn.div continuousOn_const hpoly hz4
  have hc4 : ContinuousOn (fun u : ℝ => (13/12:ℝ)/u) (Set.Icc 2 4) :=
    ContinuousOn.div continuousOn_const (continuous_id.continuousOn) hz0
  exact ((hc1.sub hc2).add hc3).sub hc4

theorem integral_L2lo :
    ∫ u in (2 : ℝ)..4, (2 * ((u - 2) / (u + 4)) + (2 / 3 : ℝ) * ((u - 2) / (u + 4)) ^ 3) / u
      = -5 / 32 + (77 / 12 : ℝ) * Real.log 2 - (15 / 4 : ℝ) * Real.log 3 := by
  have hderiv : ∀ x ∈ Set.uIcc (2:ℝ) 4, HasDerivAt L2loF (L2log x) x := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (2:ℝ) ≤ 4)] at hx
    exact hasDerivAt_L2loF x (by linarith [hx.1]) (by linarith [hx.1])
  have hint : IntervalIntegrable L2log MeasureTheory.volume (2:ℝ) 4 :=
    ContinuousOn.intervalIntegrable_of_Icc (by norm_num) continuousOn_L2log
  have hFTC : ∫ u in (2:ℝ)..4, L2log u = L2loF 4 - L2loF 2 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hcongr :
      ∫ u in (2 : ℝ)..4, (2 * ((u - 2) / (u + 4)) + (2 / 3 : ℝ) * ((u - 2) / (u + 4)) ^ 3) / u
        = ∫ u in (2:ℝ)..4, L2log u := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (2:ℝ) ≤ 4)] at hx
    have hx0 : x ≠ 0 := by linarith [hx.1]
    have hx4 : x + 4 ≠ 0 := by linarith [hx.1]
    unfold L2log
    field_simp
    ring
  rw [hcongr, hFTC]
  unfold L2loF
  have h8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8:ℝ) = 2^3 by norm_num, Real.log_pow]; norm_num
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
  have h6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [show (6:ℝ) = 2*3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  norm_num only [Real.log_pow]
  rw [h8, h4, h6]
  ring

end Work.NumberTheory.Chen.APSwitchUpper
