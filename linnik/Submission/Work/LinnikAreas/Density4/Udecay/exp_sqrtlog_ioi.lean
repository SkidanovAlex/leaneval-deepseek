import Mathlib

namespace Work.LinnikAreas.Density4.Udecay

open MeasureTheory Filter
open scoped Topology

theorem exp_sqrtlog_ioi {c : ℝ} (hc : 0 < c) {x : ℝ} (hx : 1 ≤ x) :
    ∫ t in Set.Ioi x, Real.exp (-(c * Real.sqrt (Real.log t))) / t
      = (2 / c) * (Real.sqrt (Real.log x) + 1 / c) * Real.exp (-(c * Real.sqrt (Real.log x))) := by
  have hxpos : (0 : ℝ) < x := by linarith
  have hxne : x ≠ 0 := ne_of_gt hxpos
  have hcx : c ≠ 0 := ne_of_gt hc
  -- Continuity of the antiderivative at `x` within `[x, ∞)`.
  have hcont : ContinuousWithinAt
      (fun t : ℝ => -2 * Real.exp (-(c * Real.sqrt (Real.log t))) *
        (Real.sqrt (Real.log t) / c + 1 / c ^ 2)) (Set.Ici x) x := by
    have hlog : ContinuousWithinAt Real.log (Set.Ici x) x :=
      (Real.continuousAt_log hxne).continuousWithinAt
    have hsqrt : ContinuousWithinAt (fun t => Real.sqrt (Real.log t)) (Set.Ici x) x :=
      Real.continuous_sqrt.continuousAt.comp_continuousWithinAt hlog
    have h1 : ContinuousWithinAt (fun t => Real.exp (-(c * Real.sqrt (Real.log t))))
        (Set.Ici x) x :=
      Real.continuous_exp.continuousAt.comp_continuousWithinAt ((hsqrt.const_mul c).neg)
    have h2 : ContinuousWithinAt (fun t => Real.sqrt (Real.log t) / c + 1 / c ^ 2)
        (Set.Ici x) x :=
      (hsqrt.div_const c).add_const (1 / c ^ 2)
    exact h1.const_mul (-2) |>.mul h2
  -- Derivative of the antiderivative on `(x, ∞)`.
  have hderiv : ∀ t ∈ Set.Ioi x,
      HasDerivAt (fun t : ℝ => -2 * Real.exp (-(c * Real.sqrt (Real.log t))) *
        (Real.sqrt (Real.log t) / c + 1 / c ^ 2))
        (Real.exp (-(c * Real.sqrt (Real.log t))) / t) t := by
    intro t ht
    have ht1 : (1 : ℝ) < t := lt_of_le_of_lt hx ht
    have ht0 : t ≠ 0 := by linarith
    have hlpos : 0 < Real.log t := Real.log_pos ht1
    have hlne : Real.log t ≠ 0 := ne_of_gt hlpos
    have hlog : HasDerivAt Real.log t⁻¹ t := Real.hasDerivAt_log ht0
    have hsqrt : HasDerivAt (fun t => Real.sqrt (Real.log t))
        (t⁻¹ / (2 * Real.sqrt (Real.log t))) t := hlog.sqrt hlne
    have hY : HasDerivAt (fun t => Real.sqrt (Real.log t) / c + 1 / c ^ 2)
        ((t⁻¹ / (2 * Real.sqrt (Real.log t))) / c) t :=
      (hsqrt.div_const c).add_const (1 / c ^ 2)
    have hw : HasDerivAt (fun t => -(c * Real.sqrt (Real.log t)))
        (-(c * (t⁻¹ / (2 * Real.sqrt (Real.log t))))) t :=
      (hsqrt.const_mul c).neg
    have hX : HasDerivAt (fun t => Real.exp (-(c * Real.sqrt (Real.log t))))
        (Real.exp (-(c * Real.sqrt (Real.log t))) *
          (-(c * (t⁻¹ / (2 * Real.sqrt (Real.log t)))))) t := hw.exp
    have hf := (hX.const_mul (-2)).mul hY
    have heq : -2 * (Real.exp (-(c * Real.sqrt (Real.log t))) *
          -(c * (t⁻¹ / (2 * Real.sqrt (Real.log t))))) *
            (Real.sqrt (Real.log t) / c + 1 / c ^ 2)
        + -2 * Real.exp (-(c * Real.sqrt (Real.log t))) *
            (t⁻¹ / (2 * Real.sqrt (Real.log t)) / c)
        = Real.exp (-(c * Real.sqrt (Real.log t))) / t := by
      field_simp
      ring
    exact hf.congr_deriv heq
  -- Non-negativity of the integrand on `(x, ∞)`.
  have hpos : ∀ t ∈ Set.Ioi x, 0 ≤ Real.exp (-(c * Real.sqrt (Real.log t))) / t := by
    intro t ht
    have hxt : x < t := ht
    have htpos : (0 : ℝ) < t := lt_trans hxpos hxt
    positivity
  -- The antiderivative tends to 0 at `+∞`.
  have hlim : Tendsto
      (fun t : ℝ => -2 * Real.exp (-(c * Real.sqrt (Real.log t))) *
        (Real.sqrt (Real.log t) / c + 1 / c ^ 2)) atTop (nhds 0) := by
    have hS : Tendsto (fun t : ℝ => Real.sqrt (Real.log t)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
    have h1 : Tendsto (fun t : ℝ =>
        Real.sqrt (Real.log t) * Real.exp (-(c * Real.sqrt (Real.log t)))) atTop (nhds 0) := by
      have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 c hc).comp hS
      convert h using 1
      ext t
      simp [Real.rpow_one]
    have h2 : Tendsto (fun t : ℝ => Real.exp (-(c * Real.sqrt (Real.log t))))
        atTop (nhds 0) := by
      have hcs : Tendsto (fun t : ℝ => c * Real.sqrt (Real.log t)) atTop atTop :=
        Filter.Tendsto.const_mul_atTop hc hS
      exact Real.tendsto_exp_neg_atTop_nhds_zero.comp hcs
    have key : Tendsto (fun t : ℝ =>
        (-2 / c) * (Real.sqrt (Real.log t) * Real.exp (-(c * Real.sqrt (Real.log t))))
        + (-2 / c ^ 2) * Real.exp (-(c * Real.sqrt (Real.log t)))) atTop (nhds 0) := by
      have h := (Filter.Tendsto.const_mul (-2 / c) h1).add
        (Filter.Tendsto.const_mul (-2 / c ^ 2) h2)
      simpa using h
    refine key.congr' (Eventually.of_forall (fun t => ?_))
    ring
  have hmain := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg hcont hderiv hpos hlim
  rw [hmain]
  have hfinal : (0 : ℝ) - (-2 * Real.exp (-(c * Real.sqrt (Real.log x))) *
        (Real.sqrt (Real.log x) / c + 1 / c ^ 2))
      = (2 / c) * (Real.sqrt (Real.log x) + 1 / c) * Real.exp (-(c * Real.sqrt (Real.log x))) := by
    field_simp
    ring
  exact hfinal

end Work.LinnikAreas.Density4.Udecay
