import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace Commons.Analysis.Real

open MeasureTheory Set intervalIntegral

/-- For `t ≠ 0` with `log t ≠ 0`,
`t * (log t)^2 * ((log t + 1)/(t^2 * (log t)^2)) = (log t + 1)/t`. -/
private lemma mul_logsq_mul_div_eq (t : ℝ) (ht0 : t ≠ 0) (hlogt0 : Real.log t ≠ 0) :
    t * (Real.log t) ^ 2 * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)) =
      (Real.log t + 1) / t := by
  field_simp

/-- For `exp 1 ≤ x ≤ Y`, the integral `∫_x^Y t (log t)^2 ((log t + 1)/(t^2 (log t)^2))` is at
most `2 (log Y)^2`.

On `[x,Y]` we have `log t ≥ 1`, so the integrand equals `(log t + 1)/t ≤ (log Y + 1)/t`; the latter
has primitive `(log Y + 1) log t`, giving `∫_x^Y (log Y+1)/t = (log Y+1)(log Y - log x)`. Since
`log x ≥ 1` and `log Y ≥ 1`, this is at most `(log Y + 1) log Y ≤ 2 (log Y)^2`. -/
theorem integral_mul_logsq_mul_psiKfun_le {x Y : ℝ} (hx : Real.exp 1 ≤ x) (hxY : x ≤ Y) :
    (∫ t in x..Y, t * (Real.log t) ^ 2 * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))) ≤
      2 * (Real.log Y) ^ 2 := by
  have hexp1 : (1 : ℝ) < Real.exp 1 := by rw [Real.one_lt_exp_iff]; norm_num
  have hx1 : (1 : ℝ) < x := lt_of_lt_of_le hexp1 hx
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx1
  have hlogx1 : (1 : ℝ) ≤ Real.log x := by
    have h : Real.log (Real.exp 1) ≤ Real.log x := Real.log_le_log (Real.exp_pos 1) hx
    simpa using h
  have hlogY1 : (1 : ℝ) ≤ Real.log Y := by
    have h : Real.log x ≤ Real.log Y := Real.log_le_log hx0 hxY
    linarith
  have hlogcont : ContinuousOn (fun t : ℝ => Real.log t) (Set.Icc x Y) := by
    intro t ht
    exact (Real.continuousAt_log (ne_of_gt (lt_of_lt_of_le hx0 ht.1))).continuousWithinAt
  have hf_cont : ContinuousOn
      (fun t : ℝ => t * (Real.log t) ^ 2 * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)))
      (Set.Icc x Y) := by
    apply ContinuousOn.mul
    · exact continuousOn_id.mul (hlogcont.pow 2)
    · apply ContinuousOn.div
      · exact hlogcont.add_const 1
      · exact (continuousOn_id.pow 2).mul (hlogcont.pow 2)
      · intro t ht
        exact mul_ne_zero (pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le hx0 ht.1)))
          (pow_ne_zero 2 (ne_of_gt (Real.log_pos (lt_of_lt_of_le hx1 ht.1))))
  have hg_cont : ContinuousOn (fun t : ℝ => (Real.log Y + 1) / t) (Set.Icc x Y) := by
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro t ht
    exact ne_of_gt (lt_of_lt_of_le hx0 ht.1)
  have hf_int : IntervalIntegrable
      (fun t : ℝ => t * (Real.log t) ^ 2 * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)))
      volume x Y := hf_cont.intervalIntegrable_of_Icc hxY
  have hg_int : IntervalIntegrable (fun t : ℝ => (Real.log Y + 1) / t) volume x Y :=
    hg_cont.intervalIntegrable_of_Icc hxY
  have hpoint : ∀ t ∈ Set.Icc x Y,
      t * (Real.log t) ^ 2 * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))
        ≤ (Real.log Y + 1) / t := by
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le hx0 ht.1
    have hlt : (1 : ℝ) < t := lt_of_lt_of_le hx1 ht.1
    have hlogt0 : Real.log t ≠ 0 := ne_of_gt (Real.log_pos hlt)
    rw [mul_logsq_mul_div_eq t (ne_of_gt ht0) hlogt0]
    apply div_le_div_of_nonneg_right _ (le_of_lt ht0)
    have h : Real.log t ≤ Real.log Y := Real.log_le_log ht0 ht.2
    linarith
  have hmono := integral_mono_on hxY hf_int hg_int hpoint
  have hderiv : ∀ t ∈ Set.uIcc x Y,
      HasDerivAt (fun s : ℝ => (Real.log Y + 1) * Real.log s) ((Real.log Y + 1) / t) t := by
    intro t ht
    rw [Set.uIcc_of_le hxY] at ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le hx0 ht.1)
    have h : HasDerivAt (fun s : ℝ => (Real.log Y + 1) * Real.log s)
        ((Real.log Y + 1) * t⁻¹) t := (Real.hasDerivAt_log ht0).const_mul (Real.log Y + 1)
    rwa [div_eq_mul_inv]
  have hftc : (∫ t in x..Y, (Real.log Y + 1) / t)
      = (Real.log Y + 1) * Real.log Y - (Real.log Y + 1) * Real.log x :=
    integral_eq_sub_of_hasDerivAt hderiv hg_int
  refine le_trans hmono ?_
  rw [hftc]
  have hL1 : (1 : ℝ) ≤ Real.log Y := hlogY1
  have hLsq : Real.log Y ≤ (Real.log Y) ^ 2 := by nlinarith [hL1]
  have hx0' : 0 ≤ Real.log x := le_trans zero_le_one hlogx1
  have hstep : (Real.log Y + 1) * Real.log Y - (Real.log Y + 1) * Real.log x
      ≤ (Real.log Y + 1) * Real.log Y := by nlinarith [hlogY1, hx0']
  nlinarith [hstep, hLsq, hL1]

end Commons.Analysis.Real