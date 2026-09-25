import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace Commons.Analysis.Real

open MeasureTheory Set intervalIntegral

theorem integral_log_mul_psiKfun_le_of_exp_one_le {x Y : ℝ} (hx : Real.exp 1 ≤ x) (hxY : x ≤ Y) :
    (∫ t in x..Y, Real.log t * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))) ≤ 2 / x := by
  have hexp1 : (1 : ℝ) < Real.exp 1 := by
    rw [Real.one_lt_exp_iff]; norm_num
  have hx1 : (1 : ℝ) < x := lt_of_lt_of_le hexp1 hx
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx1
  have hY0 : (0 : ℝ) < Y := lt_of_lt_of_le hx0 hxY
  -- `log t ≥ 1` for `t ∈ [x,Y]`
  have hlog1 : ∀ t ∈ Set.Icc x Y, (1 : ℝ) ≤ Real.log t := by
    intro t ht
    have h := Real.log_le_log (Real.exp_pos 1) (le_trans hx ht.1)
    simpa using h
  have hlogcont : ContinuousOn (fun t : ℝ => Real.log t) (Set.Icc x Y) := by
    intro t ht
    exact (Real.continuousAt_log (ne_of_gt (lt_of_lt_of_le hx0 ht.1))).continuousWithinAt
  have hf_cont : ContinuousOn
      (fun t : ℝ => Real.log t * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)))
      (Set.Icc x Y) := by
    apply ContinuousOn.mul hlogcont
    apply ContinuousOn.div
    · exact hlogcont.add_const 1
    · exact (continuousOn_id.pow 2).mul (hlogcont.pow 2)
    · intro t ht
      exact mul_ne_zero (pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le hx0 ht.1)))
        (pow_ne_zero 2 (ne_of_gt (Real.log_pos (lt_of_lt_of_le hx1 ht.1))))
  have hg_cont : ContinuousOn (fun t : ℝ => 2 * (t ^ 2)⁻¹) (Set.Icc x Y) := by
    apply ContinuousOn.const_mul
    apply ContinuousOn.inv₀ (continuousOn_id.pow 2)
    intro t ht
    exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le hx0 ht.1))
  have hf_int : IntervalIntegrable
      (fun t : ℝ => Real.log t * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)))
      volume x Y := hf_cont.intervalIntegrable_of_Icc hxY
  have hg_int : IntervalIntegrable (fun t : ℝ => 2 * (t ^ 2)⁻¹) volume x Y :=
    hg_cont.intervalIntegrable_of_Icc hxY
  -- pointwise bound
  have hpoint : ∀ t ∈ Set.Icc x Y,
      Real.log t * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)) ≤ 2 * (t ^ 2)⁻¹ := by
    intro t ht
    have ht1 : (1 : ℝ) < t := lt_of_lt_of_le hx1 ht.1
    have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht1
    have hlt : (1 : ℝ) ≤ Real.log t := hlog1 t ht
    have hlogt : (0 : ℝ) < Real.log t := Real.log_pos ht1
    have ht2 : (t ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 (ne_of_gt ht0)
    have hden : (0 : ℝ) < t ^ 2 * (Real.log t) ^ 2 := by positivity
    rw [mul_div_assoc']
    rw [div_le_iff₀ hden]
    have hstep : (t ^ 2)⁻¹ * (t ^ 2 * (Real.log t) ^ 2) = (Real.log t) ^ 2 := by
      rw [← mul_assoc, inv_mul_cancel₀ ht2, one_mul]
    have hR : (2 : ℝ) * (t ^ 2)⁻¹ * (t ^ 2 * (Real.log t) ^ 2) = 2 * (Real.log t) ^ 2 := by
      calc (2 : ℝ) * (t ^ 2)⁻¹ * (t ^ 2 * (Real.log t) ^ 2)
          = 2 * ((t ^ 2)⁻¹ * (t ^ 2 * (Real.log t) ^ 2)) := by rw [mul_assoc]
        _ = 2 * (Real.log t) ^ 2 := by rw [hstep]
    rw [hR]
    have hll : Real.log t * 1 ≤ Real.log t * Real.log t :=
      mul_le_mul_of_nonneg_left hlt (le_of_lt hlogt)
    nlinarith [hll]
  have hmono := integral_mono_on hxY hf_int hg_int hpoint
  have hderiv : ∀ t ∈ Set.uIcc x Y,
      HasDerivAt (fun s : ℝ => -(2 * s⁻¹)) (2 * (t ^ 2)⁻¹) t := by
    intro t ht
    rw [Set.uIcc_of_le hxY] at ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le hx0 ht.1)
    have h := ((hasDerivAt_inv ht0).const_mul 2).neg
    refine h.congr_deriv ?_
    ring
  have hFTC : (∫ t in x..Y, 2 * (t ^ 2)⁻¹)
      = (fun s : ℝ => -(2 * s⁻¹)) Y - (fun s : ℝ => -(2 * s⁻¹)) x :=
    integral_eq_sub_of_hasDerivAt hderiv hg_int
  have hval : (fun s : ℝ => -(2 * s⁻¹)) Y - (fun s : ℝ => -(2 * s⁻¹)) x = 2 / x - 2 / Y := by
    simp only
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring
  calc (∫ t in x..Y, Real.log t * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)))
      ≤ ∫ t in x..Y, 2 * (t ^ 2)⁻¹ := hmono
    _ = (fun s : ℝ => -(2 * s⁻¹)) Y - (fun s : ℝ => -(2 * s⁻¹)) x := hFTC
    _ = 2 / x - 2 / Y := hval
    _ ≤ 2 / x := by
        have : 0 ≤ 2 / Y := by positivity
        linarith

end Commons.Analysis.Real