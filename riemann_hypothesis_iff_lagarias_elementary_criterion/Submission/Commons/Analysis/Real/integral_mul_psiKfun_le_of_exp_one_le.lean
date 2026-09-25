import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace Commons.Analysis.Real

open MeasureTheory Set intervalIntegral

/-- `Real.log` is continuous on `[x,Y]` as soon as `0 < x`. -/
private lemma log_contOn_Icc_of_pos (x Y : ℝ) (hx : 0 < x) :
    ContinuousOn (fun t : ℝ => Real.log t) (Set.Icc x Y) := by
  intro t ht
  exact (Real.continuousAt_log (ne_of_gt (lt_of_lt_of_le hx ht.1))).continuousWithinAt

/-- For `exp 1 ≤ x ≤ Y`, the integral of `t ↦ t (log t + 1)/(t² log²t)` over `[x,Y]` is at most
`2 (log log Y - log log x)`.

Pointwise, for `t ∈ [x,Y]` we have `log t ≥ 1`, so `t (log t + 1)/(t² log²t) =
(log t + 1)/(t log²t) ≤ 2/(t log t)`; the latter has primitive `2 log log t`. -/
theorem integral_mul_psiKfun_le_of_exp_one_le {x Y : ℝ} (hx : Real.exp 1 ≤ x) (hxY : x ≤ Y) :
    (∫ t in x..Y, t * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))) ≤
      2 * (Real.log (Real.log Y) - Real.log (Real.log x)) := by
  have hexp1 : (1 : ℝ) < Real.exp 1 := by rw [Real.one_lt_exp_iff]; norm_num
  have hx1 : (1 : ℝ) < x := lt_of_lt_of_le hexp1 hx
  have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx1
  -- `log t ≥ 1` for `t ∈ [x,Y]`
  have hlog1 : ∀ t ∈ Set.Icc x Y, (1 : ℝ) ≤ Real.log t := by
    intro t ht
    have h : Real.log (Real.exp 1) ≤ Real.log t :=
      Real.log_le_log (Real.exp_pos 1) (le_trans hx ht.1)
    simpa using h
  have hlogcont : ContinuousOn (fun t : ℝ => Real.log t) (Set.Icc x Y) :=
    log_contOn_Icc_of_pos x Y hx0
  -- continuity of the two integrands on `[x,Y]`
  have hf_cont :
      ContinuousOn (fun t : ℝ => t * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)))
        (Set.Icc x Y) := by
    apply ContinuousOn.mul continuousOn_id
    apply ContinuousOn.div
    · exact hlogcont.add_const 1
    · exact (continuousOn_id.pow 2).mul (hlogcont.pow 2)
    · intro t ht
      have ht0 : 0 < t := lt_of_lt_of_le hx0 ht.1
      exact mul_ne_zero (pow_ne_zero 2 (ne_of_gt ht0))
        (pow_ne_zero 2 (ne_of_gt (Real.log_pos (lt_of_lt_of_le hx1 ht.1))))
  have hg_cont : ContinuousOn (fun t : ℝ => 2 * (t * Real.log t)⁻¹) (Set.Icc x Y) := by
    apply ContinuousOn.const_mul
    apply ContinuousOn.inv₀
    · exact continuousOn_id.mul hlogcont
    · intro t ht
      have ht0 : 0 < t := lt_of_lt_of_le hx0 ht.1
      exact mul_ne_zero (ne_of_gt ht0) (ne_of_gt (Real.log_pos (lt_of_lt_of_le hx1 ht.1)))
  have hf_int :
      IntervalIntegrable (fun t : ℝ => t * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)))
        volume x Y :=
    hf_cont.intervalIntegrable_of_Icc hxY
  have hg_int : IntervalIntegrable (fun t : ℝ => 2 * (t * Real.log t)⁻¹) volume x Y :=
    hg_cont.intervalIntegrable_of_Icc hxY
  -- pointwise comparison
  have hpoint : ∀ t ∈ Set.Icc x Y,
      t * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)) ≤ 2 * (t * Real.log t)⁻¹ := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le hx0 ht.1
    have hlogt : (1 : ℝ) ≤ Real.log t := hlog1 t ht
    have hden : (0 : ℝ) < t ^ 2 * (Real.log t) ^ 2 := by positivity
    have hrewrite : t * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))
        = (t * (Real.log t + 1)) / (t ^ 2 * (Real.log t) ^ 2) := by ring
    rw [hrewrite, div_le_iff₀ hden]
    have h2 : 2 * (t * Real.log t)⁻¹ * (t ^ 2 * (Real.log t) ^ 2) = 2 * t * Real.log t := by
      field_simp
    rw [h2]
    have hmul : t * 1 ≤ t * Real.log t := mul_le_mul_of_nonneg_left hlogt (le_of_lt ht0)
    nlinarith [hmul]
  have hmono :
      (∫ t in x..Y, t * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)))
        ≤ ∫ t in x..Y, 2 * (t * Real.log t)⁻¹ :=
    integral_mono_on hxY hf_int hg_int hpoint
  -- the primitive of `2/(t log t)` is `2 log log t`
  have hderiv : ∀ t ∈ Set.uIcc x Y,
      HasDerivAt (fun s : ℝ => 2 * Real.log (Real.log s)) (2 * (t * Real.log t)⁻¹) t := by
    intro t ht
    rw [Set.uIcc_of_le hxY] at ht
    have ht1 : (1 : ℝ) < t := lt_of_lt_of_le hx1 ht.1
    have ht0 : t ≠ 0 := ne_of_gt (lt_trans zero_lt_one ht1)
    have hlogt0 : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht1)
    have h1 : HasDerivAt Real.log t⁻¹ t := Real.hasDerivAt_log ht0
    have h2 : HasDerivAt Real.log (Real.log t)⁻¹ (Real.log t) := Real.hasDerivAt_log hlogt0
    have h3 : HasDerivAt (fun s : ℝ => Real.log (Real.log s)) ((Real.log t)⁻¹ * t⁻¹) t :=
      h2.comp t h1
    have h4 : HasDerivAt (fun s : ℝ => 2 * Real.log (Real.log s))
        (2 * ((Real.log t)⁻¹ * t⁻¹)) t := h3.const_mul 2
    refine h4.congr_deriv ?_
    rw [mul_inv_rev]
  have hftc :
      (∫ t in x..Y, 2 * (t * Real.log t)⁻¹)
        = 2 * Real.log (Real.log Y) - 2 * Real.log (Real.log x) := by
    have h := integral_eq_sub_of_hasDerivAt hderiv hg_int
    simpa using h
  calc (∫ t in x..Y, t * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)))
      ≤ ∫ t in x..Y, 2 * (t * Real.log t)⁻¹ := hmono
    _ = 2 * Real.log (Real.log Y) - 2 * Real.log (Real.log x) := hftc
    _ = 2 * (Real.log (Real.log Y) - Real.log (Real.log x)) := by ring

end Commons.Analysis.Real