import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace Commons.Analysis.Real

open MeasureTheory Set

theorem integral_psiKfun_le {x Y : ℝ} (hx : 1 < x) (hxY : x ≤ Y) :
    (∫ t in x..Y, (Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)) ≤ 2 / (x * Real.log x) := by
  have hxpos : 0 < x := lt_trans zero_lt_one hx
  have hYpos : 0 < Y := lt_of_lt_of_le hxpos hxY
  have hY1 : 1 < Y := lt_of_lt_of_le hx hxY
  have hlogx_pos : 0 < Real.log x := Real.log_pos hx
  have hlogY_pos : 0 < Real.log Y := Real.log_pos hY1
  -- antiderivative and its derivative
  have hderiv : ∀ t ∈ Set.uIcc x Y,
      HasDerivAt (fun s : ℝ => -((s * Real.log s)⁻¹))
        ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)) t := by
    intro t ht
    rw [Set.uIcc_of_le hxY] at ht
    have ht1 : 1 < t := lt_of_lt_of_le hx ht.1
    have htpos : 0 < t := lt_trans zero_lt_one ht1
    have hlogt_pos : 0 < Real.log t := Real.log_pos ht1
    have hlogt_ne : Real.log t ≠ 0 := ne_of_gt hlogt_pos
    have hmt : HasDerivAt (fun s : ℝ => s * Real.log s) (Real.log t + 1) t := by
      have h := (hasDerivAt_id t).mul (Real.hasDerivAt_log (ne_of_gt htpos))
      have h2 : HasDerivAt (fun s : ℝ => s * Real.log s) (1 * Real.log t + t * t⁻¹) t := h
      rw [one_mul, mul_inv_cancel₀ (ne_of_gt htpos)] at h2
      exact h2
    have hne : t * Real.log t ≠ 0 := mul_ne_zero (ne_of_gt htpos) hlogt_ne
    have hd := hmt.inv hne
    have hd2 : HasDerivAt (fun s : ℝ => (s * Real.log s)⁻¹)
        (-(Real.log t + 1) / (t * Real.log t) ^ 2) t := hd
    have hd3 := hd2.neg
    refine hd3.congr_deriv ?_
    ring_nf
  -- integrability of the integrand
  have hint : IntervalIntegrable (fun t : ℝ => (Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))
      volume x Y := by
    apply ContinuousOn.intervalIntegrable_of_Icc hxY
    have hlog_cont : ContinuousOn (fun t : ℝ => Real.log t) (Set.Icc x Y) := by
      apply Real.continuousOn_log.mono
      intro t ht
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ne_of_gt (lt_of_lt_of_le hxpos ht.1)
    apply ContinuousOn.div
    · exact hlog_cont.add continuousOn_const
    · exact (continuousOn_id' (Set.Icc x Y)).pow 2 |>.mul (hlog_cont.pow 2)
    · intro t ht
      have ht1 : 1 < t := lt_of_lt_of_le hx ht.1
      have htpos : 0 < t := lt_trans zero_lt_one ht1
      have hlogt_pos : 0 < Real.log t := Real.log_pos ht1
      exact mul_ne_zero (pow_ne_zero 2 (ne_of_gt htpos)) (pow_ne_zero 2 (ne_of_gt hlogt_pos))
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [hfund]
  -- bound the difference by the first term
  have hA : 0 ≤ (Y * Real.log Y)⁻¹ :=
    inv_nonneg.mpr (le_of_lt (mul_pos hYpos hlogY_pos))
  have hB : 0 < (x * Real.log x)⁻¹ :=
    inv_pos.mpr (mul_pos hxpos hlogx_pos)
  calc -(Y * Real.log Y)⁻¹ - -((x * Real.log x)⁻¹)
      = (x * Real.log x)⁻¹ - (Y * Real.log Y)⁻¹ := by ring
    _ ≤ (x * Real.log x)⁻¹ := by linarith
    _ ≤ 2 / (x * Real.log x) := by
        rw [div_eq_mul_inv]
        linarith

end Commons.Analysis.Real