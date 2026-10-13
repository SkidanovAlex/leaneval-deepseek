import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllipticEst.remov.integral_sub_rpow_neg

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov.SourceBound

open MeasureTheory

/-- Near `π / 2` the function `t ↦ 1 / (sin t ^ 2 * cos t ^ 3)` behaves like
`(π / 2 - t) ^ (-3)`, so its integral up to `b < π / 2` is `O((π / 2 - b) ^ (-2))`. -/
theorem integral_invSinSqCosCu_right :
    ∃ K : ℝ, 0 < K ∧ ∀ b : ℝ, Real.pi / 4 ≤ b → b < Real.pi / 2 →
      ∫ t in (Real.pi / 4)..b, 1 / (Real.sin t ^ 2 * Real.cos t ^ 3)
        ≤ K / (Real.pi / 2 - b) ^ 2 := by
  refine ⟨Real.pi ^ 3 / 4 + 1, by positivity, ?_⟩
  intro b hb1 hb2
  have hpi : 0 < Real.pi := Real.pi_pos
  -- Pointwise comparison on `[π / 4, b]`.
  have hpt : ∀ t ∈ Set.Icc (Real.pi / 4) b,
      1 / (Real.sin t ^ 2 * Real.cos t ^ 3) ≤ (Real.pi ^ 3 / 2) / (Real.pi / 2 - t) ^ 3 := by
    intro t ht
    have ht0 : 0 ≤ t := by linarith [ht.1, hpi]
    have htp2 : t < Real.pi / 2 := lt_of_le_of_lt ht.2 hb2
    have hu_pos : 0 < Real.pi / 2 - t := by linarith
    have hu_nonneg : 0 ≤ Real.pi / 2 - t := le_of_lt hu_pos
    have hu_le : Real.pi / 2 - t ≤ Real.pi / 2 := by linarith [ht0, hpi]
    -- `sin t ≥ 1 / 2`
    have hsin_ge : (1 : ℝ) / 2 ≤ Real.sin t := by
      have h1 := Real.mul_le_sin ht0 (le_of_lt htp2)
      have h2 : (1 : ℝ) / 2 ≤ 2 / Real.pi * t := by
        have h3 : 2 / Real.pi * (Real.pi / 4) = (1 : ℝ) / 2 := by field_simp; ring
        rw [← h3]
        exact mul_le_mul_of_nonneg_left ht.1 (by positivity)
      linarith
    have hsin_nonneg : 0 ≤ Real.sin t := by linarith
    have hsin_sq : (1 : ℝ) / 4 ≤ Real.sin t ^ 2 := by
      nlinarith [sq_nonneg (Real.sin t - 1 / 2), hsin_ge]
    -- `cos t ≥ (2 / π) (π / 2 - t)`
    have hcos_ge : 2 / Real.pi * (Real.pi / 2 - t) ≤ Real.cos t := by
      have h := Real.mul_le_sin hu_nonneg hu_le
      rwa [Real.sin_pi_div_two_sub] at h
    have hcos_cu : 8 / Real.pi ^ 3 * (Real.pi / 2 - t) ^ 3 ≤ Real.cos t ^ 3 := by
      have h := pow_le_pow_left₀ (mul_nonneg (by positivity) hu_nonneg) hcos_ge 3
      have h4 : (2 / Real.pi * (Real.pi / 2 - t)) ^ 3
          = 8 / Real.pi ^ 3 * (Real.pi / 2 - t) ^ 3 := by ring
      rwa [h4] at h
    have hm_le : 2 / Real.pi ^ 3 * (Real.pi / 2 - t) ^ 3 ≤ Real.sin t ^ 2 * Real.cos t ^ 3 := by
      have h := mul_le_mul hsin_sq hcos_cu
        (mul_nonneg (by positivity) (pow_nonneg hu_nonneg 3)) (sq_nonneg _)
      have h5 : (1 / 4) * (8 / Real.pi ^ 3 * (Real.pi / 2 - t) ^ 3)
          = 2 / Real.pi ^ 3 * (Real.pi / 2 - t) ^ 3 := by ring
      rwa [h5] at h
    have hm_pos : 0 < 2 / Real.pi ^ 3 * (Real.pi / 2 - t) ^ 3 :=
      mul_pos (by positivity) (pow_pos hu_pos 3)
    have h1 : 1 / (Real.sin t ^ 2 * Real.cos t ^ 3)
        ≤ 1 / (2 / Real.pi ^ 3 * (Real.pi / 2 - t) ^ 3) :=
      one_div_le_one_div_of_le hm_pos hm_le
    have h2 : 1 / (2 / Real.pi ^ 3 * (Real.pi / 2 - t) ^ 3)
        = (Real.pi ^ 3 / 2) / (Real.pi / 2 - t) ^ 3 := by
      field_simp
    linarith [h1, h2.le]
  -- Integrability of both integrands on `[π / 4, b]`.
  have hf_int : IntervalIntegrable (fun t => 1 / (Real.sin t ^ 2 * Real.cos t ^ 3)) volume
      (Real.pi / 4) b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hb1]
    refine ContinuousOn.div continuousOn_const ?_ ?_
    · exact (Real.continuous_sin.continuousOn.pow 2).mul (Real.continuous_cos.continuousOn.pow 3)
    · intro t ht
      refine ne_of_gt (mul_pos (pow_pos ?_ 2) (pow_pos ?_ 3))
      · exact Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.1, hpi])
          (by linarith [ht.2, hb2, hpi])
      · exact Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, hpi], by linarith [ht.2, hb2]⟩
  have hg_int : IntervalIntegrable (fun t => (Real.pi ^ 3 / 2) / (Real.pi / 2 - t) ^ 3) volume
      (Real.pi / 4) b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hb1]
    refine ContinuousOn.div continuousOn_const ?_ ?_
    · exact ((continuous_const : Continuous fun _ : ℝ => Real.pi / 2).sub continuous_id).continuousOn.pow 3
    · intro t ht
      exact ne_of_gt (pow_pos (by linarith [ht.2, hb2]) 3)
  have hle_int := intervalIntegral.integral_mono_on hb1 hf_int hg_int hpt
  -- Rewrite the majorant in `rpow` form so that the explicit antiderivative applies.
  have hcongr : (∫ t in (Real.pi / 4)..b, (Real.pi ^ 3 / 2) / (Real.pi / 2 - t) ^ 3)
      = ∫ t in (Real.pi / 4)..b, (Real.pi ^ 3 / 2) * (Real.pi / 2 - t) ^ (-3 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hb1] at ht
    have hbase : 0 ≤ Real.pi / 2 - t := by linarith [ht.2, hb2]
    change (Real.pi ^ 3 / 2) / (Real.pi / 2 - t) ^ 3
        = (Real.pi ^ 3 / 2) * (Real.pi / 2 - t) ^ (-3 : ℝ)
    have h3 : (Real.pi / 2 - t) ^ (3 : ℝ) = (Real.pi / 2 - t) ^ 3 := Real.rpow_natCast _ 3
    rw [Real.rpow_neg hbase 3, h3, div_eq_mul_inv]
  -- Evaluate the majorant integral.
  have hval : (∫ t in (Real.pi / 4)..b, (Real.pi ^ 3 / 2) * (Real.pi / 2 - t) ^ (-3 : ℝ))
      = (Real.pi ^ 3 / 2) * (((Real.pi / 2 - b) ^ (-2 : ℝ) - (Real.pi / 4) ^ (-2 : ℝ)) / 2) := by
    rw [intervalIntegral.integral_const_mul]
    rw [Work.FTS.EllipticEst.remov.integral_sub_rpow_neg (b := Real.pi / 2) (p := 3)
      (t := b) (θ := Real.pi / 4) hb1 hb2 (by norm_num : (1 : ℝ) < 3)]
    rw [show (1 : ℝ) - 3 = -2 by norm_num, show (3 : ℝ) - 1 = 2 by norm_num,
      show Real.pi / 2 - Real.pi / 4 = Real.pi / 4 by ring]
  have hA_nonneg : 0 ≤ (Real.pi / 2 - b) ^ (-2 : ℝ) :=
    Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ Real.pi / 2 - b) _
  have hB_nonneg : 0 ≤ (Real.pi / 4) ^ (-2 : ℝ) := Real.rpow_nonneg (by positivity) _
  have hAtarget : (Real.pi / 2 - b) ^ (-2 : ℝ) = 1 / (Real.pi / 2 - b) ^ 2 := by
    have h2 : (Real.pi / 2 - b) ^ (2 : ℝ) = (Real.pi / 2 - b) ^ 2 := Real.rpow_natCast _ 2
    rw [Real.rpow_neg (by linarith : (0 : ℝ) ≤ Real.pi / 2 - b) 2, h2, one_div]
  calc
    ∫ t in (Real.pi / 4)..b, 1 / (Real.sin t ^ 2 * Real.cos t ^ 3)
        ≤ ∫ t in (Real.pi / 4)..b, (Real.pi ^ 3 / 2) / (Real.pi / 2 - t) ^ 3 := hle_int
    _ = ∫ t in (Real.pi / 4)..b, (Real.pi ^ 3 / 2) * (Real.pi / 2 - t) ^ (-3 : ℝ) := hcongr
    _ = (Real.pi ^ 3 / 2) * (((Real.pi / 2 - b) ^ (-2 : ℝ) - (Real.pi / 4) ^ (-2 : ℝ)) / 2) :=
        hval
    _ ≤ (Real.pi ^ 3 / 2) * ((Real.pi / 2 - b) ^ (-2 : ℝ) / 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith [hB_nonneg]
    _ = Real.pi ^ 3 / 4 * (Real.pi / 2 - b) ^ (-2 : ℝ) := by ring
    _ ≤ (Real.pi ^ 3 / 4 + 1) * (Real.pi / 2 - b) ^ (-2 : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ hA_nonneg
        linarith
    _ = (Real.pi ^ 3 / 4 + 1) / (Real.pi / 2 - b) ^ 2 := by
        rw [hAtarget]; ring

end Work.FTS.EllipticEst.remov.SourceBound
