import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Honesty.lintegral_Ioo_triangle
import Submission.Work.FTS.PhiStar.Honesty.lintegral_ofReal_rpow_Ioo_left
import Submission.Work.FTS.PhiStar.Honesty.radGreen_firstTerm_sq_div_z4_integrableOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty

theorem lintegral_rpow_prim_weighted_le {c : ℝ → ℝ} {r : ℝ} (hr : -2 < r)
    (hc : AEMeasurable c)
    (hint : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1)) :
    MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1))
        (fun z => ENNReal.ofReal (z ^ (-(2 * r + 5)))
          * MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) z))
              (fun t => ENNReal.ofReal ((c t) ^ 2 * t ^ (2 * r))))
      ≤ MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1))
          (fun t => ENNReal.ofReal ((c t) ^ 2 / t ^ 4))
        * (ENNReal.ofReal (2 * r + 4))⁻¹ := by
  have h01 : (0 : ℝ) ≤ 1 := by norm_num
  have hr' : -(2 * r + 5) < (-1 : ℝ) := by linarith
  have hv : (0 : ℝ) < 2 * r + 4 := by linarith
  have hc' : AEMeasurable c (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
    hc.mono_measure Measure.restrict_le_self
  have hFmeas : AEMeasurable (fun z : ℝ => ENNReal.ofReal (z ^ (-(2 * r + 5))))
      (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (AEMeasurable.pow aemeasurable_id aemeasurable_const)
  have hGmeas : AEMeasurable (fun t : ℝ => ENNReal.ofReal ((c t) ^ 2 * t ^ (2 * r)))
      (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((hc'.pow_const 2).mul (AEMeasurable.pow aemeasurable_id aemeasurable_const))
  have hQmeas : AEMeasurable (fun t : ℝ => ENNReal.ofReal ((c t) ^ 2 / t ^ 4))
      (volume.restrict (Set.Ioo (0 : ℝ) 1)) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((hc'.pow_const 2).div (aemeasurable_id.pow_const 4))
  -- the elementary primitive: for `t ∈ (0,1)` the `z`-integral is the `ofReal` of a number
  -- at most `t ^ (-(2r+4)) / (2r+4)`
  have hinner_le : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      (∫⁻ z in Set.Ioo t 1, ENNReal.ofReal (z ^ (-(2 * r + 5))))
        ≤ ENNReal.ofReal (t ^ (-(2 * r + 4)) / (2 * r + 4)) := by
    intro t ht
    rw [lintegral_ofReal_rpow_Ioo_left (r := -(2 * r + 5)) (t := t) ht.1 (le_of_lt ht.2) hr']
    refine ENNReal.ofReal_le_ofReal ?_
    have hkey : (1 - t ^ (-(2 * r + 4))) / (-(2 * r + 4))
        = (t ^ (-(2 * r + 4)) - 1) / (2 * r + 4) := by
      rw [div_neg, ← neg_div, neg_sub]
    rw [show -(2 * r + 5) + 1 = -(2 * r + 4) by ring, hkey, div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.mpr (le_of_lt hv))
  -- the pointwise rewriting of the weight `t ^ (2r) · t ^ (-(2r+4)) = t ^ (-4)`
  have hpteq : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      ENNReal.ofReal ((c t) ^ 2 * t ^ (2 * r))
          * ENNReal.ofReal (t ^ (-(2 * r + 4)) / (2 * r + 4))
        = ENNReal.ofReal ((c t) ^ 2 / t ^ 4) * (ENNReal.ofReal (2 * r + 4))⁻¹ := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have hA : ENNReal.ofReal ((c t) ^ 2 * t ^ (2 * r)) * ENNReal.ofReal (t ^ (-(2 * r + 4)))
        = ENNReal.ofReal ((c t) ^ 2 / t ^ 4) := by
      rw [← ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt ht0) _))]
      congr 1
      rw [div_eq_mul_inv, ← Real.rpow_natCast t 4, ← Real.rpow_neg (le_of_lt ht0) ((4 : ℕ) : ℝ)]
      rw [mul_assoc, ← Real.rpow_add ht0]
      have hE : 2 * r + (-(2 * r + 4)) = -(((4 : ℕ) : ℝ)) := by push_cast; ring
      rw [hE]
    have hB : ENNReal.ofReal (t ^ (-(2 * r + 4)) / (2 * r + 4))
        = ENNReal.ofReal (t ^ (-(2 * r + 4))) * (ENNReal.ofReal (2 * r + 4))⁻¹ := by
      rw [ENNReal.ofReal_div_of_pos hv, div_eq_mul_inv]
    rw [hB, ← mul_assoc, hA]
  calc MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) 1))
        (fun z => ENNReal.ofReal (z ^ (-(2 * r + 5)))
          * MeasureTheory.lintegral (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) z))
              (fun t => ENNReal.ofReal ((c t) ^ 2 * t ^ (2 * r))))
      = ∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal ((c t) ^ 2 * t ^ (2 * r))
          * ∫⁻ z in Set.Ioo t 1, ENNReal.ofReal (z ^ (-(2 * r + 5))) :=
        lintegral_Ioo_triangle (a := 0) (b := 1) h01 hFmeas hGmeas
    _ ≤ ∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal ((c t) ^ 2 * t ^ (2 * r))
          * ENNReal.ofReal (t ^ (-(2 * r + 4)) / (2 * r + 4)) := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        exact mul_le_mul_of_nonneg_left (hinner_le t ht) zero_le
    _ = ∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal ((c t) ^ 2 / t ^ 4)
          * (ENNReal.ofReal (2 * r + 4))⁻¹ := by
        refine lintegral_congr_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        exact hpteq t ht
    _ = (∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal ((c t) ^ 2 / t ^ 4))
          * (ENNReal.ofReal (2 * r + 4))⁻¹ :=
        lintegral_mul_const'' _ hQmeas

end Work.FTS.PhiStar.Honesty
