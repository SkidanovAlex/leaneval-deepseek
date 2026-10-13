import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.L2Space
import Submission.Work.Spaces.cs_integral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

open MeasureTheory

/-- **Weighted Hardy/Cauchy–Schwarz tail bound.**

For `p > 0`, `z ≥ 1`, an a.e.-measurable `c` with `c²` integrable on `(1,∞)`, the square of
`z^p ∫_z^∞ c t · t^{-p-1} dt` is at most `(2p)^{-1} ∫_z^∞ c t² · t^{-1} dt`.

This is the classical Hardy inequality for the half-line, proved by writing
`c t · t^{-p-1} = (c t · t^{-1/2}) · t^{-p-1/2}` and applying Cauchy–Schwarz on `L²((z,∞))`
(`Work.Spaces.cs_integral`); the second factor contributes `∫_z^∞ t^{-2p-1} = z^{-2p}/(2p)`. -/
theorem sq_rpow_tail_mul_integral_le {c : ℝ → ℝ} {p z : ℝ} (hp : 0 < p) (hz : 1 ≤ z)
    (hc : AEMeasurable c)
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi (1 : ℝ))) :
    (z ^ p * ∫ t in Set.Ioi z, c t * t ^ (-p - 1)) ^ 2
      ≤ (1 / (2 * p)) * (∫ t in Set.Ioi z, (c t) ^ 2 * t ^ (-1 : ℝ)) := by
  have hz0 : 0 < z := lt_of_lt_of_le one_pos hz
  -- `z ≥ 1 > 0`
  have hc2 : IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi z) :=
    hfar.mono_set (Set.Ioi_subset_Ioi hz)
  have hc_meas : AEStronglyMeasurable c (volume.restrict (Set.Ioi z)) :=
    hc.aestronglyMeasurable.restrict
  -- the power functions are continuous (hence a.e. strongly measurable) on `(z,∞)`
  have hcont_pow : ∀ r : ℝ, ContinuousOn (fun t : ℝ => t ^ r) (Set.Ioi z) := fun r =>
    continuous_id.continuousOn.rpow_const (fun t ht => Or.inl (ne_of_gt (lt_trans hz0 ht)))
  have hmeas_pow : ∀ r : ℝ,
      AEStronglyMeasurable (fun t : ℝ => t ^ r) (volume.restrict (Set.Ioi z)) := fun r =>
    (hcont_pow r).aestronglyMeasurable measurableSet_Ioi
  -- `c² · t^{-1}` is integrable on `(z,∞)`, dominated by `c²` because `t ≥ 1` there
  have hJint : IntegrableOn (fun t : ℝ => (c t) ^ 2 * t ^ (-1 : ℝ)) (Set.Ioi z) := by
    refine Integrable.mono' hc2 ((hc_meas.pow 2).mul (hmeas_pow (-1))) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 : 1 ≤ t := le_trans hz (le_of_lt ht)
    have ht0 : 0 < t := lt_trans hz0 ht
    have hle : t ^ (-1 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ht1 (by norm_num)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (c t)),
      abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
    exact mul_le_of_le_one_right (sq_nonneg _) hle
  -- the two `L²` factors
  have hu_meas : AEStronglyMeasurable (fun t : ℝ => c t * t ^ (-1 / 2 : ℝ))
      (volume.restrict (Set.Ioi z)) := hc_meas.mul (hmeas_pow (-1 / 2))
  have hv_meas : AEStronglyMeasurable (fun t : ℝ => t ^ (-p - 1 / 2 : ℝ))
      (volume.restrict (Set.Ioi z)) := hmeas_pow (-p - 1 / 2)
  have hu_sq : Integrable (fun t : ℝ => (c t * t ^ (-1 / 2 : ℝ)) ^ 2)
      (volume.restrict (Set.Ioi z)) := by
    refine hJint.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := lt_trans hz0 ht
    have h : (t ^ (-1 / 2 : ℝ)) ^ 2 = t ^ (-1 : ℝ) := by
      rw [pow_two, ← Real.rpow_add ht0]; norm_num
    rw [mul_pow, h]
  have hv_sq : Integrable (fun t : ℝ => (t ^ (-p - 1 / 2 : ℝ)) ^ 2)
      (volume.restrict (Set.Ioi z)) := by
    refine (integrableOn_Ioi_rpow_of_lt (a := -2 * p - 1) (by linarith) hz0).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := lt_trans hz0 ht
    rw [pow_two, ← Real.rpow_add ht0]
    ring_nf
  -- Cauchy–Schwarz on `(z,∞)`
  have hcs := Work.Spaces.cs_integral
    (u := fun t : ℝ => c t * t ^ (-1 / 2 : ℝ))
    (v := fun t : ℝ => t ^ (-p - 1 / 2 : ℝ))
    ((memLp_two_iff_integrable_sq hu_meas).mpr hu_sq)
    ((memLp_two_iff_integrable_sq hv_meas).mpr hv_sq)
  -- identify the three integrals appearing in Cauchy–Schwarz
  have e1 : (∫ x in Set.Ioi z, c x * x ^ (-1 / 2 : ℝ) * x ^ (-p - 1 / 2 : ℝ))
      = ∫ t in Set.Ioi z, c t * t ^ (-p - 1) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht0 : 0 < t := lt_trans hz0 ht
    rw [mul_assoc, ← Real.rpow_add ht0]
    ring_nf
  have e2 : (∫ x in Set.Ioi z, (c x * x ^ (-1 / 2 : ℝ)) ^ 2)
      = ∫ t in Set.Ioi z, (c t) ^ 2 * t ^ (-1 : ℝ) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht0 : 0 < t := lt_trans hz0 ht
    have h : (t ^ (-1 / 2 : ℝ)) ^ 2 = t ^ (-1 : ℝ) := by
      rw [pow_two, ← Real.rpow_add ht0]; norm_num
    rw [mul_pow, h]
  have e3 : (∫ x in Set.Ioi z, (x ^ (-p - 1 / 2 : ℝ)) ^ 2) = z ^ (-2 * p) / (2 * p) := by
    have hcong : (∫ x in Set.Ioi z, (x ^ (-p - 1 / 2 : ℝ)) ^ 2)
        = ∫ t in Set.Ioi z, t ^ (-2 * p - 1) := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
      have ht0 : 0 < t := lt_trans hz0 ht
      rw [pow_two, ← Real.rpow_add ht0]
      ring_nf
    rw [hcong, integral_Ioi_rpow_of_lt (a := -2 * p - 1) (by linarith) hz0]
    rw [show (-2 * p - 1) + 1 = -2 * p by ring]
    ring
  have hmain : (∫ t in Set.Ioi z, c t * t ^ (-p - 1)) ^ 2
      ≤ (∫ t in Set.Ioi z, (c t) ^ 2 * t ^ (-1 : ℝ)) * (z ^ (-2 * p) / (2 * p)) := by
    rw [← e1, ← e2, ← e3]
    exact hcs
  have hzp : (z ^ p) ^ 2 = z ^ (2 * p) := by
    rw [pow_two, ← Real.rpow_add hz0]; ring_nf
  have hzz : z ^ (2 * p) * z ^ (-2 * p) = 1 := by
    rw [← Real.rpow_add hz0, show 2 * p + (-2 * p) = 0 by ring, Real.rpow_zero]
  calc (z ^ p * ∫ t in Set.Ioi z, c t * t ^ (-p - 1)) ^ 2
      = z ^ (2 * p) * (∫ t in Set.Ioi z, c t * t ^ (-p - 1)) ^ 2 := by
        rw [mul_pow, hzp]
    _ ≤ z ^ (2 * p) * ((∫ t in Set.Ioi z, (c t) ^ 2 * t ^ (-1 : ℝ)) *
          (z ^ (-2 * p) / (2 * p))) :=
        mul_le_mul_of_nonneg_left hmain (Real.rpow_nonneg hz0.le _)
    _ = (1 / (2 * p)) * (∫ t in Set.Ioi z, (c t) ^ 2 * t ^ (-1 : ℝ)) := by
        rw [show z ^ (2 * p) * ((∫ t in Set.Ioi z, (c t) ^ 2 * t ^ (-1 : ℝ)) *
              (z ^ (-2 * p) / (2 * p)))
            = (∫ t in Set.Ioi z, (c t) ^ 2 * t ^ (-1 : ℝ)) *
              (z ^ (2 * p) * z ^ (-2 * p)) / (2 * p) by ring]
        rw [hzz]
        ring

end Work.FTS.PhiStar.Honesty
