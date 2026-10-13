import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.PhiStar.Honesty.integrableOn_sq_mul_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

open MeasureTheory Set

/-- On `(0,1]` the weight `t ^ r` is dominated by `t ^ (-4)` whenever `r ≥ -4`; hence
`(c t)^2 * t ^ r` is controlled by the integrand `(c t)^2 / t^4` and is integrable on
`Icc 0 1` (the endpoints form a null set).  Only a.e.-measurability of `c` is needed. -/
theorem integrableOn_sq_mul_rpow_ae {c : ℝ → ℝ} {r : ℝ} (hr : -4 ≤ r)
    (hc : AEMeasurable c)
    (hint : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1)) :
    MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 * t ^ r) (Set.Icc 0 1) := by
  have hmono : Integrable (fun t : ℝ => (c t) ^ 2 * t ^ r) (volume.restrict (Ioo 0 1)) := by
    refine Integrable.mono' hint.norm ?_ ?_
    · have h1 : AEStronglyMeasurable c (volume.restrict (Ioo 0 1)) :=
        (hc.mono_measure Measure.restrict_le_self).aestronglyMeasurable
      have h2 : AEStronglyMeasurable (fun t : ℝ => t ^ r) (volume.restrict (Ioo 0 1)) :=
        (ContinuousOn.rpow_const continuousOn_id
          (fun x hx => Or.inl (ne_of_gt hx.1))).aestronglyMeasurable measurableSet_Ioo
      exact (h1.pow 2).mul h2
    · rw [ae_restrict_iff' measurableSet_Ioo]
      filter_upwards with t ht
      have ht0 : 0 < t := ht.1
      have ht1 : t ≤ 1 := ht.2.le
      have hpow : t ^ r ≤ (t ^ (4:ℕ))⁻¹ := by
        have h := Real.rpow_le_rpow_of_exponent_ge ht0 ht1 hr
        rw [Real.rpow_neg (le_of_lt ht0)] at h
        simpa using h
      have h4 : (0:ℝ) < t^4 := by positivity
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg ht0.le r)),
        abs_of_nonneg (div_nonneg (sq_nonneg _) h4.le), div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left hpow (sq_nonneg _)
  rw [MeasureTheory.IntegrableOn,
    ← Measure.restrict_congr_set (Ioo_ae_eq_Icc (a := (0:ℝ)) (b := 1))]
  exact hmono

end Work.FTS.PhiStar.Honesty
