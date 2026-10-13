import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllExist.RadGreenDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

open MeasureTheory Set

/-- The general form of the target: for an integrable-on-`(1,∞)` square `c²` and any real
exponent `q > 0`, the Lebesgue integral of `t ↦ (c t)² t^q` over `(1,z)` (i.e. the `ofReal` of
the interval integral over `1..z`) agrees with the `lintegral` of its `ofReal` over `Ioo 1 z`.

This is the standard `ofReal_integral_eq_lintegral_ofReal` (applied to the restricted measure
`volume.restrict (Ioo 1 z)`) together with the identification of `∫ t in 1..z` with the set
integral over `Ioo 1 z` for `1 ≤ z` (the endpoints differ by a null set).  Integrability comes
from `hfar` by domination with `z^q`, the exponent being bounded on `(1,z)`. -/
private theorem ofReal_integral_mul_rpow_eq_lintegral {c : ℝ → ℝ} {q : ℝ} (hq : 0 < q)
    (hc : AEMeasurable c)
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    ∀ z : ℝ, 1 ≤ z →
      ENNReal.ofReal (∫ t in (1 : ℝ)..z, (c t) ^ 2 * t ^ q)
        = ∫⁻ t in Set.Ioo (1 : ℝ) z, ENNReal.ofReal ((c t) ^ 2 * t ^ q) := by
  intro z hz
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [MeasureTheory.restrict_Ioo_eq_restrict_Ioc, ← intervalIntegral.integral_of_le hz]
  · -- integrability on `Ioo 1 z`
    have hmem : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioo (1 : ℝ) z) :=
      hfar.mono_set Set.Ioo_subset_Ioi_self
    refine MeasureTheory.Integrable.mono' (hmem.mul_const (z ^ q)) ?_ ?_
    · refine AEStronglyMeasurable.mul ((hc.aestronglyMeasurable.restrict).pow 2) ?_
      exact (ContinuousOn.rpow_const continuousOn_id
        (fun x hx => Or.inl (ne_of_gt (by linarith [hx.1] : (0 : ℝ) < x)))).aestronglyMeasurable
        measurableSet_Ioo
    · rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
      filter_upwards with t ht
      have ht0 : (0 : ℝ) ≤ t := by linarith [ht.1]
      rw [Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg ht0 q))]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ht0 ht.2.le hq.le) (sq_nonneg _)
  · change ∀ᵐ t ∂MeasureTheory.volume.restrict (Set.Ioo (1 : ℝ) z), 0 ≤ (c t) ^ 2 * t ^ q
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
    filter_upwards with t ht
    exact mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (by linarith [ht.1] : (0 : ℝ) ≤ t) q)

theorem ofReal_integral_rpow_mul_sq_eq_lintegral {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m) (hc : AEMeasurable c)
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    ∀ z : ℝ, 1 ≤ z →
      ENNReal.ofReal (∫ t in (1 : ℝ)..z, (c t) ^ 2 * t ^ (Work.FTS.EllExist.rgQ α m - 1))
        = ∫⁻ t in Set.Ioo (1 : ℝ) z,
            ENNReal.ofReal ((c t) ^ 2 * t ^ (Work.FTS.EllExist.rgQ α m - 1)) := by
  have hq : 0 < Work.FTS.EllExist.rgQ α m - 1 := by
    have := Work.FTS.EllExist.rgQ_ge hα hα4 hm
    linarith
  exact ofReal_integral_mul_rpow_eq_lintegral (q := Work.FTS.EllExist.rgQ α m - 1) hq hc hfar

end Work.FTS.PhiStar.Honesty
