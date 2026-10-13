import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllExist.RadGreenDefs
import Submission.Work.FTS.PhiStar.Honesty.lintegral_tail_swap_Ioi_one
import Submission.Work.FTS.PhiStar.Honesty.integrableOn_tailSetIntegral_Ioi_one
import Submission.Work.FTS.PhiStar.Honesty.sq_rpow_tail_mul_integral_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

open MeasureTheory Set Filter

set_option linter.unusedVariables false

/-- **Far-field square bound for the growing Green branch.**

With `p = rgP α m ≥ 8` and `rgG2 α m c z = z^p * ∫_{Ioi z} c t * t^{-p-1} dt`, the function
`z ↦ (rgG2 α m c z)²` is integrable on `(1,∞)`.

HINT (verified by two reviewers).  For `z > 1` split
`c t * t^{-p-1} = (c t * t^{-1/2}) * t^{-p-1/2}`, so Cauchy–Schwarz on `Ioi z` gives
`(∫ t in Ioi z, c t t^{-p-1})² ≤ (∫ t in Ioi z, (c t)² t^{-1}) * (∫ t in Ioi z, t^{-2p-1})`
with `∫ t in Ioi z, t^{-2p-1} = z^{-2p}/(2p)` (`p > 0`, use `integral_Ioi_rpow_of_lt`). Hence
`(rgG2 z)² ≤ (1/(2p)) * ∫ t in Ioi z, (c t)² t^{-1}` (the `t`-integral is honest: the same
Cauchy–Schwarz bounds `∫ t in Ioi z, |c t| t^{-p-1}`).
Then Tonelli on the region `1 < z < t < ∞`
(`Work.FTS.PhiStar.Honesty.lintegral_tail_swap_Ioi_one`) gives
`∫_1^∞ ∫_z^∞ (c t)² t^{-1} dt dz = ∫_1^∞ (c t)² (t-1)/t dt ≤ ∫_1^∞ (c t)² dt < ∞` (`hfar`, and
`1/t ≤ 1` on `(1,∞)`, so `(c t)²/t ∈ L¹(Ioi 1)` by `IntegrableOn.mono_set`).
For `AEStronglyMeasurable` of `z ↦ ∫ t in Ioi z, rgF2 α m c t` on `(1,∞)`: write it as
`C₁ - ∫ t in 1..z, rgF2 α m c t` with `C₁ = ∫ t in Ioi 1, rgF2 α m c t`, a sum of a constant and a
primitive, hence continuous on `(1,∞)`
(`intervalIntegral.continuousOn_primitive_interval`; the identity follows from
`setIntegral_union` on `Ioi 1 = Ioc 1 z ∪ Ioi z`). -/
/- PROOF (as implemented; the two measure-theoretic bricks below are separate modules).

Write `p = rgP α m > 0` and `Q t = (c t)² t^{-1}`.

* `Work.FTS.PhiStar.Honesty.sq_rpow_tail_mul_integral_le` is the Cauchy–Schwarz step with the
  splitting `c t · t^{-p-1} = (c t · t^{-1/2})·(t^{-p-1/2})`: for `z ≥ 1`,
  `(rgG2 α m c z)² ≤ (1/(2p)) ∫ t in Ioi z, Q t` (the factor `z^{2p}` cancels `z^{-2p}` coming
  from `∫ t in Ioi z, t^{-2p-1} = z^{-2p}/(2p)`).
* `Work.FTS.PhiStar.Honesty.integrableOn_tailSetIntegral_Ioi_one` is Tonelli on the region
  `1 < z < t`: since `Q ∈ L¹(1,∞)` (dominated by `c²` there, as `t^{-1} ≤ 1`) and also
  `t ↦ t·Q t = c²` is integrable, the tail integral `z ↦ ∫ t in Ioi z, Q t` is integrable on
  `(1,∞)`.
* Measurability of `z ↦ ∫ t in Ioi z, rgF2 α m c t` is obtained from the product-measure
  identity `MeasureTheory.AEStronglyMeasurable.integral_prod_right'` applied to
  `(z,t) ↦ 1_{z<t}·rgF2 α m c t` (the integrand restricted to `(1,∞)`), and then `rgG2` is the
  product of that map with the continuous weight `z^p`; the conclusion is `Integrable.mono'`
  against the integrable dominating function `(1/(2p)) ∫ t in Ioi z, Q t`. -/
theorem rgG2_sq_Ioi {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m) (hc : AEMeasurable c)
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.FTS.EllExist.rgG2 α m c z) ^ 2) (Set.Ioi 1) := by
  have hp8 : 8 ≤ Work.FTS.EllExist.rgP α m := Work.FTS.EllExist.rgP_ge hα hα4 hm
  have hp : 0 < Work.FTS.EllExist.rgP α m := lt_of_lt_of_le (by norm_num) hp8
  -- the weight of the Cauchy–Schwarz estimate
  set Q : ℝ → ℝ := fun t => (c t) ^ 2 * t ^ (-1 : ℝ) with hQdef
  have hQnn : 0 ≤ᵐ[volume.restrict (Ioi (1 : ℝ))] Q := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (le_of_lt (lt_trans one_pos ht)) _)
  -- `Q` is integrable on `(1,∞)`: it is dominated there by `c²`
  have hQint : IntegrableOn Q (Ioi 1) := by
    refine Integrable.mono' hfar ?_ ?_
    · have h1 : AEStronglyMeasurable (fun t : ℝ => (c t) ^ 2) (volume.restrict (Ioi 1)) :=
        (hc.aestronglyMeasurable.restrict).pow 2
      have h2 : AEStronglyMeasurable (fun t : ℝ => t ^ (-1 : ℝ)) (volume.restrict (Ioi 1)) :=
        ((continuousOn_id.rpow_const
          (fun t ht => Or.inl (ne_of_gt (lt_trans one_pos ht)))).aestronglyMeasurable
            measurableSet_Ioi)
      simpa only [hQdef] using
        (h1.mul h2).congr (Filter.EventuallyEq.of_eq (by funext t; simp only [Pi.mul_apply]))
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have hpow : t ^ (-1 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ht.le (by norm_num)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _),
        abs_of_nonneg (Real.rpow_nonneg (le_of_lt (lt_trans one_pos ht)) _)]
      calc (c t) ^ 2 * t ^ (-1 : ℝ) ≤ (c t) ^ 2 * 1 :=
            mul_le_mul_of_nonneg_left hpow (sq_nonneg _)
        _ = (c t) ^ 2 := mul_one _
  -- and so is `t ↦ t·Q t`, which is just `c²` on `(1,∞)`
  have hQt : IntegrableOn (fun t : ℝ => Q t * t) (Ioi 1) := by
    refine hfar.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_trans one_pos ht)
    simp only [hQdef, Real.rpow_neg_one, mul_assoc, inv_mul_cancel₀ ht0, mul_one]
  -- the Tonelli step on the region `1 < z < t`
  have hTail : IntegrableOn (fun z : ℝ => ∫ t in Ioi z, Q t) (Ioi 1) :=
    (integrableOn_tailSetIntegral_Ioi_one hQint hQnn hQt).1
  -- the Cauchy–Schwarz pointwise bound
  have hbound : ∀ z ∈ Ioi (1 : ℝ), (Work.FTS.EllExist.rgG2 α m c z) ^ 2
      ≤ (1 / (2 * Work.FTS.EllExist.rgP α m)) * (∫ t in Ioi z, Q t) := by
    intro z hz
    have h1 := sq_rpow_tail_mul_integral_le (c := c) (p := Work.FTS.EllExist.rgP α m)
      (z := z) hp hz.le hc hfar
    simpa only [hQdef, Work.FTS.EllExist.rgG2, Work.FTS.EllExist.rgB,
      Work.FTS.EllExist.rgF2] using h1
  -- a.e.-strong measurability of the tail integrand `rgF2 α m c` …
  have hrgF2_aesm : AEStronglyMeasurable (Work.FTS.EllExist.rgF2 α m c)
      (volume.restrict (Ioi (1 : ℝ))) := by
    have h1 : AEStronglyMeasurable c (volume.restrict (Ioi (1 : ℝ))) :=
      hc.aestronglyMeasurable.restrict
    have h2 : AEStronglyMeasurable (fun t : ℝ => t ^ (-(Work.FTS.EllExist.rgP α m) - 1))
        (volume.restrict (Ioi (1 : ℝ))) :=
      ((continuousOn_id.rpow_const
        (fun t ht => Or.inl (ne_of_gt (lt_trans one_pos ht)))).aestronglyMeasurable
          measurableSet_Ioi)
    refine (h1.mul h2).congr (Filter.EventuallyEq.of_eq ?_)
    funext t
    simp only [Pi.mul_apply, Work.FTS.EllExist.rgF2]
  -- … hence of its tail integral, by the product-measure form of Fubini
  have htail_aesm : AEStronglyMeasurable
      (fun z : ℝ => ∫ t in Ioi z, Work.FTS.EllExist.rgF2 α m c t)
      (volume.restrict (Ioi (1 : ℝ))) := by
    set g : ℝ → ℝ := (Ioi (1 : ℝ)).indicator (Work.FTS.EllExist.rgF2 α m c) with hg_def
    have hg : AEStronglyMeasurable g (volume.restrict (Ioi (1 : ℝ))) :=
      hrgF2_aesm.indicator measurableSet_Ioi
    have hpair : AEStronglyMeasurable (fun p : ℝ × ℝ => if p.1 < p.2 then g p.2 else (0 : ℝ))
        ((volume.restrict (Ioi (1 : ℝ))).prod (volume.restrict (Ioi (1 : ℝ)))) := by
      have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => g p.2)
          ((volume.restrict (Ioi (1 : ℝ))).prod (volume.restrict (Ioi (1 : ℝ)))) :=
        hg.comp_snd
      have h2 : Measurable (fun p : ℝ × ℝ => (if p.1 < p.2 then (1 : ℝ) else 0)) :=
        Measurable.ite (measurableSet_lt measurable_fst measurable_snd) measurable_const
          measurable_const
      refine (h1.mul h2.aestronglyMeasurable).congr ?_
      filter_upwards with p
      by_cases h : p.1 < p.2 <;> simp [h]
    refine (hpair.integral_prod_right').congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hsuby : Ioi y ⊆ Ioi (1 : ℝ) :=
      fun t ht => Set.mem_Ioi.mpr (lt_trans (Set.mem_Ioi.mp hy) (Set.mem_Ioi.mp ht))
    calc ∫ t, (if y < t then g t else (0 : ℝ)) ∂(volume.restrict (Ioi (1 : ℝ)))
        = ∫ t, (Ioi y).indicator (Work.FTS.EllExist.rgF2 α m c) t
            ∂(volume.restrict (Ioi (1 : ℝ))) := by
          refine integral_congr_ae ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          by_cases h : y < t
          · rw [ite_eq_left h, Set.indicator_of_mem (Set.mem_Ioi.mpr h),
              hg_def, Set.indicator_of_mem ht]
          · rw [ite_eq_right h, Set.indicator_of_notMem (by simpa using h)]
      _ = ∫ t in Ioi y, Work.FTS.EllExist.rgF2 α m c t
            ∂(volume.restrict (Ioi (1 : ℝ))) := integral_indicator measurableSet_Ioi
      _ = ∫ t in Ioi y, Work.FTS.EllExist.rgF2 α m c t := by
          rw [Measure.restrict_restrict_of_subset hsuby]
  -- a.e.-strong measurability of `rgG2` and of its square
  have hrg_aesm : AEStronglyMeasurable (fun z : ℝ => Work.FTS.EllExist.rgG2 α m c z)
      (volume.restrict (Ioi (1 : ℝ))) := by
    have hzpow : AEStronglyMeasurable (fun z : ℝ => z ^ (Work.FTS.EllExist.rgP α m))
        (volume.restrict (Ioi (1 : ℝ))) :=
      ((continuousOn_id.rpow_const
        (fun z hz => Or.inl (ne_of_gt (lt_trans one_pos hz)))).aestronglyMeasurable
          measurableSet_Ioi)
    refine (hzpow.mul htail_aesm).congr (Filter.EventuallyEq.of_eq ?_)
    funext z
    simp only [Pi.mul_apply]
    rw [Work.FTS.EllExist.rgG2, Work.FTS.EllExist.rgB]
  have htarget : AEStronglyMeasurable (fun z : ℝ => (Work.FTS.EllExist.rgG2 α m c z) ^ 2)
      (volume.restrict (Ioi (1 : ℝ))) := hrg_aesm.pow 2
  -- the dominating function is integrable, and the target is dominated by it
  have hdom_int : IntegrableOn
      (fun z : ℝ => (1 / (2 * Work.FTS.EllExist.rgP α m)) * (∫ t in Ioi z, Q t)) (Ioi 1) :=
    hTail.const_mul _
  refine Integrable.mono' hdom_int htarget ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact hbound z hz

end Work.FTS.PhiStar.Honesty
