import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.PhiStar.Honesty.tendsto_integral_mul_of_tendsto_integral_sq_zero
import Submission.Work.FTS.PhiStar.Honesty.integral_sq_eq_of_difference

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

theorem tendsto_sq_weighted_of_tendsto_difference {c : ℝ → ℝ} {c_ : ℕ → ℝ → ℝ}
    (hcw : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 * (Work.Spaces.w t) ^ 2) (Set.Ioi 0))
    (hint : ∀ n, MeasureTheory.IntegrableOn (fun t : ℝ => (c_ n t - c t) ^ 2 * (Work.Spaces.w t) ^ 2) (Set.Ioi 0))
    (hcross : ∀ n, MeasureTheory.IntegrableOn (fun t : ℝ => (c_ n t - c t) * c t * (Work.Spaces.w t) ^ 2) (Set.Ioi 0))
    (hconv : Filter.Tendsto (fun n => ∫ t in Set.Ioi 0, (c_ n t - c t) ^ 2 * (Work.Spaces.w t) ^ 2) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => ∫ t in Set.Ioi 0, (c_ n t) ^ 2 * (Work.Spaces.w t) ^ 2) Filter.atTop
      (nhds (∫ t in Set.Ioi 0, (c t) ^ 2 * (Work.Spaces.w t) ^ 2)) := by
  have ha : ∀ n, MeasureTheory.Integrable
      (fun t : ℝ => ((c_ n t - c t) * Work.Spaces.w t) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
    intro n
    exact (hint n).congr
      (Filter.Eventually.of_forall fun t => (mul_pow (c_ n t - c t) (Work.Spaces.w t) 2).symm)
  have hb : MeasureTheory.Integrable (fun t : ℝ => (c t * Work.Spaces.w t) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
    exact hcw.congr
      (Filter.Eventually.of_forall fun t => (mul_pow (c t) (Work.Spaces.w t) 2).symm)
  have hconv' : Filter.Tendsto
      (fun n : ℕ => ∫ x, ((c_ n x - c x) * Work.Spaces.w x) ^ 2
        ∂(MeasureTheory.volume.restrict (Set.Ioi 0))) Filter.atTop (nhds 0) := by
    simpa only [mul_pow] using hconv
  have hcross0 : Filter.Tendsto
      (fun n : ℕ => ∫ x, ((c_ n x - c x) * Work.Spaces.w x) * (c x * Work.Spaces.w x)
        ∂(MeasureTheory.volume.restrict (Set.Ioi 0))) Filter.atTop (nhds 0) :=
    tendsto_integral_mul_of_tendsto_integral_sq_zero (α := ℝ)
      (μ := MeasureTheory.volume.restrict (Set.Ioi 0))
      (a := fun n x => (c_ n x - c x) * Work.Spaces.w x)
      (b := fun x => c x * Work.Spaces.w x) ha hb hconv'
  have hcross0' : Filter.Tendsto
      (fun n : ℕ => ∫ t in Set.Ioi 0, (c_ n t - c t) * c t * (Work.Spaces.w t) ^ 2)
      Filter.atTop (nhds 0) := by
    refine hcross0.congr (fun n => ?_)
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    ring
  have hsum : Filter.Tendsto
      (fun n : ℕ => (∫ t in Set.Ioi 0, (c_ n t - c t) ^ 2 * (Work.Spaces.w t) ^ 2)
        + 2 * (∫ t in Set.Ioi 0, (c_ n t - c t) * c t * (Work.Spaces.w t) ^ 2)
        + ∫ t in Set.Ioi 0, (c t) ^ 2 * (Work.Spaces.w t) ^ 2)
      Filter.atTop (nhds (∫ t in Set.Ioi 0, (c t) ^ 2 * (Work.Spaces.w t) ^ 2)) := by
    have h1 : Filter.Tendsto
        (fun n : ℕ => (∫ t in Set.Ioi 0, (c_ n t - c t) ^ 2 * (Work.Spaces.w t) ^ 2)
          + 2 * (∫ t in Set.Ioi 0, (c_ n t - c t) * c t * (Work.Spaces.w t) ^ 2))
        Filter.atTop (nhds (0 + 2 * 0)) := hconv.add (hcross0'.const_mul 2)
    have h2 := h1.add (tendsto_const_nhds : Filter.Tendsto
      (fun _ : ℕ => ∫ t in Set.Ioi 0, (c t) ^ 2 * (Work.Spaces.w t) ^ 2) Filter.atTop
      (nhds (∫ t in Set.Ioi 0, (c t) ^ 2 * (Work.Spaces.w t) ^ 2)))
    simpa using h2
  refine hsum.congr (fun n => ?_)
  exact (integral_sq_eq_of_difference (c := c) (c_ := c_) n hcw (hint n) (hcross n)).symm

end Work.FTS.PhiStar.Honesty
