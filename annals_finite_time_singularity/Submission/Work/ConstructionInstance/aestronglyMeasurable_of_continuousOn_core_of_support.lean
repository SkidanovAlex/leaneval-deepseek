import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.StabilityFar.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

/-- A field `ω` that is continuous on the core region `coreRegion R'` and whose support lies in
the closed ball of radius `R ≤ R'` is almost everywhere strongly measurable for the Lebesgue
measure.  Indeed `ω` coincides with its restriction to the closed ball of radius `R` cut off
by zero, and the restriction is continuous there while the complement is the null-behaviour
part; the two are glued along a measurable set. -/
theorem aestronglyMeasurable_of_continuousOn_core_of_support
    {ω : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)} {R R' : ℝ} (hR : R ≤ R')
    (hcont : ContinuousOn ω (Work.StabilityFar.coreRegion R'))
    (hsupp : ∀ y : EuclideanSpace ℝ (Fin 3),
      ω y ≠ 0 → y ∈ Metric.closedBall 0 R) :
    MeasureTheory.AEStronglyMeasurable ω MeasureTheory.volume := by
  classical
  set s : Set (EuclideanSpace ℝ (Fin 3)) := Metric.closedBall 0 R with hs_def
  have hsub : s ⊆ Work.StabilityFar.coreRegion R' := by
    intro x hx
    rw [hs_def, Metric.mem_closedBall, dist_eq_norm, sub_zero] at hx
    rw [Work.StabilityFar.mem_coreRegion]
    exact le_trans hx hR
  have hcont_s : ContinuousOn ω s := hcont.mono hsub
  have hs_meas : MeasurableSet s := by
    rw [hs_def]; exact Metric.isClosed_closedBall.measurableSet
  have hAESM_restrict :
      MeasureTheory.AEStronglyMeasurable ω (MeasureTheory.volume.restrict s) :=
    hcont_s.aestronglyMeasurable hs_meas
  have h_ind :
      MeasureTheory.AEStronglyMeasurable (s.indicator ω) MeasureTheory.volume :=
    (aestronglyMeasurable_indicator_iff hs_meas).mpr hAESM_restrict
  have hfix : s.indicator ω =ᵐ[MeasureTheory.volume] ω := by
    refine Filter.Eventually.of_forall fun x => ?_
    by_cases hx : x ∈ s
    · simp [Set.indicator_of_mem hx]
    · have hz : ω x = 0 := by
        by_contra h
        exact hx (hsupp x h)
      simp [Set.indicator_of_notMem hx, hz]
  exact h_ind.congr hfix

end Work.ConstructionInstance
