import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SolutionDelivery.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.SolutionDelivery.Measurable

open MeasureTheory

/-- **Measurability of the vorticity slices from the core regularity.**

The core `C¹` regularity of `ω.uncurry` on `coreRegion ρ ×ˢ extWindow T`, together with the
support box (the slices vanish outside `B(0,R) ⊆ B(0,ρ)`), makes every slice `ω · t` at a window
time `t` Borel measurable: a function which is continuous on the closed ball `B(0,ρ)` and vanishes
off it is Borel measurable, hence (as `ℝ³` is second countable) almost everywhere strongly
measurable. -/
theorem slicesMeasurable_of_core {ω : Work.SolutionDelivery.R3 → ℝ → Work.SolutionDelivery.R3}
    {ρ R T : ℝ} (hρ : R ≤ ρ)
    (hcont : ContDiffOn ℝ 1 ω.uncurry
      (Work.StabilityFar.coreRegion ρ ×ˢ Work.SolutionDelivery.extWindow T))
    (hsupp : ∀ t ∈ Work.SolutionDelivery.extWindow T, ∀ y : Work.SolutionDelivery.R3,
      ω y t ≠ 0 → y ∈ Metric.closedBall 0 R) :
    Work.StabilityFar.SlicesMeasurable ω T := by
  intro t ht
  -- the window sits inside the extended window, where the core regularity is imposed
  have ht_ext : t ∈ Work.SolutionDelivery.extWindow T :=
    Work.SolutionDelivery.window_subset_extWindow T ht
  -- the `t`-slice is continuous on the core region
  have hcont_slice : ContinuousOn (fun y : Work.SolutionDelivery.R3 => ω y t)
      (Work.StabilityFar.coreRegion ρ) := by
    refine (hcont.continuousOn.comp (f := fun y : Work.SolutionDelivery.R3 => (y, t)) ?_ ?_)
    · exact (continuous_id.prodMk continuous_const).continuousOn
    · intro y hy; exact ⟨hy, ht_ext⟩
  -- hence a.e. strongly measurable for the restricted measure
  have hmeas : AEStronglyMeasurable (fun y : Work.SolutionDelivery.R3 => ω y t)
      (volume.restrict (Work.StabilityFar.coreRegion ρ)) :=
    hcont_slice.aestronglyMeasurable (Work.StabilityFar.isClosed_coreRegion ρ).measurableSet
  have hind : AEStronglyMeasurable
      ((Work.StabilityFar.coreRegion ρ).indicator (fun y : Work.SolutionDelivery.R3 => ω y t))
      volume :=
    (aestronglyMeasurable_indicator_iff
      (Work.StabilityFar.isClosed_coreRegion ρ).measurableSet).mpr hmeas
  -- the slice already vanishes off the (closed) core ball, so the indicator is the slice itself
  have heq : (Work.StabilityFar.coreRegion ρ).indicator (fun y : Work.SolutionDelivery.R3 => ω y t)
      = (fun y => ω y t) := by
    funext y
    rcases em (y ∈ Work.StabilityFar.coreRegion ρ) with hy | hy
    · rw [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy]
      symm
      by_contra hne
      have hmemR : y ∈ Metric.closedBall (0 : Work.SolutionDelivery.R3) R := hsupp t ht_ext y hne
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hmemR
      exact hy (by rw [Work.StabilityFar.mem_coreRegion]; linarith)
  rw [heq] at hind
  exact hind

end Work.SolutionDelivery.Measurable
