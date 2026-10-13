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

/-- **Almost-everywhere strong measurability from continuity on a closed ball plus compact
support.**

If `f : ℝ³ → ℝ³` is continuous on the closed ball `B(0,ρ)` and vanishes outside `B(0,R)` with
`R ≤ ρ`, then `f` is a.e. strongly measurable: it agrees with the `B(0,ρ)`-indicator of itself,
which is a.e. strongly measurable for `volume` because `f` is continuous (hence a.e. strongly
measurable) on the measurable set `B(0,ρ)`. -/
theorem aestronglyMeasurable_of_contOn_closedBall {f : Work.SolutionDelivery.R3 → Work.SolutionDelivery.R3}
    {R ρ : ℝ} (hρ : R ≤ ρ)
    (hcont : ContinuousOn f (Metric.closedBall 0 ρ))
    (hsupp : ∀ x : Work.SolutionDelivery.R3, f x ≠ 0 → x ∈ Metric.closedBall 0 R) :
    MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume := by
  have hsub : Metric.closedBall (0 : Work.SolutionDelivery.R3) R ⊆
      Metric.closedBall (0 : Work.SolutionDelivery.R3) ρ :=
    Metric.closedBall_subset_closedBall hρ
  have hms : MeasurableSet (Metric.closedBall (0 : Work.SolutionDelivery.R3) ρ) :=
    Metric.isClosed_closedBall.measurableSet
  -- `f` is a.e. strongly measurable for the measure restricted to the closed ball
  have h1 : AEStronglyMeasurable f
      (volume.restrict (Metric.closedBall (0 : Work.SolutionDelivery.R3) ρ)) :=
    hcont.aestronglyMeasurable hms
  -- hence so is its indicator, for the ambient volume
  have h2 : AEStronglyMeasurable
      ((Metric.closedBall (0 : Work.SolutionDelivery.R3) ρ).indicator f) volume :=
    (aestronglyMeasurable_indicator_iff hms).mpr h1
  -- the support hypothesis turns the indicator into `f` itself
  have heq : (Metric.closedBall (0 : Work.SolutionDelivery.R3) ρ).indicator f = f := by
    funext x
    rcases em (x ∈ Metric.closedBall (0 : Work.SolutionDelivery.R3) ρ) with hx | hx
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      symm
      by_contra hne
      exact hx (hsub (hsupp x hne))
  rwa [heq] at h2

end Work.SolutionDelivery.Measurable
