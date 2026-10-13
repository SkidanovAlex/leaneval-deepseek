import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SolutionDelivery.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.SolutionDelivery.Integrable

open MeasureTheory

/-- A function on `ℝ³` that is almost-everywhere strongly measurable, vanishes outside
`B(0,R)`, and is pointwise bounded by `M`, is integrable. -/
theorem integrable_of_support_subset_closedBall {f : Work.SolutionDelivery.R3 → Work.SolutionDelivery.R3} {R M : ℝ}
    (hmeas : MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume)
    (hsupp : ∀ x : Work.SolutionDelivery.R3, f x ≠ 0 → x ∈ Metric.closedBall 0 R)
    (hbdd : ∀ x : Work.SolutionDelivery.R3, ‖f x‖ ≤ M) :
    MeasureTheory.Integrable f MeasureTheory.volume := by
  have hsub : Function.support f ⊆ Metric.closedBall (0 : Work.SolutionDelivery.R3) R :=
    fun x hx => hsupp x (Function.mem_support.mp hx)
  have hIntOn : IntegrableOn f (Metric.closedBall (0 : Work.SolutionDelivery.R3) R) volume :=
    IntegrableOn.of_bound (MeasureTheory.measure_closedBall_lt_top (x := (0 : Work.SolutionDelivery.R3)) (r := R))
      hmeas.restrict M (Filter.Eventually.of_forall hbdd)
  exact (integrableOn_iff_integrable_of_support_subset hsub).mp hIntOn

end Work.SolutionDelivery.Integrable
