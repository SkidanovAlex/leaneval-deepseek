import Mathlib
import Submission.Work.PlanarSC.Defs
import Submission.Work.PlanarSC.Tools
import Submission.Work.PlanarSC.exists_sqrtCurve

namespace Work.PlanarSC

/-- **A null-winding simple closed curve has an injective continuous square root parametrised by
the circle.**  This is the `HasArg (· - a) 0` form of `Work.PlanarSC.exists_sqrtCurve`: the
hypothesis `HasArg (fun t => circleParam γ t - a) 0` says, after unfolding `HasArg` and
simplifying `· - 0`, exactly `HasArg (circleParam γ) a`. -/
theorem exists_injective_sqrtCurve {γ : C(Circle, ℂ)} (hγ : Function.Injective γ) {a : ℂ}
    (ha : a ∉ Set.range γ)
    (hH : Commons.Topology.Winding.HasArg (fun t : ℝ => Work.PlanarSC.circleParam γ t - a) 0) :
    ∃ k : C(Circle, ℂ), Function.Injective k ∧ ∀ u : Circle, (k u) ^ 2 = γ u - a := by
  have hArg : Commons.Topology.Winding.HasArg (Work.PlanarSC.circleParam γ) a := by
    simpa only [Commons.Topology.Winding.HasArg, sub_zero] using hH
  exact exists_sqrtCurve γ hγ ha hArg

end Work.PlanarSC
