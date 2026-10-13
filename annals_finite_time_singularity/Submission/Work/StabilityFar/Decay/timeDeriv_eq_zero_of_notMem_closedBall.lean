import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.StabilityFar.Defs
import Submission.Work.StabilityFar.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.unusedVariables false

namespace Work.StabilityFar.Decay

theorem timeDeriv_eq_zero_of_notMem_closedBall {ω : Work.StabilityFar.R3 → ℝ → Work.StabilityFar.R3}
    {R t ε : ℝ}
    (hdc : ∀ s ∈ Set.Ioo (t - ε) (t + ε), ∀ y,
      HasDerivAt (fun s' => ω y s') (FiniteTimeSingularity.timeDeriv ω y s) s)
    (hsupp : ∀ s ∈ Set.Ioo (t - ε) (t + ε), ∀ y,
      ω y s ≠ 0 → y ∈ Metric.closedBall 0 R)
    {s : ℝ} (hs : s ∈ Set.Ioo (t - ε) (t + ε)) {y : Work.StabilityFar.R3}
    (hy : y ∉ Metric.closedBall 0 R) :
    FiniteTimeSingularity.timeDeriv ω y s = 0 := by
  refine Work.StabilityFar.timeDeriv_eq_zero_of_eventuallyEq_zero ?_
  filter_upwards [isOpen_Ioo.mem_nhds hs] with s' hs'
  by_contra hne
  exact hy (hsupp s' hs' y hne)

end Work.StabilityFar.Decay
