import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Coercivity.Defs
import Submission.Work.FM.Core2
import Submission.Work.Coercivity.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

/-- Under the Hardy hypotheses, `L₁₂(f)` has derivative `-L12dens K f` at every point of
`(0,∞)` (`Work.FM.hasDerivAt_L12`), hence is differentiable there and therefore
continuous on `(0,∞)`. -/
theorem L12f_continuousOn (f : ℝ → ℝ → ℝ) (hfH : HardyHyp f) :
    ContinuousOn (fun z : ℝ => L12f f z) (Set.Ioi (0 : ℝ)) := by
  have hd : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun x : ℝ => L12f f x) (-(FM.L12dens Spaces.K f z)) z := by
    intro z hz
    exact Work.FM.hasDerivAt_L12 (K := Spaces.K) (f := f) (a := 0) (ρ := z)
      hfH.hint (hfH.hcont z hz) hz
  have hdiff : DifferentiableOn ℝ (fun z : ℝ => L12f f z) (Set.Ioi (0 : ℝ)) :=
    fun z hz => (hd z hz).differentiableAt.differentiableWithinAt
  exact hdiff.continuousOn

end Work.Coercivity
