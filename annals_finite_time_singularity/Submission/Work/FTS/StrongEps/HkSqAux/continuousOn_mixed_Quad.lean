import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.StrongEps.mixed_Jeps
import Submission.Work.FTS.LocData.SmoothChain

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.HkSqAux

/-- `D_z^j D_θ^i f` is continuous on the open quadrant, for `f` that is `C^n` there for every
`n`.  Immediate from smoothness preservation (`contDiffOn_mixed`) and the fact that a `C^∞`
function is continuous. -/
theorem continuousOn_mixed_Quad {f : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.StrongEps.Quad) (j i : ℕ) :
    ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.mixed j i f q.1 q.2) Work.FTS.StrongEps.Quad := by
  have hsm : ContDiffOn ℝ Work.Stability.smoothOrder (Function.uncurry f)
      Work.FTS.StrongEps.Quad := contDiffOn_infty.mpr hf
  have h := Work.FTS.LocData.contDiffOn_mixed Work.FTS.StrongEps.isOpen_Quad hsm j i
  exact h.continuousOn

end Work.FTS.StrongEps.HkSqAux
