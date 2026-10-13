import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine.ZTracesAux

/-- The weight `w(z) = (1+z)²/z²` is differentiable at every `z ≠ 0`, with
derivative `-2(1+z)/z³`. -/
theorem hasDerivAt_w (z : ℝ) (hz : z ≠ 0) :
    HasDerivAt Work.Spaces.w (-2 * (1 + z) / z ^ 3) z := by
  change HasDerivAt (fun z : ℝ => (1 + z) ^ 2 / z ^ 2) (-2 * (1 + z) / z ^ 3) z
  have h1 : HasDerivAt (fun z : ℝ => (1 + z) ^ 2) (2 * (1 + z)) z := by
    have h : HasDerivAt (fun z : ℝ => 1 + z) 1 z := (hasDerivAt_id z).const_add 1
    have h2 := h.pow 2
    convert h2 using 1
    ring
  have h2 : HasDerivAt (fun z : ℝ => z ^ 2) (2 * z) z := by
    have h := hasDerivAt_pow 2 z
    convert h using 1
    ring
  have hd := h1.div h2 (by positivity)
  convert hd using 1
  field_simp
  ring

end Work.FTS.EpsEngine.ZTracesAux
