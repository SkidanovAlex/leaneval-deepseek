import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.Basic
import Submission.Work.Coercivity.pz_mul_w

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

theorem L_mul_w_deriv {f : ℝ → ℝ → ℝ} {z θ : ℝ} (hz : 0 < z)
    (hf : HasDerivAt (fun z' => f z' θ) (Spaces.pz f z θ) z) :
    L f z θ * Spaces.w z
      = f z θ * Spaces.w z + z * Spaces.pz (fun z θ => f z θ * Spaces.w z) z θ := by
  rw [pz_mul_w (ne_of_gt hz) hf, L_mul_w f z θ hz]

end Work.Coercivity
