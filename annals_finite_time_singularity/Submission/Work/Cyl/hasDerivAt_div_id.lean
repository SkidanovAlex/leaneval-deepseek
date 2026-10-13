import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Cyl

/-- Quotient rule specialised to the denominator `t ↦ t`: if `F` has derivative `c` at `a`
and `a ≠ 0`, then `t ↦ F t / t` has derivative `(c * a - F a) / a ^ 2` at `a`. -/
theorem hasDerivAt_div_id {F : ℝ → ℝ} {c a : ℝ} (h : HasDerivAt F c a) (ha : a ≠ 0) :
    HasDerivAt (fun t : ℝ => F t / t) ((c * a - F a) / a ^ 2) a := by
  change HasDerivAt (F / id) ((c * a - F a) / a ^ 2) a
  simpa only [id_eq, mul_one] using h.div (hasDerivAt_id a) ha

end Work.Cyl
