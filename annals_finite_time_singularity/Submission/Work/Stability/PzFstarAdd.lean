import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.Stability.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Stability

/-- The `z`-slice of the reference profile `F_* = α(Γ/c)·F_{*,rad}` is differentiable at every
`z > -1`: `F_{*,rad}(z) = 2z/(1+z)²` is a rational function whose only pole is at `z = -1`
(`Work.FM.hasDerivAt_Fstar`), and the angular factor `α(Γ(θ)/c)` is a constant of the slice. -/
theorem differentiableAt_Fstar_slice (α θ z : ℝ) (hz : -1 < z) :
    DifferentiableAt ℝ (fun z' => Work.Construction.Fstar α z' θ) z := by
  have h := (Work.FM.hasDerivAt_Fstar z hz).differentiableAt.const_mul
    (α * (Work.Spaces.Gam α θ / Work.Spaces.c α))
  simpa [Work.Construction.Fstar, mul_assoc] using h


end Work.Stability
