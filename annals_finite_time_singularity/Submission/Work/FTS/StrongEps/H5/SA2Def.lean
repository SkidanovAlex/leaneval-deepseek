import Mathlib.Basic.Real.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.GammaW_Prelim
import Submission.Work.FTS.StrongEps.ClassCRHS.StarAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology

namespace Work.FTS.StrongEps.H5

set_option autoImplicit false

/-- The angular profile `α · D_θ²Γ / c(α)` of `D_θ(D_θ F_*)`: the third `F_*`-angular profile,
sitting next to `ClassCRHS.SA0 = αΓ/c` and `ClassCRHS.SA1 = α D_θΓ/c`.  With `D_θ = sin 2θ ∂_θ`,
one has `D_θ(D_θ F_*) = SA2 α θ · SR0 z` and `φ · D_θ(D_θ F_*) = SA2 α θ · SR0 z` on the open
quadrant. -/
def SA2 (α θ : ℝ) : ℝ :=
  α * Work.Spaces.dthU^[2] (fun t => Work.Spaces.Gam α t) θ / Work.Spaces.c α

end Work.FTS.StrongEps.H5
