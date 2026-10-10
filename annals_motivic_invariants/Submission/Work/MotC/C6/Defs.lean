import Mathlib
import ChallengeDeps
import Submission.Work.TorsorExistence.Defs
import Submission.Work.MotC.Defs
import Submission.Work.MotC.constantsOnly_all

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Node C6 (i): the generic point of a Weierstrass curve

This file fixes the two coordinates of the **generic point** of a Weierstrass curve `W` over a field
`L`, i.e. the images in the function field `K = L(W)` of the classes of `X` and `Y` in the affine
coordinate ring `L[W] = L[X, Y]/(W(X,Y))`:

* `genX W` is `x = [X] ∈ K`,
* `genY W` is `y = [Y] ∈ K`.

They satisfy the Weierstrass equation of `W` (indeed of `W` base changed to any field extension of
`L`), and they are the coordinates of the generic point used by the argument that the twisted curve
times `ℙ¹` is not rational: base changing the generic point along an `L`-algebra map
`K → L(u,v)` produces a point of `W(L(u,v))`, and two applications of the one-variable rigidity
`Work.MotC.exists_baseChange_eq_of_point_ratFunc_all` show that this point is constant.
-/

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine

namespace Work.MotC.C6

noncomputable section

variable {L : Type} [Field L]

/-- The `x`-coordinate `[X]` of the generic point of `W` in its function field. -/
noncomputable def genX (W : WeierstrassCurve L) :
    WeierstrassCurve.Affine.FunctionField W :=
  algebraMap (WeierstrassCurve.Affine.CoordinateRing W)
    (WeierstrassCurve.Affine.FunctionField W)
    (WeierstrassCurve.Affine.CoordinateRing.mk W (Polynomial.C Polynomial.X))

/-- The `y`-coordinate `[Y]` of the generic point of `W` in its function field. -/
noncomputable def genY (W : WeierstrassCurve L) :
    WeierstrassCurve.Affine.FunctionField W :=
  algebraMap (WeierstrassCurve.Affine.CoordinateRing W)
    (WeierstrassCurve.Affine.FunctionField W)
    (AdjoinRoot.root (WeierstrassCurve.Affine.polynomial W))

end

end Work.MotC.C6
