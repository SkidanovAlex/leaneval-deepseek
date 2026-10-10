import Mathlib
import Submission.Work.MotC.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The marked point is Galois-fixed (`MotC`, audit node C1)

The marked point `P ∈ E(L)` of a `QuinticTwist` datum is the base change of the rational point
`D.P ∈ E(𝕜)` (`Work.MotC.markPoint`), and the Galois action `Work.MotC.galPoint D` is the map on
points induced by the chosen generator `σ ∈ Gal(L/𝕜)` (`D.sigma`, an element of `L ≃ₐ[𝕜] L`).
Since `σ` is a `𝕜`-algebra automorphism, it acts trivially on the image of `𝕜` in `L`, hence on
points coming from `𝕜`:

`σ(P) = P`, i.e. `galPoint D (markPoint D) = markPoint D`.

This is the point-level counterpart of `coeffCoordEquiv_algebraMap` (the coefficient action fixes
the constants of `L[E]`), and it is the input identifying the Galois action on `E(L)` with the
trivial action on the marked `5`-torsion point used to build the twisted-translation automorphism
`twistAut D τ` of node C1.

Formally it is exactly Mathlib's `WeierstrassCurve.Affine.Point.map_baseChange`:
`map f (baseChange F K P) = baseChange F L P` for `f : K →ₐ[F] L`.
-/

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine

namespace Work.MotC

noncomputable section

variable {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]

/-- **The marked point is fixed by the Galois action.** The generator `σ` of `Gal(L/𝕜)` is a
`𝕜`-algebra automorphism, so it acts trivially on `E(L)` on the base-changed rational point
`P ∈ E(L)`. -/
theorem galPoint_markPoint {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜]
    (D : Work.TorsorExistence.QuinticTwist 𝕜) :
    Work.MotC.galPoint D (Work.MotC.markPoint D) = Work.MotC.markPoint D := by
  simp only [Work.MotC.galPoint, Work.MotC.markPoint]
  exact WeierstrassCurve.Affine.Point.map_baseChange (W' := D.E) D.sigma.toAlgHom D.P

end

end Work.MotC
