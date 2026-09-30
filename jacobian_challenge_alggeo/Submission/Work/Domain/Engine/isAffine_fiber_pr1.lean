
import Mathlib
import Submission.Work.Domain.Graph
import Submission.Work.Domain.Theta
import Submission.Work.Domain.Engine.affine_fiber_pr1_crux

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.Domain.Engine

/-- **The fibre of `pr₁` over `x` is affine.**  The geometric content is
`Work.Domain.Engine.affine_fiber_pr1_crux`: the fibre is a closed subscheme of an affine scheme
(namely the `S`-fibre `Spec κ(x) ×_S Y` of `Y`), and the hypothesis `h` forces it into the
preimage of the single point `y₀`; the map to `Y` is affine with image `{y₀}`, so the source is
affine. -/
theorem isAffine_fiber_pr1 {S X Y : AlgebraicGeometry.Scheme} [X.Over S] [Y.Over S]
    [AlgebraicGeometry.IsProper (Work.Domain.overHom S Y)]
    (g : AlgebraicGeometry.Scheme.PartialMap X Y)
    [hg : AlgebraicGeometry.Scheme.PartialMap.IsOver S g] {x : X} {y₀ : Y}
    (h : ∀ γ : Work.Domain.PartialMap.graph S g,
      Work.Domain.PartialMap.pr₁ S g γ = x → Work.Domain.PartialMap.pr₂ S g γ = y₀) :
    AlgebraicGeometry.IsAffine ((Work.Domain.PartialMap.pr₁ S g).fiber x) := by
  obtain ⟨B, i, hB, hi⟩ := affine_fiber_pr1_crux (S := S) g h
  haveI : IsAffine B := hB
  haveI : IsClosedImmersion i := hi
  exact isAffine_of_isAffineHom i

end Work.Domain.Engine
