import Mathlib
import Submission.Work.Domain.Graph
import Submission.Work.Domain.Theta
import Submission.Work.Domain.Engine.fibreFiniteCrux

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.style.haveILetI false

namespace Work.Domain.Engine

/-- **Finiteness of the fibre from constancy of the second projection.**

Let `g : X ⇢ Y` be an `S`-partial map with `Y` proper over `S`, and let `Γ` be the closure of its
graph, with projections `pr₁ : Γ ⟶ X`, `pr₂ : Γ ⟶ Y`.  If every point of the fibre of `pr₁` over
`x` is mapped by `pr₂` to the same point `y₀`, then that fibre is finite.

The scheme-theoretic form of the statement (that the fibre `(pr₁ S g).fiber x` is a finite scheme)
is `Work.Domain.Engine.fibreFiniteCrux`; here we transport it to the set-theoretic fibre
`pr₁ ⁻¹' {x}` along the homeomorphism `Scheme.Hom.fiberHomeo`. -/
theorem fibreFiniteOfPr2Const {S X Y : AlgebraicGeometry.Scheme} [X.Over S] [Y.Over S]
    [AlgebraicGeometry.IsProper (Work.Domain.overHom S Y)]
    (g : AlgebraicGeometry.Scheme.PartialMap X Y)
    [hg : AlgebraicGeometry.Scheme.PartialMap.IsOver S g] {x : X} {y₀ : Y}
    (h : ∀ γ : Work.Domain.PartialMap.graph S g,
      Work.Domain.PartialMap.pr₁ S g γ = x → Work.Domain.PartialMap.pr₂ S g γ = y₀) :
    (Work.Domain.PartialMap.pr₁ S g ⁻¹' ({x} : Set X)).Finite := by
  haveI : Finite ((Work.Domain.PartialMap.pr₁ S g).fiber x) :=
    fibreFiniteCrux (S := S) g h
  exact Set.finite_coe_iff.mpr
    (Finite.of_equiv _ (AlgebraicGeometry.Scheme.Hom.fiberHomeo
      (Work.Domain.PartialMap.pr₁ S g) x).toEquiv)

end Work.Domain.Engine
