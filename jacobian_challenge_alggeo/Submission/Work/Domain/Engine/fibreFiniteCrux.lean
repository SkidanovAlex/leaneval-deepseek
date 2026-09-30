import Mathlib
import Submission.Work.Domain.Graph
import Submission.Work.Domain.Theta
import Submission.Work.Domain.Engine.isAffine_fiber_pr1

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Domain.Engine

theorem fibreFiniteCrux {S X Y : AlgebraicGeometry.Scheme} [X.Over S] [Y.Over S]
    [AlgebraicGeometry.IsProper (Work.Domain.overHom S Y)]
    (g : AlgebraicGeometry.Scheme.PartialMap X Y)
    [hg : AlgebraicGeometry.Scheme.PartialMap.IsOver S g] {x : X} {y₀ : Y}
    (h : ∀ γ : Work.Domain.PartialMap.graph S g,
      Work.Domain.PartialMap.pr₁ S g γ = x → Work.Domain.PartialMap.pr₂ S g γ = y₀) :
    Finite ((Work.Domain.PartialMap.pr₁ S g).fiber x) := by
  -- The fibre `Γ_x = (pr₁)⁻¹(x)` is affine: this is the geometric crux.
  haveI hAff : AlgebraicGeometry.IsAffine ((Work.Domain.PartialMap.pr₁ S g).fiber x) :=
    isAffine_fiber_pr1 g h
  -- The structure map `Γ_x ⟶ Spec κ(x)` is affine (both source and target are affine) and
  -- proper (it is a base change of the proper morphism `pr₁`), hence finite.
  have hAffHom : AlgebraicGeometry.IsAffineHom
      ((Work.Domain.PartialMap.pr₁ S g).fiberToSpecResidueField x) :=
    AlgebraicGeometry.isAffineHom_of_isAffine _
  have hProper : AlgebraicGeometry.IsProper
      ((Work.Domain.PartialMap.pr₁ S g).fiberToSpecResidueField x) :=
    AlgebraicGeometry.IsProper.instSndScheme (Work.Domain.PartialMap.pr₁ S g)
      (X.fromSpecResidueField x)
  haveI hFin : AlgebraicGeometry.IsFinite
      ((Work.Domain.PartialMap.pr₁ S g).fiberToSpecResidueField x) :=
    (AlgebraicGeometry.IsFinite.iff_isProper_and_isAffineHom).mpr ⟨hProper, hAffHom⟩
  -- A finite morphism over a field has finite source: `Γ_x` is locally Artinian and compact,
  -- hence an Artinian scheme, whose underlying type is finite.
  haveI hLQF : AlgebraicGeometry.LocallyQuasiFinite
      ((Work.Domain.PartialMap.pr₁ S g).fiberToSpecResidueField x) := inferInstance
  haveI hLA : AlgebraicGeometry.IsLocallyArtinian ((Work.Domain.PartialMap.pr₁ S g).fiber x) :=
    AlgebraicGeometry.IsLocallyArtinian.of_locallyQuasiFinite
      ((Work.Domain.PartialMap.pr₁ S g).fiberToSpecResidueField x)
  haveI hA : AlgebraicGeometry.IsArtinianScheme ((Work.Domain.PartialMap.pr₁ S g).fiber x) :=
    (AlgebraicGeometry.isArtinianScheme_iff ((Work.Domain.PartialMap.pr₁ S g).fiber x)).mpr
      ⟨hLA, inferInstance⟩
  exact AlgebraicGeometry.IsArtinianScheme.finite

end Work.Domain.Engine
