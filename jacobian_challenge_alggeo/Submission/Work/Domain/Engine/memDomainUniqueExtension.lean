import Mathlib
import Submission.Work.Domain.Graph
import Submission.Work.Domain.Theta
import Submission.Work.Domain.Ring
import Submission.Work.Domain.Engine.memDomainFiniteFibre
import Submission.Work.Domain.Engine.fibreValue
import Submission.Work.Domain.Engine.fibreFiniteOfPr2Const

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Domain.Engine

theorem memDomainUniqueExtension {S X Y : AlgebraicGeometry.Scheme} [X.Over S] [Y.Over S]
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsLocallyNoetherian X]
    [AlgebraicGeometry.IsProper (Work.Domain.overHom S Y)]
    (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (g : AlgebraicGeometry.Scheme.PartialMap X Y)
    [hg : AlgebraicGeometry.Scheme.PartialMap.IsOver S g] (x : X) (y₀ : Y)
    (H : ∀ (A : ValuationSubring X.functionField)
        (hA : ∀ s : X.presheaf.stalk x,
          algebraMap (X.presheaf.stalk x) X.functionField s ∈ A)
        (_ : IsLocalHom ((algebraMap (X.presheaf.stalk x) X.functionField).codRestrict
          A.toSubring hA))
        (ψ : AlgebraicGeometry.Spec (CommRingCat.of A) ⟶ Y),
        CategoryTheory.CategoryStruct.comp ψ (Work.Domain.overHom S Y) =
          CategoryTheory.CategoryStruct.comp
            (CategoryTheory.CategoryStruct.comp
              (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
                ((algebraMap (X.presheaf.stalk x) X.functionField).codRestrict A.toSubring hA)))
              (AlgebraicGeometry.Scheme.fromSpecStalk X x))
            (Work.Domain.overHom S X) →
        CategoryTheory.CategoryStruct.comp
            (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap A X.functionField))) ψ =
          AlgebraicGeometry.Scheme.PartialMap.fromFunctionField g →
        ψ (IsLocalRing.closedPoint A) = y₀) :
    x ∈ g.toRationalMap.domain := by
  -- The valuative hypothesis `H` says exactly that the second projection of the graph closure
  -- is constant `= y₀` on the fibre of `pr₁` over `x` (`fibreValue`), hence that fibre is a
  -- single point, in particular finite (`fibreFiniteOfPr2Const`).  The domain engine
  -- (`memDomainFiniteFibre`) then promotes finiteness of the fibre to membership of `x` in the
  -- domain of definition of the rational map.
  apply memDomainFiniteFibre (S := S) hX g
  apply fibreFiniteOfPr2Const (S := S) g
  intro γ hγ
  exact fibreValue (S := S) g H γ hγ

end Work.Domain.Engine
