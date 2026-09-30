import Mathlib
import Submission.Work.SpecLin.Conventions

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# Extension of points along the generic point: the valuative criterion for properness

Let `A` be a proper `K`-scheme (`K` a field), let `R` be a valuation ring which is a `K`-algebra
and let `x : Spec (FractionRing R) ⟶ A` be an `R`-generic valued point of `A`.  Then `x` extends
to an actual `R`-valued point of `A`: there is `X : Spec R ⟶ A` over `Spec K` with
`genPt R ≫ X = x`.

This is exactly the existence half of the valuative criterion for proper morphisms
(`AlgebraicGeometry.IsProper.eq_valuativeCriterion`), stated in the `Work.SpecLin`
conventions.
-/

open CategoryTheory Limits AlgebraicGeometry

namespace Work.KeyLemma.Curve

universe u

/-- **Existence part of the valuative criterion, in `SpecLin` conventions.** -/
theorem exists_extension_of_proper {K : Type u} [Field K] {R : Type u} [CommRing R] [IsDomain R]
    [ValuationRing R] [Algebra K R] {A : Work.SpecLin.Sch K} [AlgebraicGeometry.IsProper A.hom]
    (x : Work.SpecLin.FPt A (FractionRing R)) :
    ∃ X : Work.SpecLin.RPt A R,
      CategoryTheory.CategoryStruct.comp (Work.SpecLin.genPt R) X = x := by
  -- Properness gives the existence part of the valuative criterion.
  have hVC : ValuativeCriterion A.hom := by
    have h : ((ValuativeCriterion ⊓ @QuasiCompact ⊓ @QuasiSeparated ⊓ @LocallyOfFiniteType)
        A.hom) := by
      rw [← IsProper.eq_valuativeCriterion]
      exact inferInstance
    exact h.1.1.1
  -- The square `Spec (FractionRing R) ⟶ A`, `Spec R ⟶ Spec K` commutes over `Spec K`.
  have hcomp : (algebraMap R (FractionRing R)).comp (algebraMap K R) =
      algebraMap K (FractionRing R) :=
    RingHom.ext fun k => (IsScalarTower.algebraMap_apply K R (FractionRing R) k).symm
  have hcomm : x.left ≫ A.hom =
      Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K R)) := by
    rw [x.w, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]
    rfl
  -- the valuative commutative square
  let S : ValuativeCommSq A.hom :=
    { R := R
      K := FractionRing R
      i₁ := x.left
      i₂ := Spec.map (CommRingCat.ofHom (algebraMap K R))
      commSq := ⟨hcomm⟩ }
  obtain ⟨l, hl₁, hl₂⟩ := (ValuativeCriterion.existence hVC S).exists_lift
  -- `l` is the wanted `R`-valued point of `A`
  refine ⟨Over.homMk l hl₂, ?_⟩
  apply Over.OverMorphism.ext
  exact hl₁

end Work.KeyLemma.Curve
