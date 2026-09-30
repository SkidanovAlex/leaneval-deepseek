import Mathlib
import Submission.Work.Domain.Resid.Setup

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.Domain.Resid

open CategoryTheory AlgebraicGeometry

universe u

/-- The germ map `𝒪_{X,x} → K(X)` of an irreducible scheme, followed by `Spec`, is the
specialisation morphism `Spec K(X) ⟶ Spec 𝒪_{X,x}`.  Consequently the composite
`Spec K(X) ⟶ Spec 𝒪_{X,x} ⟶ X` is the canonical morphism from the generic point.

This is `Work.Domain.Resid.fromSpecStalk_algebraMap`, proved here from Mathlib's
`Scheme.SpecMap_stalkSpecializes_fromSpecStalk`, because the definition of the algebra structure
`Algebra (X.presheaf.stalk x) X.functionField` is `stalkSpecializes` of the specialisation of the
generic point to `x` (`AlgebraicGeometry.stalkFunctionFieldAlgebra`). -/
private lemma fromSpecStalk_algebraMap_aux {X : AlgebraicGeometry.Scheme.{u}}
    [IrreducibleSpace X] (x : X) :
    Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField)) ≫
      X.fromSpecStalk x = X.fromSpecStalk (genericPoint X) := by
  have h : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
  have h' : CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) X.functionField) =
      X.presheaf.stalkSpecializes h := by
    rw [RingHom.algebraMap_toAlgebra]
    rfl
  rw [h']
  exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk h

/-- **The generic fibre of the canonical point.**  For an integral `K`-scheme `X`, a point
`x : X` and a ring homomorphism `ρ : 𝒪_{X,x} →+* A` over `K` (in the sense that the composite
`Spec A ⟶ Spec 𝒪_{X,x} ⟶ X` is a morphism over `Spec K`, hypothesis `hKA`) which is compatible
with the structure of `K(X)` as an `A`-algebra (hypothesis `hρ`), the base change of the
canonical `A`-point `canonPt x ρ` along `Spec K(X) ⟶ Spec A` is the generic point of `X`. -/
theorem canonPt_generic {K : Type _} [Field K] {X : Work.GCBasics.Sch K}
    [AlgebraicGeometry.IsIntegral X.left] (x : X.left)
    {A : Type _} [CommRing A] [Algebra K A] [Algebra A X.left.functionField]
    [IsScalarTower K A X.left.functionField]
    (ρ : X.left.presheaf.stalk x →+* A)
    (hKA : (Work.GCBasics.specOf K A).hom = CategoryTheory.CategoryStruct.comp
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom ρ))
      (CategoryTheory.CategoryStruct.comp (X.left.fromSpecStalk x) X.hom))
    (hρ : (algebraMap A X.left.functionField).comp ρ =
      algebraMap (X.left.presheaf.stalk x) X.left.functionField) :
    Work.GCBasics.RPt.map (IsScalarTower.toAlgHom K A X.left.functionField)
      (Work.Domain.Resid.canonPt x ρ hKA) = Work.GCBasics.genericFPt X := by
  have aux := fromSpecStalk_algebraMap_aux (X := X.left) x
  apply Over.OverMorphism.ext
  simp only [Work.GCBasics.RPt.map, Work.GCBasics.specOfMap_left, Over.comp_left,
    Work.Domain.Resid.canonPt_left, Work.GCBasics.genericFPt]
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hcomp : (IsScalarTower.toAlgHom K A X.left.functionField).toRingHom.comp ρ =
      algebraMap (X.left.presheaf.stalk x) X.left.functionField := hρ
  rw [hcomp]
  exact aux

end Work.Domain.Resid
