import Mathlib

universe u v

namespace Work.DSG1

/-- The comparison isomorphism underlying `homologyFunctor_Q_obj_iso`: the `q`-th homology of the
image `DerivedCategory.Plus.Q.obj K` of a bounded-below complex `K` in the bounded-below derived
category is the `q`-th homology of `K`.

It is the composite of the image under `DerivedCategory.homologyFunctor C q` of the structural
isomorphism `DerivedCategory.Plus.QCompιIso C :
DerivedCategory.Plus.Q ⋙ DerivedCategory.Plus.ι ≅
CochainComplex.Plus.ι C ⋙ DerivedCategory.Q` (at the object `K`) with the structural
isomorphism `DerivedCategory.homologyFunctorFactors C q :
DerivedCategory.Q ⋙ DerivedCategory.homologyFunctor C q ≅
HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) q`. -/
noncomputable def homologyFunctor_Q_obj_iso' {C : Type u} [CategoryTheory.Category.{v} C]
    [CategoryTheory.Abelian C] [HasDerivedCategory C] (K : CochainComplex.Plus C) (q : ℤ) :
    (DerivedCategory.Plus.homologyFunctor C q).obj (DerivedCategory.Plus.Q.obj K) ≅
      (CochainComplex.Plus.ι C).obj K |>.homology q :=
  (DerivedCategory.homologyFunctor C q).mapIso ((DerivedCategory.Plus.QCompιIso C).app K) ≪≫
    (DerivedCategory.homologyFunctorFactors C q).app ((CochainComplex.Plus.ι C).obj K)

/-- The homology of the image in the bounded-below derived category of a bounded-below complex is
the homology of the complex.

Proof: `DerivedCategory.Plus.homologyFunctor C q = DerivedCategory.Plus.ι ⋙
DerivedCategory.homologyFunctor C q` by definition, so the left-hand side is the
`q`-th homology of `DerivedCategory.Plus.ι.obj (DerivedCategory.Plus.Q.obj K)`, and
`DerivedCategory.Plus.QCompιIso : DerivedCategory.Plus.Q ⋙ DerivedCategory.Plus.ι ≅
CochainComplex.Plus.ι C ⋙ DerivedCategory.Q` rewrites this to
`(DerivedCategory.homologyFunctor C q).obj (DerivedCategory.Q.obj ((CochainComplex.Plus.ι C).obj K))`,
which `DerivedCategory.homologyFunctorFactors C q` identifies with the complex-level homology. -/
theorem homologyFunctor_Q_obj_iso {C : Type u} [CategoryTheory.Category.{v} C]
    [CategoryTheory.Abelian C] [HasDerivedCategory C] (K : CochainComplex.Plus C) (q : ℤ) :
    Nonempty ((DerivedCategory.Plus.homologyFunctor C q).obj
        (DerivedCategory.Plus.Q.obj K) ≅
      (CochainComplex.Plus.ι C).obj K |>.homology q) := by
  exact ⟨homologyFunctor_Q_obj_iso' K q⟩

end Work.DSG1
