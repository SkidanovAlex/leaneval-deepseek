import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle

namespace Work.SSGRoute.ExtConeLift

open CategoryTheory Limits CochainComplex HomComplex

universe u v w

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- The connecting morphism `hS.singleδ` attached to a short exact sequence of objects of `C` is the
connecting morphism `triangleOfSESδ` of the short exact sequence of cochain complexes obtained by
applying the single functor `singleFunctor C 0` to `S`.  (The two are related by the conjugation
isomorphisms `singleFunctorsPostcompQIso`, which are the identity.) -/
theorem single_delta_eq_triangleOfSES_delta {C : Type u} [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C] {S : ShortComplex C} (hS : S.ShortExact) :
    hS.singleδ = DerivedCategory.triangleOfSESδ
      (hS.map_of_exact (HomologicalComplex.single C (ComplexShape.up ℤ) 0)) := by
  rw [ShortComplex.ShortExact.singleδ]

end Work.SSGRoute.ExtConeLift
