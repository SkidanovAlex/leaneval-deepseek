import Mathlib

open CategoryTheory AlgebraicTopology Simplicial Limits

namespace Work.Serre

/-- The simplicial chain complex functor `X ↦ (X.chainComplex R)` preserves coproducts
(i.e. colimits indexed by a discrete category), for coefficients in `R` viewed as a module
over itself.

The functor is the composite of the degreewise "free module" functor
`X ↦ (n ↦ ∐_{x : X_n} R)` — a right-whiskering of `sigmaConst.obj R`, which preserves
colimits because `sigmaConst.obj R` does — with the alternating face map complex, which
preserves colimits because in each degree it is the evaluation functor on the functor
category of simplicial objects.  Since colimits of homological complexes are computed
degreewise, it suffices to check this after applying `HomologicalComplex.eval` in each
degree. -/
theorem chainComplexFunctor_preserves_coproduct (R : Type) [CommRing R] (ι : Type) :
    CategoryTheory.Limits.PreservesColimitsOfShape (CategoryTheory.Discrete ι)
      ((SSet.chainComplexFunctor (ModuleCat R)).obj (ModuleCat.of R R)) := by
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro n
  change PreservesColimitsOfShape (Discrete ι)
    (((CategoryTheory.Functor.whiskeringRight SimplexCategoryᵒᵖ (Type) (ModuleCat R)).obj
        (sigmaConst.obj (ModuleCat.of R R))) ⋙
      (evaluation (SimplexCategoryᵒᵖ) (ModuleCat R)).obj (Opposite.op (SimplexCategory.mk n)))
  infer_instance

end Work.Serre
