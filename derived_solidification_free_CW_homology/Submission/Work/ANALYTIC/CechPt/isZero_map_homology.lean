import Mathlib

namespace Work.ANALYTIC.CechPt

theorem isZero_map_homology {C : Type*} {D : Type*} [CategoryTheory.Category C]
    [CategoryTheory.Category D] [CategoryTheory.Abelian C] [CategoryTheory.Abelian D]
    (F : CategoryTheory.Functor C D) [F.Additive]
    [CategoryTheory.Limits.PreservesFiniteLimits F]
    [CategoryTheory.Limits.PreservesFiniteColimits F] (K : ChainComplex C ℕ)
    (i : ℕ) (h : CategoryTheory.Limits.IsZero (K.homology i)) :
    CategoryTheory.Limits.IsZero
      (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K).homology i) := by
  -- `F` is exact, hence preserves homology of short complexes.
  have : F.PreservesHomology := CategoryTheory.Functor.preservesHomologyOfExact F
  -- `F` sends the zero object `K.homology i` to a zero object.
  have hz : CategoryTheory.Limits.IsZero (F.obj (K.homology i)) := F.map_isZero h
  -- the `i`-th short complex of the image complex is the image of `K.sc i`
  -- (`HomologicalComplex.sc` and `Functor.mapHomologicalComplex` commute definitionally),
  -- and `F` identifies their homologies.
  exact CategoryTheory.Limits.IsZero.of_iso hz
    (CategoryTheory.ShortComplex.mapHomologyIso (K.sc i) F)

end Work.ANALYTIC.CechPt
