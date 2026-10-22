import Mathlib
import Submission.Work.ANALYTIC.CechPt.CechTermDefs

/-!
# The coordinate projections of `cechTerm` jointly separate morphisms

`cechTerm p` is the light profinite set of `(p+1)`-tuples of points of the Cantor set with the
same binary expansion, i.e. (the underlying light profinite set of) the closed subspace
`cechCover p ⊆ C^{p+1}`.  Consequently a morphism into `cechTerm p` is determined by its `p + 1`
coordinate projections: if two maps `S ⟶ cechTerm p` agree after composing with every
`cechProj p j`, they are equal.
-/

open CategoryTheory Limits LightProfinite LightCondensed

namespace Work.ANALYTIC.CechPt

theorem eq_of_cechProj_eq (p : ℕ) {S : LightProfinite.{0}}
    (a b : S ⟶ Work.ANALYTIC.CechPt.cechTerm p)
    (h : ∀ j : Fin (p + 1),
      CategoryTheory.CategoryStruct.comp a (Work.ANALYTIC.CechPt.cechProj p j) =
        CategoryTheory.CategoryStruct.comp b (Work.ANALYTIC.CechPt.cechProj p j)) : a = b := by
  -- The forgetful functor to types is faithful, so it suffices to compare the underlying maps.
  apply ConcreteCategory.ext
  apply ContinuousMap.ext
  intro s
  -- Both values lie in the subtype `cechCover p ⊆ C^{p+1}`, so it suffices to compare coordinates.
  apply Subtype.ext
  funext j
  have hj := ConcreteCategory.congr_hom (h j) s
  simp only [ConcreteCategory.comp_apply] at hj
  rw [Work.ANALYTIC.CechPt.cechProj_apply, Work.ANALYTIC.CechPt.cechProj_apply] at hj
  exact hj

end Work.ANALYTIC.CechPt
