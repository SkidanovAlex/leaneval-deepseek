import Mathlib
import Submission.Work.Universal.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


open CategoryTheory

namespace Work.Universal

/-- `h`-images of the `n`-fold sum term: composing the sum term of `f` with a monoid
homomorphism `h` is the sum term of `f ≫ h`. -/
theorem sumTerm_comp_hom {K : Type _} [Field K] {C : Work.CurveBasics.Curve K}
    {A B : Work.GCBasics.Sch K} [CategoryTheory.MonObj A] [CategoryTheory.MonObj B]
    [CategoryTheory.IsCommMonObj A] [CategoryTheory.IsCommMonObj B]
    (f : C.toOver ⟶ A) (h : A ⟶ B) [CategoryTheory.IsMonHom h] (n : ℕ) :
    sumTerm C f n ≫ h = sumTerm C (f ≫ h) n := by
  simp only [sumTerm]
  rw [prod_comp]
  simp only [Category.assoc]

/-- The sum morphism `Σᵐ f : Symⁿ C ⟶ A` is natural in the target: composing it with a monoid
homomorphism `h : A ⟶ B` gives the sum morphism of `f ≫ h`. -/
theorem sumMap_comp_hom {K : Type _} [Field K] {C : Work.CurveBasics.Curve K}
    {P0 : Work.AbVar.Point C.toOver} [Work.SpecLin.DivBase C]
    (D : Work.GroupChunk.Input C P0) [Work.Universal.SymQuotData C P0 D]
    {A B : Work.GCBasics.Sch K} [CategoryTheory.GrpObj A] [CategoryTheory.IsCommMonObj A]
    [CategoryTheory.GrpObj B] [CategoryTheory.IsCommMonObj B]
    (f : C.toOver ⟶ A) (h : A ⟶ B) [CategoryTheory.IsMonHom h] (n : ℕ) :
    CategoryTheory.CategoryStruct.comp (Work.Universal.sumMap D f n) h
      = Work.Universal.sumMap D (CategoryTheory.CategoryStruct.comp f h) n := by
  refine sumMap_unique D (f ≫ h) n ?_
  rw [← Category.assoc, sumMap_spec]
  exact sumTerm_comp_hom f h n

end Work.Universal
