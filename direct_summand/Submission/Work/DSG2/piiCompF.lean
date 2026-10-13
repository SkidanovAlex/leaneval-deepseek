import Mathlib
import Submission.Work.DSG2.Setup
import Submission.Work.DSG2.phiiCompJ

universe u

open CategoryTheory

namespace Work.DSG2

/-- The composite `pii D i ≫ f : V i ⟶ Spec A` agrees with the restriction of the structure
morphism `Z ⟶ P ⟶ Spec A`. Both factor through `phii D i ≫ j i ≫ ℙ^N_A ⟶ Spec A`, the first
by `phiiCompJ` and `hjComp`, the second by `pi_spec` and `pComp`. -/
theorem piiCompF {A : Type u} [CommRing A] {X : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of A)} (D : Work.DSG2.ChowSetup A X f) (i : Fin D.m) : CategoryTheory.CategoryStruct.comp (Work.DSG2.ChowSetup.pii D i) f = CategoryTheory.CategoryStruct.comp (CategoryTheory.CategoryStruct.comp (Work.DSG2.ChowSetup.Vi D i).ι (Work.DSG2.ChowSetup.Ziota D)) D.πP := by
  rw [ChowSetup.pii, Category.assoc, ← D.hjComp i, ← Category.assoc]
  rw [phiiCompJ D i]
  rw [Category.assoc, ChowSetup.qi, Category.assoc, D.pComp i, Category.assoc]

end Work.DSG2
