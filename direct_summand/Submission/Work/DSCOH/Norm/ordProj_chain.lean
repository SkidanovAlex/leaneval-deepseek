import Mathlib
import Submission.Work.DSCOH.Norm.Maps

namespace Work.DSCOH.Norm

open CategoryTheory Limits Opposite TopologicalSpace
open scoped Simplicial BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u v w

theorem ordProj_chain {X : Type u} [TopologicalSpace X] {A : Type v} [CommRing A]
    {ι : Type w} [Fintype ι] [LinearOrder ι]
    [CategoryTheory.Limits.HasProducts (ModuleCat A)]
    (P : CategoryTheory.Functor (Opposite (TopologicalSpace.Opens X)) (ModuleCat A))
    (U : ι → TopologicalSpace.Opens X) (n : ℕ) :
    CategoryTheory.CategoryStruct.comp (Work.DSCOH.Norm.ordProj P U n)
        (Work.DSCOH.Norm.ordD P U n)
      = CategoryTheory.CategoryStruct.comp (Work.DSCOH.Norm.semiD P U n)
          (Work.DSCOH.Norm.ordProj P U (n + 1)) := by
  apply Pi.hom_ext
  intro x
  simp only [Category.assoc, Work.DSCOH.Norm.ordD, Work.DSCOH.Norm.semiD, Work.DSCOH.Norm.ordProj,
    Pi.lift_comp_π]
  simp only [Preadditive.comp_sum, Preadditive.comp_zsmul, Pi.lift_comp_π_assoc]

end Work.DSCOH.Norm
