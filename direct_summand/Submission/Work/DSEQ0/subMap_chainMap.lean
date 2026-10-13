import Mathlib
import Submission.Work.DSEQ0.ChartCompare

namespace Work.DSEQ0

universe u

theorem subMap_chainMap {A : Type u} [CommRing A] {X : AlgebraicGeometry.Scheme.{u}}
    {ι : Type u} [LinearOrder ι] {f : X ⟶ AlgebraicGeometry.Spec (.of A)} (U : ι → X.Opens)
    (q : ℕ) :
    CategoryTheory.CategoryStruct.comp ((DSMap.cech A X f U).d q (q + 1))
        (subMap (A := A) (X := X) (f := f) U (q + 1))
      = CategoryTheory.CategoryStruct.comp (subMap (A := A) (X := X) (f := f) U q)
        ((SubCech (A := A) (X := X) (f := f) U).d q (q + 1)) := by sorry

end Work.DSEQ0
