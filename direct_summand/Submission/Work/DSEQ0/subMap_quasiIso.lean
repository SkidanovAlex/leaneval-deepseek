import Mathlib
import Submission.Work.DSEQ0.ChartCompare
import Submission.Work.DSEQ0.subMap_chainMap
import Submission.Work.DSEQ0.surjCech_top

namespace Work.DSEQ0

universe u

theorem subMap_quasiIso {A : Type u} [CommRing A] {X : AlgebraicGeometry.Scheme.{u}}
    {ι : Type u} [Fintype ι] [LinearOrder ι] {f : X ⟶ AlgebraicGeometry.Spec (.of A)}
    (U : ι → X.Opens) (q : ℕ) :
    Nonempty ((DSMap.cech A X f U).homology q
      ≅ (SubCech (A := A) (X := X) (f := f) U).homology q) := by sorry

end Work.DSEQ0
