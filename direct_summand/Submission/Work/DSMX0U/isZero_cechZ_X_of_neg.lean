import Mathlib
import Submission.Work.DSMX0U.Basic

namespace Work.DSMX0U

open CategoryTheory AlgebraicGeometry

universe a

theorem isZero_cechZ_X_of_neg {A : Type a} [CommRing A] {X : Scheme.{a}}
    (f : X ⟶ Spec (.of A)) {ι : Type a} (U : ι → X.Opens) :
    ∀ i : ℤ, i < 0 → CategoryTheory.Limits.IsZero ((DSMap.cechZ A X f U).X i) := by
  intro i hi
  refine HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat i (fun n hn => ?_)
  rw [ComplexShape.embeddingUpNat_f] at hn
  omega

end Work.DSMX0U
