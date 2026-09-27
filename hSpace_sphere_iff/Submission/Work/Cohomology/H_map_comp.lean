import Mathlib
import Submission.Work.Cohomology.Basic
import Submission.Work.Cohomology.Cup
import Submission.Work.Cohomology.coboundary_comp
import Submission.Work.Cohomology.cupOf_coboundary
import Submission.Work.Cohomology.Cohomology

open CategoryTheory Simplicial Opposite

namespace Work.Cohomology

/-- Functoriality of the contravariant map on cohomology: pullback along `f ≫ g` equals
pullback along `g` followed by pullback along `f`. -/
theorem H_map_comp {S T U : SSet.{0}} {R : Type} [CommRing R] (f : S ⟶ T) (g : T ⟶ U) (n : ℕ)
    (x : Submission.Cohomology.H U R n) :
    Submission.Cohomology.H.map R (CategoryTheory.CategoryStruct.comp f g) n x
      = Submission.Cohomology.H.map R f n (Submission.Cohomology.H.map R g n x) := by
  refine Quotient.inductionOn x ?_
  intro a
  change Submission.Cohomology.H.map R (f ≫ g) n (Submission.Cohomology.H.mk a.1 a.2)
      = Submission.Cohomology.H.map R f n
          (Submission.Cohomology.H.map R g n (Submission.Cohomology.H.mk a.1 a.2))
  rw [Submission.Cohomology.H.map_mk, Submission.Cohomology.H.map_mk,
    Submission.Cohomology.H.map_mk]
  rfl

end Work.Cohomology
