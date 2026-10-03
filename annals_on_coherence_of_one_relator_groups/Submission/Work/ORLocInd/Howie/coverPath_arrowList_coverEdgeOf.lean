import Mathlib
import Submission.Work.ORLocInd.Howie.CoverCode

namespace Work.ORLocInd.Howie

/-- The code list of a lifted path is the image under `coverEdgeOf` of its arrow list: the two
recursive definitions (`coverCodeList` appends the code of the last arrow, and `arrowList` appends
that arrow) run in lockstep.  The general statement for an arbitrary base path `p`, which is the
induction that the main theorem below reuses. -/
theorem liftPath_arrowList_map_coverEdgeOf {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (P : Presentation V) (L : Labelling V) (τ : Quiver.Total V → ℤ)
    {a b : V} (p : Quiver.Path a b) (n : ℤ) :
    (liftPath L p n).arrowList.map (coverEdgeOf P L τ) = coverCodeList P L τ p n := by
  induction p with
  | nil =>
    rw [liftPath_nil_cast L a n, Quiver.Path.arrowList_cast_map]
    simp
  | cons p e ih =>
    rw [liftPath_cons_cast L p e n]
    erw [Quiver.Path.arrowList_cast_map]
    erw [Quiver.Path.arrowList_cons]
    rw [coverCodeList_cons, List.map_append, ih]
    simp only [List.map_cons, List.map_nil]
    simp [coverEdgeOf, coverCodeOf]

theorem coverPath_arrowList_coverEdgeOf {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (P : Work.ORLocInd.Howie.Presentation V) (L : Work.ORLocInd.Howie.Labelling V)
    (hrel : Work.ORLocInd.Howie.VanishOnRelators L P) (τ : Quiver.Total V → ℤ)
    (i : P.ι) (n : ℤ) :
    (Work.ORLocInd.Howie.coverPath P L hrel i n).arrowList.map
        (Work.ORLocInd.Howie.coverEdgeOf P L τ) =
      Work.ORLocInd.Howie.coverCodeList P L τ (P.path i) n := by
  rw [coverPath]
  rw [Quiver.Path.arrowList_cast_map]
  exact liftPath_arrowList_map_coverEdgeOf P L τ (P.path i) n

end Work.ORLocInd.Howie
