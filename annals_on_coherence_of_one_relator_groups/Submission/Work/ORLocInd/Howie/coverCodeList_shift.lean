import Mathlib
import Submission.Work.ORLocInd.Howie.CoverCode

namespace Work.ORLocInd.Howie

variable {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]

/-- The code of the arrow `(e, n + m)` of the cover is the code of `(e, m)` with its level shifted
by `n`.  This is the pointwise form of `coverCodeList_shift`. -/
theorem codeShift_coverCodeOf (P : Presentation V) (τ : Quiver.Total V → ℤ) {b c : V}
    (e : b ⟶ c) (n m : ℤ) :
    coverCodeOf P τ e (n + m) = codeShift P n (coverCodeOf P τ e m) := by
  simp only [coverCodeOf, codeShift, ofLex_toLex]
  congr 1
  congr 1
  omega

theorem coverCodeList_shift {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (P : Work.ORLocInd.Howie.Presentation V) (L : Work.ORLocInd.Howie.Labelling V)
    (τ : Quiver.Total V → ℤ) {a b : V} (p : Quiver.Path a b) (n : ℤ) :
    Work.ORLocInd.Howie.coverCodeList P L τ p n =
      (Work.ORLocInd.Howie.coverCodeList P L τ p 0).map
        (Work.ORLocInd.Howie.codeShift P n) := by
  induction p with
  | nil => simp
  | cons p e ih =>
    rw [coverCodeList_cons, coverCodeList_cons, ih, List.map_append, List.map_singleton]
    congr 1
    rw [codeShift_coverCodeOf, zero_add]

end Work.ORLocInd.Howie
