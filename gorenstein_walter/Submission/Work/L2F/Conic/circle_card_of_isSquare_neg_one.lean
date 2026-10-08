import Mathlib
import Submission.Work.L2F.Conic.circle_ncard_conic
import Submission.Work.L2F.Conic.ncard_conic_plus

namespace Work.L2F.Conic

/-- FILE `Submission/Work/L2F/Conic/circle_card_of_isSquare_neg_one.lean`, in `namespace Work.L2F.Conic`.
In a finite field `F` of odd characteristic, if `-1` is a square then the centralizer `circle F = C_{SL(2,F)}(z)` has `q - 1` elements.  This is `Work.L2F.Conic.circle_ncard_conic` combined with `Work.L2F.Conic.ncard_conic_plus`. -/
theorem circle_card_of_isSquare_neg_one (F : Type*) [Field F] [Fintype F] (h2 : (2 : F) ≠ 0)
    (h : IsSquare (-1 : F)) : Nat.card (Work.L2F.circle F) = Nat.card F - 1 := by
  obtain ⟨i, hi⟩ := h
  rw [circle_ncard_conic F, ncard_conic_plus F h2]
  exact ⟨i, hi.symm⟩

end Work.L2F.Conic
