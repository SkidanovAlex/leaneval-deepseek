import Mathlib
import Submission.Work.SGsep.hand.HandDefs2

namespace Work.SGsep.hand

open Work.SG Work.SG.Data Work.SGsep.Hand Work.SGsep.Hand.Data

/-- Unpacking the handedness check `Data.HandCert.chk` in the `none` case: the element is not a
rotation. -/
theorem chk_none {k i : Nat} (h : HandCert.chk k i none = true) :
    (A3n k i).det ≠ 1 ∨ (A3n k i).ord < 3 := by
  simp only [HandCert.chk, A3n] at h ⊢
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · left; intro hh; rw [hh] at h; simp at h
  · right; exact of_decide_eq_true h

end Work.SGsep.hand
