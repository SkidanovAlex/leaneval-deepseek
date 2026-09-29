import Mathlib
import Submission.Work.IntLib.Defs
import Submission.Work.IntLib.Basic
import Submission.Work.IntLib.Shift.Defs

namespace Work.IntLib.Shift

open Work.IntLib

/-- `natOfMSB` (the Horner fold `p ↦ 2p + b` over a most-significant-first bit list) shifts `p`
left by the length of the list and adds the value of the list read as a binary number. -/
theorem natOfMSB_eq (p : ℕ) (R : List Bool) :
    natOfMSB p R = p * 2 ^ R.length + ofBits R.reverse := by
  induction R generalizing p with
  | nil => simp [natOfMSB, ofBits]
  | cons b bs ih =>
    rw [natOfMSB_cons, ih, List.reverse_cons, ofBits_append, List.length_reverse,
      show ofBits [b] = b.toNat from by simp [ofBits], List.length_cons, pow_succ]
    ring

theorem natOfMSBFacts : (∀ (p : ℕ) (R : List Bool), Work.IntLib.Shift.natOfMSB p R = p * 2 ^ R.length + Work.IntLib.ofBits R.reverse) := by
  exact natOfMSB_eq

end Work.IntLib.Shift
