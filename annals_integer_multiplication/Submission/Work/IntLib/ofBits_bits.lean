import Mathlib
import Submission.Work.IntLib.Basic

namespace Work.IntLib

theorem ofBits_bits (n : ℕ) : Work.IntLib.ofBits n.bits = n := by
  rw [ofBits_eq_ofDigits, bits_map_toNat]
  exact Nat.ofDigits_digits 2 n

end Work.IntLib
