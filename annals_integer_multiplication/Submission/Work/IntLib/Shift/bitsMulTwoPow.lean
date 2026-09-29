import Mathlib
import Submission.Work.IntLib.Defs
import Submission.Work.IntLib.Shift.Defs

namespace Work.IntLib.Shift

/-- Shifting by `k` appends `k` zero (least significant) bits to the bit representation:
`(m * 2^k).bits = replicate k false ++ m.bits` for `m ≠ 0`. -/
theorem bitsMulTwoPow (m k : ℕ) (hm : m ≠ 0) : (m * 2 ^ k).bits = List.replicate k false ++ m.bits := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hpos : m * 2 ^ k ≠ 0 := Nat.mul_ne_zero hm (pow_ne_zero k (by norm_num))
    have h : m * 2 ^ (k + 1) = 2 * (m * 2 ^ k) := by ring
    rw [h, Nat.bit0_bits _ hpos, ih]
    simp [List.replicate_succ]

end Work.IntLib.Shift
