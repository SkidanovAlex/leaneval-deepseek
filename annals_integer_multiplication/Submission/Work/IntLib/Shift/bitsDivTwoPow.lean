import Mathlib
import Submission.Work.IntLib.Defs
import Submission.Work.IntLib.Shift.Defs

namespace Work.IntLib.Shift

/-- Dropping the `k` least significant bits of `m` is dividing by `2 ^ k`:
`(m / 2 ^ k).bits = m.bits.drop k`. -/
theorem bitsDivTwoPow (m k : ℕ) : (m / 2 ^ k).bits = m.bits.drop k := by
  induction k generalizing m with
  | zero => simp
  | succ k ih =>
    rw [Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul, ih (m / 2)]
    rw [← Nat.div2_val, Nat.div2_bits_eq_tail, ← List.drop_one, List.drop_drop, Nat.add_comm]

end Work.IntLib.Shift
