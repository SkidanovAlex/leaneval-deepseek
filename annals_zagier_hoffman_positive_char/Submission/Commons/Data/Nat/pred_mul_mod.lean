import Mathlib.Algebra.Group.Nat.Defs

namespace Commons.Data.Nat

/-- For `1 ≤ v ≤ q` with `1 ≤ q`, the residue of `(q - 1) * v` modulo `q` is the
`q`-complement `q - v` of `v`. -/
theorem pred_mul_mod {q v : ℕ} (hq : 1 ≤ q) (hv : 1 ≤ v) (hvq : v ≤ q) :
    (q - 1) * v % q = q - v := by
  have hA : v ≤ q * v := by
    simpa using Nat.mul_le_mul_right v hq
  have hB : q ≤ q * v := by
    simpa using Nat.mul_le_mul_left q hv
  have key : (q - 1) * v = q * (v - 1) + (q - v) := by
    rw [Nat.sub_mul, one_mul, Nat.mul_sub_left_distrib, mul_one]
    omega
  rw [key, Nat.add_comm (q * (v - 1)) (q - v), Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (by omega : q - v < q)]

end Commons.Data.Nat