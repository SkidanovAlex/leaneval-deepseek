import Mathlib

namespace Work.PTCert.digits

theorem sum_mul_pow_lt_pow {b : ℕ} (hb : 2 ≤ b) (d : ℕ → ℕ) (n : ℕ) (hd : ∀ j < n, d j < b) :
    ∑ j ∈ Finset.range n, d j * b ^ j < b ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hdn : d n < b := hd n (Nat.lt_succ_self n)
    have ih' : ∑ j ∈ Finset.range n, d j * b ^ j < b ^ n :=
      ih (fun j hj => hd j (Nat.lt_succ_of_lt hj))
    calc
      ∑ j ∈ Finset.range n, d j * b ^ j + d n * b ^ n
          < b ^ n + d n * b ^ n := Nat.add_lt_add_right ih' _
      _ = (d n + 1) * b ^ n := by ring
      _ ≤ b * b ^ n := by
          apply Nat.mul_le_mul_right
          omega
      _ = b ^ (n + 1) := by rw [pow_succ]; ring

end Work.PTCert.digits
