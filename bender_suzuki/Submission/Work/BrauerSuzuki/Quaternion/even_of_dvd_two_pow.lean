import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BrauerSuzuki.Quaternion

/-- Every divisor `d > 1` of a power of two is even: the divisors of `2 ^ m` are
exactly the powers `2 ^ k` with `k ≤ m`, and `d > 1` forces `k ≠ 0`. -/
theorem even_of_dvd_two_pow {d m : ℕ} (h : d ∣ 2 ^ m) (hd : 1 < d) : Even d := by
  obtain ⟨k, _hk, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h
  rw [even_iff_two_dvd]
  cases k with
  | zero => simp at hd
  | succ k => exact dvd_pow_self 2 (Nat.succ_ne_zero k)

end Work.BrauerSuzuki.Quaternion
