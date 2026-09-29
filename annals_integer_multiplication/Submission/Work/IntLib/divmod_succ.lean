import Mathlib

namespace Work.IntLib

/-- One-step division/modulo recursion: `(k+1)/b` and `(k+1)%b` are obtained from
`k/b` and `k%b` by incrementing the remainder, carrying into the quotient when the
remainder wraps around to `b`. -/
theorem divmod_succ (b k : ℕ) (hb : 1 ≤ b) : (k + 1) / b = (if k % b + 1 = b then k / b + 1 else k / b) ∧ (k + 1) % b = (if k % b + 1 = b then 0 else k % b + 1) := by
  have hb0 : 0 < b := hb
  have hk : k = b * (k / b) + k % b := (Nat.div_add_mod k b).symm
  by_cases h : k % b + 1 = b
  · have hk1 : k + 1 = b * (k / b) + b := by omega
    constructor
    · rw [if_pos h, hk1, Nat.mul_add_div hb0, Nat.div_self hb0]
    · rw [if_pos h, hk1, Nat.mul_add_mod, Nat.mod_self]
  · have hlt : k % b + 1 < b := by
      have := Nat.mod_lt k hb0
      omega
    have hk1 : k + 1 = b * (k / b) + (k % b + 1) := by omega
    constructor
    · rw [if_neg h, hk1, Nat.mul_add_div hb0, Nat.div_eq_of_lt hlt, add_zero]
    · rw [if_neg h, hk1, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]

end Work.IntLib
