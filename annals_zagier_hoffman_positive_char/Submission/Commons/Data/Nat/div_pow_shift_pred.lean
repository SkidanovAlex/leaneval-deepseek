import Mathlib
import Submission.Commons.Data.Nat.div_pow_add_mul_mod
import Submission.Commons.Data.Nat.div_pow_pow_sub_one_mod

namespace Commons.Data.Nat

/-- The base-`p` digits of `p ^ l * x + (p ^ l - 1)`: all digits below position `l` are `p - 1`,
and the digit at position `j ≥ l` is the digit of `x` at position `j - l`. -/
theorem div_pow_shift_pred (p l x j : ℕ) (hp : 2 ≤ p) :
    (p ^ l * x + (p ^ l - 1)) / p ^ j % p = if j < l then p - 1 else x / p ^ (j - l) % p := by
  have hp0 : 0 < p := by omega
  have hlt : p ^ l - 1 < p ^ l := Nat.sub_one_lt (Nat.pow_pos hp0).ne'
  have h := div_pow_add_mul_mod p l hp (a := p ^ l - 1) (c := x) hlt j
  rcases Nat.lt_or_ge j l with hj | hj
  · rw [if_pos hj] at h ⊢
    rw [h, div_pow_pow_sub_one_mod p l hp (by omega) j, if_pos hj]
  · rw [if_neg (by omega : ¬ j < l)] at h ⊢
    exact h

end Commons.Data.Nat
