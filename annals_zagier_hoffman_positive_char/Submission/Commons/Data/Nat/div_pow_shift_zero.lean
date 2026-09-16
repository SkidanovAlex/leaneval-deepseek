import Mathlib
import Submission.Commons.Data.Nat.div_pow_add_mul_mod

/-!
# Base-`p` digits of `p ^ l * x`

Multiplying `x` by `p ^ l` shifts its base-`p` digits up by `l` places.  Hence the
`j`-th base-`p` digit of `p ^ l * x` is `0` for `j < l`, and equals the
`(j - l)`-th digit of `x` for `j ≥ l`.

This is the special case `a = 0` of the concatenation formula
`Commons.Data.Nat.div_pow_add_mul_mod`.
-/

namespace Commons.Data.Nat

/-- The base-`p` digits of `p ^ l * x`: all digits below position `l` vanish, and the digit at
position `j ≥ l` is the digit of `x` at position `j - l`. -/
theorem div_pow_shift_zero (p l x j : ℕ) (hp : 2 ≤ p) :
    p ^ l * x / p ^ j % p = if j < l then 0 else x / p ^ (j - l) % p := by
  have hp0 : 0 < p := by omega
  have h := div_pow_add_mul_mod p l hp (a := 0) (c := x) (Nat.pow_pos hp0) j
  simpa using h

end Commons.Data.Nat
