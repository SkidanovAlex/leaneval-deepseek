import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Tactic.NormNum.Ineq
import Submission.Commons.Data.Nat.div_pow_add_mul_mod
import Submission.Commons.Data.Nat.div_pow_pow_sub_one_mod

/-!
# The base-`p` "no carry" condition is invariant under the shift `(a,b) ↦ (p^k a, p^k b + p^k - 1)`

Let `p ≥ 2`.  Write `a_i = a / p ^ i % p` for the `i`-th base-`p` digit of `a`
(least significant digit `i = 0`).  The condition `a_i + b_i < p` for all `i`
says that adding `a` and `b` in base `p` produces no carries.

Multiplying by `p ^ k` shifts the digits up by `k` places.  Because the low `k`
digits of `p ^ k * b` are all zero, adding `p ^ k - 1` (whose base-`p` digits
are `p - 1` in positions `0, …, k - 1`) fills them with `p - 1` and creates no
carry.  Hence the pair `(p ^ k * a, p ^ k * b + (p ^ k - 1))` satisfies the
no-carry condition exactly when `(a, b)` does, which is the content of this
lemma.

The two digit computations are provided by the commons lemmas
`Commons.Data.Nat.div_pow_add_mul_mod` and
`Commons.Data.Nat.div_pow_pow_sub_one_mod`.
-/

namespace Commons.Data.Nat

theorem noCarry_pow_mul_shift (p k : ℕ) (hp : 2 ≤ p) (a b : ℕ) : (∀ i : ℕ, (p ^ k * a) / p ^ i % p + (p ^ k * b + (p ^ k - 1)) / p ^ i % p < p) ↔ (∀ i : ℕ, a / p ^ i % p + b / p ^ i % p < p) := by
  have hp0 : 0 < p := by omega
  have hpk_pos : 0 < p ^ k := pow_pos hp0 k
  have hpk_sub : p ^ k - 1 < p ^ k := Nat.sub_lt hpk_pos (by norm_num)
  -- digits of `p ^ k * a`: the `i`-th digit is `0` for `i < k`, else that of `a` shifted down.
  have hA : ∀ i, (p ^ k * a) / p ^ i % p = if i < k then 0 else a / p ^ (i - k) % p := by
    intro i
    have h := div_pow_add_mul_mod p k hp (a := 0) (c := a) hpk_pos i
    simpa using h
  -- digits of `p ^ k * b + (p ^ k - 1)`: the `i`-th digit is `p - 1` for `i < k`,
  -- else that of `b` shifted down.
  have hB : ∀ i, (p ^ k * b + (p ^ k - 1)) / p ^ i % p = if i < k then p - 1 else b / p ^ (i - k) % p := by
    intro i
    have h := div_pow_add_mul_mod p k hp (a := p ^ k - 1) (c := b) hpk_sub i
    by_cases hik : i < k
    · rw [h, if_pos hik, if_pos hik]
      rw [div_pow_pow_sub_one_mod p k hp (by omega) i, if_pos hik]
    · rw [h, if_neg hik, if_neg hik]
  constructor
  · intro H j
    have Hj := H (k + j)
    rw [hA (k + j), hB (k + j)] at Hj
    have h1 : ¬ (k + j < k) := by omega
    rw [if_neg h1, if_neg h1, Nat.add_sub_cancel_left] at Hj
    exact Hj
  · intro H i
    rw [hA i, hB i]
    by_cases hik : i < k
    · rw [if_pos hik, if_pos hik]
      omega
    · rw [if_neg hik, if_neg hik]
      exact H (i - k)

end Commons.Data.Nat