import Mathlib
import Submission.Work.Main.defs

namespace Work.Main.chunks

open Work.Main

/-- Mixed-radix expansion: the base-`B` "digits" `x / B ^ i % B` of `x`, recombined with weights
`B ^ i` for `i < N`, give back `x % B ^ N`.  No hypothesis on `B` is needed (`B = 0` is handled by
the conventions `x / 0 = 0`, `x % 0 = x`).

`Nat.mod_pow_succ` (`x % B ^ (k+1) = x % B ^ k + B ^ k * (x / B ^ k % B)`) is exactly the
induction step. -/
theorem sum_digit_mul_pow (X B N : ℕ) :
    ∑ i ∈ Finset.range N, (X / B ^ i % B) * B ^ i = X % B ^ N := by
  induction N with
  | zero => simp only [Finset.sum_range_zero, pow_zero, Nat.mod_one]
  | succ n ih => rw [Finset.sum_range_succ, ih, Nat.mod_pow_succ, Nat.mul_comm]

/-- The base-`2^b` chunks of `x` (padded with zeros up to `N` chunks) recombine, with weights
`2 ^ (b * i)`, to `x % 2 ^ (b * N)`. -/
theorem sumPchunkMulPow (x b N : ℕ) : ∑ i ∈ Finset.range N, Work.Main.pchunk x b N i * 2 ^ (b * i) = x % 2 ^ (b * N) := by
  have key : ∀ i ∈ Finset.range N,
      pchunk x b N i * 2 ^ (b * i) = (x / (2 ^ b) ^ i % 2 ^ b) * (2 ^ b) ^ i := by
    intro i hi
    have hi' : i < N := Finset.mem_range.mp hi
    rw [pchunk, ite_eq_left hi', pow_mul]
  rw [Finset.sum_congr rfl key, sum_digit_mul_pow, ← pow_mul]

end Work.Main.chunks
