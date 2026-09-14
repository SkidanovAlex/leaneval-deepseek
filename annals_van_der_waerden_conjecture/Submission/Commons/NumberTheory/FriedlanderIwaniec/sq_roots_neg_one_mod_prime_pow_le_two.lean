import Mathlib
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sq_roots_neg_one_mod_prime_pow_eq_two
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sq_roots_neg_one_mod_prime_pow_eq_zero

namespace Commons.NumberTheory.FriedlanderIwaniec

/-- For an odd prime `p` the residue of `p` modulo `4` is `1` or `3`. -/
private lemma prime_mod_four_eq_one_or_three {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) :
    p % 4 = 1 ∨ p % 4 = 3 := by
  rcases hp.eq_two_or_odd with h | h
  · exact absurd h hpodd
  · omega

/-- The number of square roots of `-1` in `ZMod (p ^ e)`, for `p` an odd prime
and `e ≥ 1`, is at most `2`.  Indeed, if `p ≡ 1 (mod 4)` there are exactly two
solutions, while if `p ≡ 3 (mod 4)` there are none. -/
theorem sq_roots_neg_one_mod_prime_pow_le_two {p e : ℕ} (hp : p.Prime) (hpodd : p ≠ 2)
    (he : 1 ≤ e) : ({α : ZMod (p ^ e) | α ^ 2 = -1}.ncard) ≤ 2 := by
  rcases prime_mod_four_eq_one_or_three hp hpodd with h4 | h4
  · rw [sq_roots_neg_one_mod_prime_pow_eq_two hp h4 he]
  · rw [sq_roots_neg_one_mod_prime_pow_eq_zero hp h4 he]
    omega

end Commons.NumberTheory.FriedlanderIwaniec
