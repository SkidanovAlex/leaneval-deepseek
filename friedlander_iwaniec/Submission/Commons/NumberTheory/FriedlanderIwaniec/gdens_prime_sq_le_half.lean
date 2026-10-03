import Mathlib
import Submission.Commons.NumberTheory.FriedlanderIwaniec.gdens_le_one
import Submission.Commons.NumberTheory.FriedlanderIwaniec.X2Y4_pair_roots_mod_prime_sq_card

namespace Commons.NumberTheory.FriedlanderIwaniec

/-- The local density `g(d) = N(d)/d²` of `x² + y⁴ = 0`, evaluated at the
square `p²` of a prime, is at most `1/2`.  This is the elementary input to the
Friedlander–Iwaniec sieve: it is read off from the explicit local counts
`X2Y4_pair_roots_mod_prime_sq_card`. -/
theorem gdens_prime_sq_le_half {p : ℕ} (hp : p.Prime) : Submission.gdens (p ^ 2) ≤ 1/2 := by
  have hcard := X2Y4_pair_roots_mod_prime_sq_card hp
  rw [Submission.gdens]
  unfold Submission.N
  rw [hcard]
  have hq2 : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp.two_le
  have hden : ((((p ^ 2 : ℕ)) : ℚ)) ^ 2 = (p : ℚ) ^ 4 := by
    rw [Nat.cast_pow]; ring
  rw [hden]
  by_cases h2 : p = 2
  · subst h2
    norm_num
  · rw [if_neg h2]
    by_cases h41 : p % 4 = 1
    · rw [if_pos h41]
      have hq5 : (5 : ℚ) ≤ (p : ℚ) := by
        have h5 : 5 ≤ p := by have h := hp.two_le; omega
        exact_mod_cast h5
      have hcast : ((3 * p ^ 2 - 2 * p : ℕ) : ℚ) = 3 * (p : ℚ) ^ 2 - 2 * (p : ℚ) := by
        have hle : 2 * p ≤ 3 * p ^ 2 := by nlinarith [hp.two_le]
        rw [Nat.cast_sub hle]; push_cast; ring
      rw [hcast, div_le_iff₀ (by positivity)]
      nlinarith [sq_nonneg ((p : ℚ)), sq_nonneg ((p : ℚ) - 5)]
    · rw [if_neg h41]
      push_cast
      rw [div_le_iff₀ (by positivity)]
      have hprod : (0 : ℚ) ≤ (p : ℚ) ^ 2 * ((p : ℚ) ^ 2 - 2) :=
        mul_nonneg (sq_nonneg _) (by nlinarith [hq2])
      nlinarith [hprod]

end Commons.NumberTheory.FriedlanderIwaniec
