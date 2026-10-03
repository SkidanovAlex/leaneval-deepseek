import Mathlib
import Submission.Work.FIArea2.TsumDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Splitting a prime into the even and the odd case

The local estimate of *FI* Lemma 8.1 at a prime power is proved separately for `p = 2`
(`Work.FIArea2.Tsum_prime_pow_two`) and for odd `p` (`Work.FIArea2.Tsum_prime_pow_odd`); this file
turns the two into the single statement by a case split on the prime.
-/

namespace Work.FIArea2

open scoped BigOperators

/-- The local estimate at `p^ν` from the `2`-primary case and the odd case. -/
theorem Tsum_prime_pow_of_cases
    (H2 : ∀ (ν : ℕ) (hν : 1 ≤ ν) (a h1 h2 : ℤ), IsUnit (a : ZMod (2 ^ ν)) →
      ‖Tsum (2 ^ ν) a h1 h2‖
        ≤ ((ν : ℝ) + 1) ^ 3 * (Nat.gcd (2 ^ ν) ((h1 ^ 2 - a * h2 ^ 2).natAbs) : ℝ))
    (Hodd : ∀ (p : ℕ), p.Prime → Odd p → ∀ (ν : ℕ) (hν : 1 ≤ ν) [NeZero (p ^ ν)]
      (a h1 h2 : ℤ), IsUnit (a : ZMod (p ^ ν)) →
      ‖Tsum (p ^ ν) a h1 h2‖
        ≤ ((ν : ℝ) + 1) ^ 3 * (Nat.gcd (p ^ ν) ((h1 ^ 2 - a * h2 ^ 2).natAbs) : ℝ))
    (p : ℕ) (hp : p.Prime) (ν : ℕ) (hν : 1 ≤ ν) [NeZero (p ^ ν)] (a h1 h2 : ℤ)
    (ha : IsUnit (a : ZMod (p ^ ν))) :
    ‖Tsum (p ^ ν) a h1 h2‖
      ≤ ((ν : ℝ) + 1) ^ 3 * (Nat.gcd (p ^ ν) ((h1 ^ 2 - a * h2 ^ 2).natAbs) : ℝ) := by
  rcases hp.eq_two_or_odd with h | h
  · subst h
    exact H2 ν hν a h1 h2 ha
  · exact Hodd p hp (Nat.odd_iff.mpr h) ν hν a h1 h2 ha

end Work.FIArea2
