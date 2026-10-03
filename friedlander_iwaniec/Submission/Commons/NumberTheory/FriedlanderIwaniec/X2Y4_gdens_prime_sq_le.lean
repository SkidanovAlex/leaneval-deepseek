import Mathlib
import Submission.Commons.NumberTheory.FriedlanderIwaniec.X2Y4_pair_roots_mod_prime_card
import Submission.Commons.NumberTheory.FriedlanderIwaniec.X2Y4_pair_roots_mod_prime_sq_card

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The local density `g(p²) ≤ g(p)` for `X² + Y⁴`

For the multiplicative local density
`g(d) = #{x² + y⁴ = 0 in ZMod d × ZMod d} / d²`
of the equation `X² + Y⁴ = 0`, we record the elementary bounds at a prime `p`:

* `0 ≤ g (p ^ 2)`;
* `g (p ^ 2) ≤ g p` (reduction mod `p` is at most `p²`-to-one);
* `g (p ^ 2) ≤ 4 / p ^ 2` (the solution set at `p²` is at most `4 p²` pairs);
* `g p < 1` (there are at most `2 p - 1` solutions mod `p`).

These are immediate from the explicit counts
`X2Y4_pair_roots_mod_prime_card` and `X2Y4_pair_roots_mod_prime_sq_card`.
-/

set_option linter.style.haveILetI false

namespace Commons.NumberTheory.FriedlanderIwaniec

theorem X2Y4_gdens_prime_sq_le (p : ℕ) (hp : p.Prime) :
    let g : ℕ → ℝ := fun d =>
      (({x : ZMod d × ZMod d | x.1 ^ 2 + x.2 ^ 4 = 0}.ncard : ℕ) : ℝ) / (d : ℝ) ^ 2
    0 ≤ g (p ^ 2) ∧ g (p ^ 2) ≤ g p ∧ g (p ^ 2) ≤ 4 / (p : ℝ) ^ 2 ∧ g p < 1 := by
  dsimp only
  rw [X2Y4_pair_roots_mod_prime_sq_card hp, X2Y4_pair_roots_mod_prime_card hp]
  have hp1R : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hp2R : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0R : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hden : ((p ^ 2 : ℕ) : ℝ) ^ 2 = (p : ℝ) ^ 4 := by
    rw [show ((p ^ 2 : ℕ) : ℝ) = (p : ℝ) ^ 2 by push_cast; ring]; ring
  have hnum : ((p ^ 2 : ℕ) : ℝ) = (p : ℝ) ^ 2 := by push_cast; ring
  by_cases h2 : p = 2
  · subst h2; norm_num
  · rw [if_neg h2]
    have hpodd : p % 2 = 1 := (Nat.Prime.eq_two_or_odd hp).resolve_left h2
    by_cases h43 : p % 4 = 3
    · rw [if_neg (by omega : ¬ p % 4 = 1), if_pos h43]
      rw [hden, hnum]
      simp only [Nat.cast_one]
      refine ⟨by positivity, ?_, ?_, ?_⟩
      · rw [div_le_div_iff₀ (by positivity) (by positivity)]; ring_nf; nlinarith
      · rw [div_le_div_iff₀ (by positivity) (by positivity)]; ring_nf; nlinarith
      · rw [div_lt_one (by positivity)]; nlinarith [hp2R]
    · rw [if_neg h43, if_neg h2]
      have h41 : p % 4 = 1 := by
        have hlt : p % 4 < 4 := Nat.mod_lt p (by norm_num)
        have hmod2 : (p % 4) % 2 = 1 := by
          rw [Nat.mod_mod_of_dvd p (by norm_num : 2 ∣ 4)]; exact hpodd
        interval_cases p % 4 <;> omega
      rw [if_pos h41]
      have hcastA : ((3 * p ^ 2 - 2 * p : ℕ) : ℝ) = 3 * (p : ℝ) ^ 2 - 2 * (p : ℝ) := by
        rw [Nat.cast_sub (by nlinarith [hp.two_le])]; push_cast; ring
      have hcastB : ((2 * p - 1 : ℕ) : ℝ) = 2 * (p : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ 2 * p)]; push_cast; ring
      rw [hden, hcastA, hcastB]
      refine ⟨?_, ?_, ?_, ?_⟩
      · apply div_nonneg _ (by positivity)
        nlinarith [hp1R]
      · rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hp1R]
      · rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hp1R]
      · rw [div_lt_one (by positivity)]
        nlinarith [hp2R]

end Commons.NumberTheory.FriedlanderIwaniec
