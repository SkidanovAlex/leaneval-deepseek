import Mathlib
import Submission.Commons.NumberTheory.FriedlanderIwaniec.X2Y4_density_prime_sum_powLog
import Submission.Commons.NumberTheory.FriedlanderIwaniec.X2Y4_pair_roots_mod_prime_card

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Commons.NumberTheory.FriedlanderIwaniec

/-- Casting `p : ℕ` to `ZMod 4` through `ℤ` is the same as the direct cast. -/
private lemma natCast_intCast_zmod4 (p : ℕ) :
    ((p : ℤ) : ZMod 4) = ((p : ℕ) : ZMod 4) := by
  push_cast
  ring

/-- **Pointwise comparison of the local densities.**  For a prime `p`, the local
density `N_p / p²` of the set `{x : ZMod p × ZMod p | x.1 ^ 2 + x.2 ^ 4 = 0}`
equals the Euler factor `(1 + χ₄(p))/p - χ₄(p)/p²` appearing in
`X2Y4_density_prime_sum_powLog`.  Indeed `N_p = 2p - 1` for `p ≡ 1 (mod 4)`,
`N_p = 1` for `p ≡ 3 (mod 4)` and `N_p = 2` for `p = 2`. -/
private lemma dens_summand_eq (p : ℕ) (hp : p.Prime) :
    (({x : ZMod p × ZMod p | x.1 ^ 2 + x.2 ^ 4 = 0}.ncard : ℕ) : ℝ) / (p : ℝ) ^ 2
      = (1 + ((ZMod.χ₄ ((p : ℤ) : ZMod 4) : ℤ) : ℝ)) / (p : ℝ)
        - ((ZMod.χ₄ ((p : ℤ) : ZMod 4) : ℤ) : ℝ) / (p : ℝ) ^ 2 := by
  rw [X2Y4_pair_roots_mod_prime_card hp, natCast_intCast_zmod4 p]
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  by_cases h43 : p % 4 = 3
  · rw [if_pos h43]
    have hc : ZMod.χ₄ ((p : ℕ) : ZMod 4) = -1 := ZMod.χ₄_nat_three_mod_four h43
    rw [hc]
    push_cast
    field_simp
    ring
  · rw [if_neg h43]
    by_cases h2 : p = 2
    · subst h2
      rw [if_pos rfl]
      have hc : ZMod.χ₄ ((2 : ℕ) : ZMod 4) = 0 := by decide
      rw [hc]
      norm_num
    · rw [if_neg h2]
      have hp4 : p % 4 = 1 := by
        have hlt : p % 4 < 4 := Nat.mod_lt p (by norm_num)
        have hmod2 : (p % 4) % 2 = 1 := by
          rw [Nat.mod_mod_of_dvd p (by norm_num : 2 ∣ 4)]
          exact (Nat.Prime.eq_two_or_odd hp).resolve_left h2
        interval_cases p % 4 <;> omega
      have hc : ZMod.χ₄ ((p : ℕ) : ZMod 4) = 1 := ZMod.χ₄_nat_one_mod_four hp4
      rw [hc]
      have hcast : ((2 * p - 1 : ℕ) : ℝ) = 2 * (p : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ 2 * p)]
        push_cast
        ring
      rw [hcast]
      push_cast
      field_simp
      ring

theorem X2Y4_gdens_prime_sum :
    ∃ c : ℝ, ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 2 ≤ y →
      |(∑ p ∈ (⌊y⌋₊).primesLE,
          (({x : ZMod p × ZMod p | x.1 ^ 2 + x.2 ^ 4 = 0}.ncard : ℕ) : ℝ) / (p : ℝ) ^ 2)
        - (Real.log (Real.log y) + c)| ≤ C / (Real.log y) ^ A := by
  obtain ⟨c, hc⟩ := X2Y4_density_prime_sum_powLog
  refine ⟨c, fun A hA => ?_⟩
  obtain ⟨C, hCpos, hC⟩ := hc A hA
  refine ⟨C, hCpos, fun y hy => ?_⟩
  have hsum : (∑ p ∈ (⌊y⌋₊).primesLE,
        (({x : ZMod p × ZMod p | x.1 ^ 2 + x.2 ^ 4 = 0}.ncard : ℕ) : ℝ) / (p : ℝ) ^ 2)
      = (∑ p ∈ (⌊y⌋₊).primesLE,
        ((1 + ((ZMod.χ₄ ((p : ℤ) : ZMod 4) : ℤ) : ℝ)) / (p : ℝ)
          - ((ZMod.χ₄ ((p : ℤ) : ZMod 4) : ℤ) : ℝ) / (p : ℝ) ^ 2)) := by
    apply Finset.sum_congr rfl
    intro p hp'
    exact dens_summand_eq p (Nat.prime_of_mem_primesLE hp')
  rw [hsum]
  exact hC y hy

end Commons.NumberTheory.FriedlanderIwaniec
