import Mathlib
import Submission.Commons.NumberTheory.FriedlanderIwaniec.tendsto_prod_one_sub_chi4_div_prime
import Submission.Commons.NumberTheory.FriedlanderIwaniec.X2Y4_pair_roots_mod_prime_card

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators
open Finset

namespace Commons.NumberTheory.FriedlanderIwaniec

noncomputable section

/-- For every prime `p`, the local Euler factor of the density
`∏_p (1 − ρ(p)/p²)/(1 − 1/p)` equals `1 − χ₄(p)/p`, where `ρ(p)` counts the
solutions of `x² + y⁴ = 0` in `(ZMod p)²`. -/
private lemma local_factor_eq_chi4 (p : ℕ) (hp : p.Prime) :
    (1 - (({x : ZMod p × ZMod p | x.1 ^ 2 + x.2 ^ 4 = 0}.ncard : ℕ) : ℝ) / (p : ℝ) ^ 2)
        / (1 - 1 / (p : ℝ))
      = 1 - ((ZMod.χ₄ ((p : ℕ) : ZMod 4) : ℤ) : ℝ) / (p : ℝ) := by
  have hp2n : 2 ≤ p := hp.two_le
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
    linarith
  by_cases h43 : p % 4 = 3
  · rw [X2Y4_pair_roots_mod_prime_card hp, if_pos h43]
    have hchi : ((ZMod.χ₄ ((p : ℕ) : ZMod 4) : ℤ) : ℝ) = -1 := by
      rw [ZMod.χ₄_nat_three_mod_four h43]; norm_num
    rw [hchi]
    push_cast
    field_simp
    ring
  · by_cases h2 : p = 2
    · subst h2
      rw [X2Y4_pair_roots_mod_prime_card hp, if_neg h43, if_pos rfl]
      have hchi : ((ZMod.χ₄ ((2 : ℕ) : ZMod 4) : ℤ) : ℝ) = 0 := by
        rw [ZMod.χ₄_nat_eq_if_mod_four]
        norm_num
      rw [hchi]
      norm_num
    · rw [X2Y4_pair_roots_mod_prime_card hp, if_neg h43, if_neg h2]
      have hp4 : p % 4 = 1 := by
        have hlt : p % 4 < 4 := Nat.mod_lt p (by norm_num)
        have hmod2 : (p % 4) % 2 = 1 := by
          rw [Nat.mod_mod_of_dvd p (by norm_num : 2 ∣ 4)]
          exact (Nat.Prime.eq_two_or_odd hp).resolve_left h2
        interval_cases p % 4 <;> omega
      have hchi : ((ZMod.χ₄ ((p : ℕ) : ZMod 4) : ℤ) : ℝ) = 1 := by
        rw [ZMod.χ₄_nat_one_mod_four hp4]; norm_num
      rw [hchi]
      have hcast : ((2 * p - 1 : ℕ) : ℝ) = 2 * (p : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ 2 * p)]
        push_cast
        ring
      rw [hcast]
      field_simp
      ring

theorem tendsto_prod_one_sub_X2Y4_density :
    Filter.Tendsto (fun N : ℕ => ∏ p ∈ Nat.primesBelow N,
        (1 - (({x : ZMod p × ZMod p | x.1 ^ 2 + x.2 ^ 4 = 0}.ncard : ℕ) : ℝ) / (p : ℝ) ^ 2)
          / (1 - 1 / (p : ℝ)))
      Filter.atTop (nhds (4 / Real.pi)) := by
  refine tendsto_prod_one_sub_chi4_div_prime.congr (fun N => ?_)
  exact Finset.prod_congr rfl fun p hp =>
    (local_factor_eq_chi4 p (Nat.mem_primesBelow.mp hp).2).symm

end
end Commons.NumberTheory.FriedlanderIwaniec
