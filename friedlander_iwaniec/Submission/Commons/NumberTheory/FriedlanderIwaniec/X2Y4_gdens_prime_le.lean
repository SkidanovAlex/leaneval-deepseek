import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Submission.Commons.NumberTheory.FriedlanderIwaniec.X2Y4_pair_roots_mod_prime_card

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.NumberTheory.FriedlanderIwaniec

theorem X2Y4_gdens_prime_le (p : ℕ) (hp : p.Prime) :
    let g : ℕ → ℝ := fun d =>
      (({x : ZMod d × ZMod d | x.1 ^ 2 + x.2 ^ 4 = 0}.ncard : ℕ) : ℝ) / (d : ℝ) ^ 2
    g p ≤ 3 / (p : ℝ) ∧ g p ≤ (2 * (p : ℝ) - 1) / (p : ℝ) ^ 2 + 1 / (p : ℝ) ^ 2 := by
  dsimp only
  rw [X2Y4_pair_roots_mod_prime_card hp]
  set N : ℕ := (if p % 4 = 3 then 1 else if p = 2 then 2 else 2 * p - 1) with hNdef
  have hp1 : 1 ≤ p := hp.one_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hpne : (p : ℝ) ≠ 0 := ne_of_gt hp0
  have hNle : N ≤ 2 * p := by
    rw [hNdef]
    by_cases h43 : p % 4 = 3
    · rw [if_pos h43]; omega
    · rw [if_neg h43]
      by_cases h2 : p = 2
      · rw [if_pos h2]; omega
      · rw [if_neg h2]; omega
  have hNRle : (N : ℝ) ≤ 2 * (p : ℝ) := by exact_mod_cast hNle
  have hg2 : (N : ℝ) / (p : ℝ) ^ 2 ≤ 2 / (p : ℝ) := by
    rw [div_le_iff₀ (pow_pos hp0 2)]
    rw [show (2 : ℝ) / (p : ℝ) * (p : ℝ) ^ 2 = 2 * (p : ℝ) by field_simp]
    exact hNRle
  constructor
  · calc (N : ℝ) / (p : ℝ) ^ 2 ≤ 2 / (p : ℝ) := hg2
      _ ≤ 3 / (p : ℝ) := by
        rw [div_le_div_iff₀ hp0 hp0]
        nlinarith [hp0]
  · calc (N : ℝ) / (p : ℝ) ^ 2 ≤ 2 / (p : ℝ) := hg2
      _ = (2 * (p : ℝ) - 1) / (p : ℝ) ^ 2 + 1 / (p : ℝ) ^ 2 := by
        field_simp
        ring

end Commons.NumberTheory.FriedlanderIwaniec