import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.SD

theorem rho_window_arith (ρ a b : ℝ) (hρ : 0 < ρ) (ha : 0 < a) (hb : 5 * b ≤ 7 * a) :
    1 ≤ Nat.ceil (1 / ρ) ∧ b ≤ a * (1 + ρ) ^ (Nat.ceil (1 / ρ)) := by
  have hpos : 0 < 1 / ρ := by positivity
  constructor
  · exact Nat.one_le_ceil_iff.mpr hpos
  · -- Let n = ⌈1/ρ⌉. Since n ≥ 1/ρ (as a real), ρ * n ≥ 1, so by Bernoulli
    -- (1+ρ)^n ≥ 1 + n*ρ ≥ 2 > 7/5. Then b ≤ 7a/5 ≤ 2a ≤ a*(1+ρ)^n.
    have hn1 : (1 : ℝ) ≤ ρ * (Nat.ceil (1 / ρ) : ℝ) := by
      have h := Nat.le_ceil (1 / ρ)
      have hmul : ρ * (1 / ρ) ≤ ρ * (Nat.ceil (1 / ρ) : ℝ) :=
        mul_le_mul_of_nonneg_left h (le_of_lt hρ)
      rw [mul_one_div, div_self (ne_of_gt hρ)] at hmul
      exact hmul
    have hn1' : (1 : ℝ) ≤ (Nat.ceil (1 / ρ) : ℝ) * ρ := by
      rw [mul_comm]; exact hn1
    have hbern : 1 + (Nat.ceil (1 / ρ) : ℝ) * ρ ≤ (1 + ρ) ^ (Nat.ceil (1 / ρ)) :=
      one_add_mul_le_pow (by linarith) _
    have hge2 : (2 : ℝ) ≤ (1 + ρ) ^ (Nat.ceil (1 / ρ)) := by linarith
    have hb' : b ≤ 7 * a / 5 := by linarith
    have h7a : 7 * a / 5 ≤ a * 2 := by nlinarith [ha]
    have h2a : a * 2 ≤ a * (1 + ρ) ^ (Nat.ceil (1 / ρ)) :=
      mul_le_mul_of_nonneg_left hge2 (le_of_lt ha)
    linarith

end Work.BMF.SD
