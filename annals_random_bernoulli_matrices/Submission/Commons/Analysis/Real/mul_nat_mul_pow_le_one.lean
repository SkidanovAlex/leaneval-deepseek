import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecificLimits.Normed

open Filter

namespace Commons.Analysis.Real

theorem mul_nat_mul_pow_le_one {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {c : ℝ} (hc : 0 ≤ c) :
    ∃ N : ℕ, ∀ n ≥ N, c * (n : ℝ) * s ^ n ≤ 1 := by
  have _ := hc
  have hs_abs : |s| < 1 := by rw [abs_of_pos hs0]; exact hs1
  have htend : Tendsto (fun n : ℕ => (n : ℝ) * s ^ n) atTop (nhds 0) := by
    simpa using tendsto_pow_const_mul_const_pow_of_abs_lt_one 1 hs_abs
  have htend' : Tendsto (fun n : ℕ => c * ((n : ℝ) * s ^ n)) atTop (nhds 0) := by
    simpa using htend.const_mul c
  have hev : ∀ᶠ n : ℕ in atTop, c * ((n : ℝ) * s ^ n) < 1 :=
    (tendsto_order.1 htend').2 1 zero_lt_one
  rw [eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  refine ⟨N, fun n hn => ?_⟩
  have hlt : c * ((n : ℝ) * s ^ n) < 1 := hN n hn
  calc c * (n : ℝ) * s ^ n = c * ((n : ℝ) * s ^ n) := by ring
    _ ≤ 1 := le_of_lt hlt

end Commons.Analysis.Real