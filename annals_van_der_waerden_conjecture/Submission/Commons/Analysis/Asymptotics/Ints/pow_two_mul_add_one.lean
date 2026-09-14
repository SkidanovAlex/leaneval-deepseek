import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Asymptotics.Defs

open Filter Asymptotics
set_option autoImplicit false

namespace Commons.Analysis.Asymptotics.Ints

theorem pow_two_mul_add_one (n : ℕ) :
    (fun H : ℕ => (((2 * H + 1) : ℕ) ^ n : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ n : ℝ)) := by
  refine IsBigO.of_bound ((3 : ℝ) ^ n) ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with H hH
  have hHr : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
  have hf0 : (0 : ℝ) ≤ ((2 * H + 1 : ℕ) : ℝ) := by positivity
  have hf0n : (0 : ℝ) ≤ (((2 * H + 1 : ℕ) : ℝ) ^ n) := pow_nonneg hf0 n
  have hg0 : (0 : ℝ) ≤ (H : ℝ) := by exact_mod_cast (Nat.zero_le H)
  have hg0n : (0 : ℝ) ≤ ((H : ℝ) ^ n) := pow_nonneg hg0 n
  rw [Real.norm_of_nonneg hf0n, Real.norm_of_nonneg hg0n]
  have hle : ((2 * H + 1 : ℕ) : ℝ) ≤ (3 : ℝ) * (H : ℝ) := by
    norm_num [Nat.cast_add, Nat.cast_mul]
    nlinarith
  calc
    ((2 * H + 1 : ℕ) : ℝ) ^ n ≤ ((3 : ℝ) * (H : ℝ)) ^ n := pow_le_pow_left₀ hf0 hle n
    _ = (3 : ℝ) ^ n * (H : ℝ) ^ n := by rw [mul_pow]

end Commons.Analysis.Asymptotics.Ints