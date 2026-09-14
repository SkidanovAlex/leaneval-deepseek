import Mathlib.Analysis.Asymptotics.Defs

open Filter Asymptotics
set_option autoImplicit false

namespace Commons.Analysis.Asymptotics

theorem isBigO_of_natCast_le_mul_pow (n C : ℕ) (f : ℕ → ℕ)
    (hf : ∀ᶠ H : ℕ in atTop, f H ≤ C * H ^ n) :
    (fun H : ℕ => (f H : ℝ)) =O[atTop] (fun H : ℕ => ((H : ℕ) ^ n : ℝ)) := by
  refine IsBigO.of_bound (C : ℝ) ?_
  filter_upwards [hf] with H hH
  calc
    ‖(f H : ℝ)‖ = (f H : ℝ) := by
      rw [Real.norm_of_nonneg]
      exact_mod_cast (Nat.zero_le (f H))
    _ ≤ (↑(C * H ^ n) : ℝ) := by
      exact_mod_cast hH
    _ = (C : ℝ) * (H : ℝ) ^ n := by
      rw [Nat.cast_mul, Nat.cast_pow]
    _ = (C : ℝ) * ‖(H : ℝ) ^ n‖ := by
      rw [Real.norm_of_nonneg]
      positivity

end Commons.Analysis.Asymptotics