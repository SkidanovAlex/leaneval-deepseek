import Mathlib.Analysis.Asymptotics.Defs

open Filter Asymptotics
set_option autoImplicit false

namespace Commons.Analysis.Asymptotics

/-- If `f H ≤ g H` eventually (for natural-valued functions), then as real-valued
functions `f =O[atTop] g`. Both values are nonnegative, so the bound constant is `1`. -/
theorem isBigO_of_eventually_le (f g : ℕ → ℕ)
    (h : ∀ᶠ H : ℕ in atTop, f H ≤ g H) :
    (fun H : ℕ => (f H : ℝ)) =O[atTop] (fun H : ℕ => (g H : ℝ)) := by
  refine IsBigO.of_bound (1 : ℝ) ?_
  filter_upwards [h] with H hH
  have hf0 : (0 : ℝ) ≤ (f H : ℝ) := by exact_mod_cast Nat.zero_le (f H)
  have hg0 : (0 : ℝ) ≤ (g H : ℝ) := by exact_mod_cast Nat.zero_le (g H)
  rw [Real.norm_of_nonneg hf0, Real.norm_of_nonneg hg0]
  norm_num
  exact_mod_cast hH

end Commons.Analysis.Asymptotics