import Mathlib.Data.NNReal.Defs

namespace Commons.Analysis.Real

/-- A `Λ`-lacunary sequence of nonnegative reals with `Λ > 1` is monotone. -/
theorem monotone_of_lacunary {Λ : NNReal} (hΛ : 1 < Λ) {x : ℕ → NNReal}
    (hx : ∀ n, Λ * x n ≤ x (n + 1)) : Monotone x := by
  refine monotone_nat_of_le_succ (fun n => ?_)
  calc x n ≤ Λ * x n := le_mul_of_one_le_left' (le_of_lt hΛ)
    _ ≤ x (n + 1) := hx n

end Commons.Analysis.Real