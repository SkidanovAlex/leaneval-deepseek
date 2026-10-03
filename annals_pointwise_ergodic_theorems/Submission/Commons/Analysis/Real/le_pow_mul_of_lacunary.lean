import Mathlib.Data.NNReal.Defs

namespace Commons.Analysis.Real

/-- Growth bound for a `Λ`-lacunary sequence of nonnegative reals (`Λ > 1`,
    `x (n+1) ≥ Λ * x n`): `Λ ^ n * x 0 ≤ x n`. -/
theorem le_pow_mul_of_lacunary {Λ : NNReal} {x : ℕ → NNReal}
    (hx : ∀ n, Λ * x n ≤ x (n + 1)) (n : ℕ) : Λ ^ n * x 0 ≤ x n := by
  induction n with
  | zero => simp
  | succ k ih =>
    calc Λ ^ (k + 1) * x 0 = Λ * (Λ ^ k * x 0) := by rw [pow_succ', mul_assoc]
      _ ≤ Λ * x k := mul_le_mul_of_nonneg_left ih (by positivity)
      _ ≤ x (k + 1) := hx k

end Commons.Analysis.Real