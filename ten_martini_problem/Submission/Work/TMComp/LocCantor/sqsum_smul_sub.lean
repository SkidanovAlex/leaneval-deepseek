import Mathlib

namespace Work.TMComp.LocCantor

/-- For a `2 × 2` real matrix `A` and scalars `u₁ u₂`, the sum of the squares of the
entries of `u₁ • A - u₂ • 1` equals
`u₁ ^ 2 * (Σ A i j ^ 2) - 2 * u₁ * u₂ * A.trace + 2 * u₂ ^ 2`. -/
theorem sqsum_smul_sub (A : Matrix (Fin 2) (Fin 2) ℝ) (u₁ u₂ : ℝ) :
    (u₁ • A - u₂ • 1) 0 0 ^ 2 + (u₁ • A - u₂ • 1) 0 1 ^ 2
      + (u₁ • A - u₂ • 1) 1 0 ^ 2 + (u₁ • A - u₂ • 1) 1 1 ^ 2
    = u₁ ^ 2 * (A 0 0 ^ 2 + A 0 1 ^ 2 + A 1 0 ^ 2 + A 1 1 ^ 2) - 2 * u₁ * u₂ * A.trace
      + 2 * u₂ ^ 2 := by
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
    Matrix.trace_fin_two]
  norm_num
  ring

end Work.TMComp.LocCantor
