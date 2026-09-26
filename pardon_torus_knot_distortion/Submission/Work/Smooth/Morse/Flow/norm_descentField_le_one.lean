import Mathlib
import Submission.Work.Smooth.Morse.Defs

namespace Work.Smooth.Morse.Flow

/-- The descent field `descentField ψ g p = -((1 + (∂₁G)² + (∂₂G)²)⁻¹) • (∂₁G, ∂₂G)` is bounded by
`1` in the product (sup) norm on the parameter plane.  Indeed its two coordinates are
`-c * ∂₁G` and `-c * ∂₂G` with `c = (1 + (∂₁G)² + (∂₂G)²)⁻¹ > 0`, so

`‖descentField ψ g p‖ = c * max(|∂₁G|, |∂₂G|)`,

and each of `c * |∂₁G|`, `c * |∂₂G|` is at most `1` because `|∂ᵢG| ≤ 1 + (∂₁G)² + (∂₂G)²`. -/
theorem norm_descentField_le_one (ψ : Submission.Diffeo) (g : LeanEval.KnotTheory.PardonDistortion.R3 → ℝ) :
    ∀ q : ℝ × ℝ, ‖Work.Smooth.Morse.descentField ψ g q‖ ≤ 1 := by
  intro q
  have hpair : Work.Smooth.Morse.descentField ψ g q =
      ((-(1 + (Work.Smooth.Morse.partialD₁ ψ g q)^2 + (Work.Smooth.Morse.partialD₂ ψ g q)^2)⁻¹) *
          Work.Smooth.Morse.partialD₁ ψ g q,
        (-(1 + (Work.Smooth.Morse.partialD₁ ψ g q)^2 + (Work.Smooth.Morse.partialD₂ ψ g q)^2)⁻¹) *
          Work.Smooth.Morse.partialD₂ ψ g q) := by
    rw [Work.Smooth.Morse.descentField]; rfl
  have hpos : (0 : ℝ) < 1 + (Work.Smooth.Morse.partialD₁ ψ g q)^2 + (Work.Smooth.Morse.partialD₂ ψ g q)^2 :=
    by positivity
  rw [hpair, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_neg, abs_inv,
    abs_of_pos hpos]
  apply max_le
  · rw [inv_mul_le_iff₀ hpos]
    nlinarith [sq_nonneg (|Work.Smooth.Morse.partialD₁ ψ g q| - 1 / 2),
      sq_nonneg (Work.Smooth.Morse.partialD₂ ψ g q),
      abs_nonneg (Work.Smooth.Morse.partialD₁ ψ g q),
      sq_abs (Work.Smooth.Morse.partialD₁ ψ g q)]
  · rw [inv_mul_le_iff₀ hpos]
    nlinarith [sq_nonneg (|Work.Smooth.Morse.partialD₂ ψ g q| - 1 / 2),
      sq_nonneg (Work.Smooth.Morse.partialD₁ ψ g q),
      abs_nonneg (Work.Smooth.Morse.partialD₂ ψ g q),
      sq_abs (Work.Smooth.Morse.partialD₂ ψ g q)]

end Work.Smooth.Morse.Flow
