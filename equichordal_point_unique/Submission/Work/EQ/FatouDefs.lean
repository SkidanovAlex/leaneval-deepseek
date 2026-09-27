import Mathlib
import Submission.Work.EQ.DefsCore

/-! Shared definitions for the Fatou / F. and M. Riesz development
(`Submission/Work/EQ/fatou_riesz.lean`).  Namespace `Work.EQ`. -/

namespace Work.EQ

open MeasureTheory

/-- The angle form of the Poisson kernel: `pk r ψ = (1 - r²)/(1 - 2 r cos ψ + r²)`. -/
noncomputable def pk (r ψ : ℝ) : ℝ := (1 - r ^ 2) / (1 - 2 * r * Real.cos ψ + r ^ 2)

/-- The (negated) derivative in `ψ` of the angle Poisson kernel:
`pkS r s = -(d/ds) pk r s = 2 r (1 - r²) sin s / (1 - 2 r cos s + r²)²`. -/
noncomputable def pkS (r s : ℝ) : ℝ :=
  2 * r * (1 - r ^ 2) * Real.sin s / (1 - 2 * r * Real.cos s + r ^ 2) ^ 2

/-- The disc value `A_ρ(θ) = g (ρ e^{iθ})`. -/
noncomputable def discVal (g : ℂ → ℂ) (ρ θ : ℝ) : ℂ := g (ρ * Complex.exp ((θ : ℂ) * Complex.I))

end Work.EQ
