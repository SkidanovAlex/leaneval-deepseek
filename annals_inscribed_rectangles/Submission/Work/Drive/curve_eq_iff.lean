import Mathlib
import Submission.Work.Drive.UmlaufSetup

namespace Work.Drive

open scoped Manifold ContDiff
open Manifold

/-- Two parameters give the same point of the curve `t ↦ γ (Circle.exp t)` of an embedded curve
exactly when they differ by a period.

`γ` is injective (`hγ.isEmbedding.injective`), and `Circle.exp s = Circle.exp t` iff
`Complex.exp (s * I) = Complex.exp (t * I)` (`Circle.coe_exp`) iff `∃ n : ℤ,
s * I = t * I + n * (2 * π * I)` (`Complex.exp_eq_exp_iff_exists_int`), i.e. iff
`∃ k : ℤ, s = t + 2 * π * k`.  For the converse use periodicity of `Circle.exp`
(`Circle.exp_add_two_pi`): if `s = t + 2πk` then `Circle.exp s = Circle.exp t`. -/
theorem curve_eq_iff (γ : Circle → ℝ × ℝ)
    (hγ : IsSmoothEmbedding (𝓡 1) (𝓘(ℝ, ℝ × ℝ)) ∞ γ) (s t : ℝ) :
    Work.Drive.curve γ s = Work.Drive.curve γ t ↔ ∃ k : ℤ, s = t + 2 * Real.pi * k := by
  simp only [curve]
  rw [hγ.isEmbedding.injective.eq_iff, Circle.exp_eq_exp]
  constructor
  · rintro ⟨m, hm⟩; exact ⟨m, by rw [hm]; ring⟩
  · rintro ⟨m, hm⟩; exact ⟨m, by rw [hm]; ring⟩

end Work.Drive
