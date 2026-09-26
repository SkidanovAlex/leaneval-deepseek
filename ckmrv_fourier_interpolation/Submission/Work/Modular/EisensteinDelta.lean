import Mathlib

/-!
# The weight-twelve Eisenstein series `E₁₂` and the discriminant `Δ`

These are the two ingredients of the weight-twelve level-one modular forms, used for the
"magic of dimension 24" (the theta series of an even unimodular rank-24 lattice with no vectors
of squared length `2` is `E₁₂ - (65520/691) Δ`).
-/

open UpperHalfPlane ModularForm
open scoped MatrixGroups ModularForm

namespace Work.Modular

/-- The normalized weight-twelve Eisenstein series,
`E₁₂(τ) = 1 + (65520/691) ∑_{n ≥ 1} σ₁₁(n) qⁿ`. -/
noncomputable abbrev E12 : ℍ → ℂ := ⇑(ModularForm.E (by norm_num : 3 ≤ 12))

/-- The modular discriminant `Δ = (E₄³ - E₆²)/1728 = q ∏ (1 - qⁿ)^24`. -/
noncomputable abbrev Delta : ℍ → ℂ := ModularForm.discriminant

end Work.Modular
