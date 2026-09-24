import Mathlib
import Submission.Work.GM.Affine.region_II_vocab
import Submission.Work.GM.Affine.psi1hat_decay

/-!
# GM §9 region II, the far part: the "far mass"

This file defines the quantity `FarMass K f M₂ M₃` appearing in the reduction of the region-II
*far* part `Work.GM.Affine.region_II_far` to a purely "structural" estimate:

`FarMass K f M₂ M₃ = Σ_ℓ ∫_{|τ| > 2} ‖H_ℓ(τ)‖² ‖ψ̂₁(τ)‖² dτ`,

with `H_ℓ(τ) = Σ_{m₂ ∈ R2 M₂} m₂ Fhat f (m₂ (ℓ + τ/M₃))` (so `H_ℓ(τ) = Bsum f M₂ (ℓ + τ/M₃)`).

The point of the region-II far decomposition is that the far part of `ghat` is bounded by
`(M₁ + M₃) · FarMass` (the reduction, using the resonance count `card_mul_pairs_le`,
Cauchy–Schwarz over the far pairs and the change of variables), while the *far mass* itself is
bounded by a constant times the resonant window mass `WinMass f M₂ M₃`: this is the analytic
content, because the weight `‖ψ̂₁(M₃θ)‖²` is concentrated on the scale `1/M₃` around the lattice
points, exactly like the window `1_{|τ|≤2}` defining `WinMass`, whereas the *coherent* far weight
`‖W_far‖² = ‖M₃ Σ_{far ℓ} ψ̂₁(M₃(ℓ - y))‖²` is **not** so controlled (it grows like `M₃`
relative to `WinMass`, so Cauchy–Schwarz over `m₁` alone is insufficient).
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

/-- The `m₃`-profile `Wsum` restricted to the **far** integers:
`M₃ Σ_{|ℓ-y|>2/M₃} ψ̂₁(M₃(ℓ-y))`. -/
def Wfar (K M₃ y : ℝ) : ℂ :=
  (M₃ : ℂ) * ∑' ℓ : ℤ,
    if |(ℓ : ℝ) - y| > 2 / M₃ then psi1hat K (M₃ * ((ℓ : ℝ) - y)) else 0

/-- The **far mass**: the `‖ψ̂₁‖²`-weighted `L²` mass of `H_ℓ` over the far range `|τ| > 2`. -/
def FarMass (K : ℝ) (f : ℝ → ℝ) (M₂ M₃ : ℝ) : ℝ :=
  ∑' ℓ : ℤ, ∫ τ in (Set.Ioi 2 ∪ Set.Iio (-2)),
    ‖Hfun f M₂ M₃ ℓ τ‖ ^ 2 * ‖psi1hat K τ‖ ^ 2

end

end Work.GM.Affine
