import Mathlib
import Submission.Work.GM.Affine.fine_setup
import Submission.Work.GM.Affine.smoothed_properties

/-!
# GM §9: vocabulary for region II (the honest chain)

The middle region `T^η M₁/M₃ < |ξ| ≤ T^6` of GM's Lemma 9.2 is estimated by

* counting the resonant pairs `(m₁, ℓ)`, `|m₁ℓ - ξ| ⪅ M₁/M₃`, and Cauchy–Schwarz;
* the change of variables `ξ = m₁ℓ + (m₁/M₃)τ`;
* Poisson summation in `ℓ`, which converts the resulting frequency sum into a *spatial*
  localisation, producing the honest affine sum `Gfun` of `f̃ = smoothed psiSmooth T f`.

`Hfun f M₂ M₃ ℓ τ = Σ_{m₂ ∈ R2 M₂} m₂ · f̂(m₂(ℓ + τ/M₃))` is the inner `m₂`-sum.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

/-- The inner `m₂`-sum `H_ℓ(τ) = Σ_{m₂ ∈ R2 M₂} m₂ · Fhat f (m₂ (ℓ + τ/M₃))`. -/
def Hfun (f : ℝ → ℝ) (M₂ M₃ : ℝ) (ℓ : ℤ) (τ : ℝ) : ℂ :=
  ∑ m₂ ∈ R2 M₂, ((m₂ : ℝ) : ℂ) * Fhat f ((m₂ : ℝ) * ((ℓ : ℝ) + τ / M₃))

/-- The honest affine sum produced by Poisson summation in `ℓ`:

`Gfun C₀ T M₂ f u = Σ_{m₂,m₂' ∈ R2 M₂} Σ_{|j| ≤ ⌊2C₀M₂⌋} f̃((m₂ u + j)/m₂')`.
-/
def Gfun (C₀ T M₂ : ℝ) (f : ℝ → ℝ) (u : ℝ) : ℝ :=
  ∑ m₂ ∈ R2 M₂, ∑ m₂' ∈ R2 M₂,
    ∑ j ∈ Finset.Icc (-⌊2 * C₀ * M₂⌋) ⌊2 * C₀ * M₂⌋,
      smoothed psiSmooth T f (((m₂ : ℝ) * u + (j : ℝ)) / (m₂' : ℝ))

end

end Work.GM.Affine
