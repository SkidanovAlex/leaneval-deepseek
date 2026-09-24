import Mathlib
import Submission.Work.GM.Affine.FarMass_defs
import Submission.Work.GM.Affine.region_II_vocab
import Submission.Work.GM.Affine.psi1hat_decay

/-!
# Splitting the region-II far mass at a *bounded* τ-threshold

The proof of `Work.GM.Affine.ghatFar_L2_le_far_mass` splits the far lattice sum
`Wfar K M₃ y = M₃ Σ_{|ℓ-y| > 2/M₃} ψ̂₁(M₃(ℓ-y))` at a *constant* threshold `B₀ ≥ 2`:

* the **window** part `|τ| ≤ B₀` is the "near" part, handled by the resonance count
  `card_mul_pairs_le` (the pair count is bounded because the τ-window is bounded);
* the **tail** part `|τ| > B₀` has exponentially small weights and is handled by the
  coherence lemma `far_lattice_coherence` (or, crudely, by the decay `psi1hat_decay`).

This file only records the definitions and the elementary comparisons (the tail mass is
dominated by the far mass, the weights split, etc.).
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

/-- The **tail** part of the far resonance weight: `M₃ Σ_{|ℓ-y| > B₀/M₃} ψ̂₁(M₃(ℓ-y))`. -/
def WfarBig (K B₀ M₃ y : ℝ) : ℂ :=
  (M₃ : ℂ) * ∑' ℓ : ℤ,
    if |(ℓ : ℝ) - y| > B₀ / M₃ then psi1hat K (M₃ * ((ℓ : ℝ) - y)) else 0

/-- The **tail far mass**: the `‖ψ̂₁‖²`-weighted `L²` mass of `H_ℓ` over `|τ| > B₀`. -/
def FarMassBig (K : ℝ) (f : ℝ → ℝ) (B₀ M₂ M₃ : ℝ) : ℝ :=
  ∑' ℓ : ℤ, ∫ τ in (Set.Ioi B₀ ∪ Set.Iio (-B₀)),
    ‖Hfun f M₂ M₃ ℓ τ‖ ^ 2 * ‖psi1hat K τ‖ ^ 2

end

end Work.GM.Affine
