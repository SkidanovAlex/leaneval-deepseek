import Mathlib
import Submission.Work.NN.Core.CnPert
import Submission.Work.CR.Flat.Polydisc

namespace Work.NN.Core.Lev2

open scoped ENNReal ContDiff Topology
open MeasureTheory Set

/-- The assignment's *power Caccioppoli hypothesis with source* `Λ`: for every level `k ≥ 1` and
every smooth non-negative compactly supported test function `φ` with `tsupport φ ⊆ polydisc 0 ρ`,

`∫ k² φ² (‖u‖²)^{k-1} Σ_j (‖∂_j u‖² + ‖∂̄_j u‖²) ≤ A₀ (∫ ‖Dφ‖² (‖u‖²)^k + k² ∫ φ² (‖u‖²)^{k-1} Λ²)`.

This is exactly the hypothesis assumed by `Work.NN.Core.Lev2.supMoserMeanValue` (and produced by
`Work.NN.Core.Lev.powCaccioppoliSource`). -/
def HasPowCaccSource {n : ℕ} (ρ : Fin n → ℝ) (A₀ Λ : ℝ) (u : Work.NN.Core.Cn n → ℂ) : Prop :=
  ∀ (k : ℕ), 1 ≤ k → ∀ (φ : Work.NN.Core.Cn n → ℝ),
    ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
    tsupport φ ⊆ Work.CR.Flat.polydisc 0 ρ → (∀ z, 0 ≤ φ z) →
    ∫ z in Work.CR.Flat.polydisc 0 ρ,
        (k : ℝ)^2 * (φ z)^2 * (‖u z‖^2)^(k-1) *
          (∑ j, (‖Work.CR.Flat.dCoord j u z‖^2 + ‖Work.CR.Flat.dbarCoord j u z‖^2))
      ≤ A₀ * ((∫ z in Work.CR.Flat.polydisc 0 ρ, ‖fderiv ℝ φ z‖^2 * (‖u z‖^2)^k)
             + (k:ℝ)^2 * ∫ z in Work.CR.Flat.polydisc 0 ρ,
                 (φ z)^2 * (‖u z‖^2)^(k-1) * Λ^2)

end Work.NN.Core.Lev2
