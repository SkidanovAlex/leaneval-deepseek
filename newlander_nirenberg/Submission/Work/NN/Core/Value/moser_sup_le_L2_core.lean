/-
# Moser iteration: interior sup bound from the weighted power Caccioppoli inequality

This file now (a) re-exports the helper library (moved verbatim to
`Submission.Work.NN.Core.Value.moserCoreDefs`, so that the cycle-free copy of the Moser boost
`Submission.Work.Value.moserClassicalBoostX` can use `moser_boost` without importing this module),
and (b) contains the requested theorem `Work.NN.Core.Value.moser_sup_le_L2_core`, proved from
`Work.Value.moserWindowedSupBoundX`.
-/
import Submission.Work.NN.Core.Value.moserCoreDefs
import Submission.Work.Value.moserWindowedSupBoundX

noncomputable section

open scoped NNReal ENNReal ContDiff Topology
open Set MeasureTheory Filter

namespace Work.NN.Core.Value

theorem moser_sup_le_L2_core {n : ℕ} (hn : 0 < n) {σ ρ : Fin n → ℝ} (hσ0 : ∀ j, 0 < σ j)
    (hρ0 : ∀ j, 0 < ρ j) (hσρ : ∀ j, σ j < ρ j) {C₀ δ : ℝ} (hC₀ : 0 < C₀) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {u : Work.NN.Core.Cn n → ℂ},
      ContDiffOn ℝ 1 u (Work.CR.Flat.polydisc 0 ρ) →
      (∀ (γ : ℝ), 1 ≤ γ →
        (∃ k : ℕ, 1 ≤ k ∧ |γ - (k : ℝ)| < δ * (k : ℝ)) →
        ∀ (ψ : Work.NN.Core.Cn n → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
          tsupport ψ ⊆ Work.CR.Flat.polydisc 0 ρ → (∀ z, 0 ≤ ψ z) →
          ∫ z in Work.CR.Flat.polydisc 0 ρ, (ψ z)^2 * ‖u z‖ ^ (2*γ-2) *
              (∑ j, (‖Work.CR.Flat.dCoord j u z‖^2 + ‖Work.CR.Flat.dbarCoord j u z‖^2))
            ≤ C₀ * ∫ z in Work.CR.Flat.polydisc 0 ρ, ‖fderiv ℝ ψ z‖^2 * ‖u z‖ ^ (2*γ)) →
      ∀ z ∈ Work.CR.Flat.polydisc 0 σ,
        ENNReal.ofReal ‖u z‖ ≤ ENNReal.ofReal C *
          MeasureTheory.eLpNorm u 2
            (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 ρ)) :=
  Work.Value.moserWindowedSupBoundX hn hσ0 hρ0 hσρ hC₀ hδ

end Work.NN.Core.Value
