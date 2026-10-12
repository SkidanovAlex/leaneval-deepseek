import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.FRKDefs
import Submission.Work.BoseBoxFock.LatVec
import Submission.Work.BoseBoxFock.kinRow_lattice_tauPhi
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.windowAlias_of_pieces` — the design's W3 assembled from its two inputs

`LEAD_DESIGN_formrowkin_v2.md` §1 states the windowed alias bound (W3, `windowAlias_le`): for a
smooth nonnegative symbol `σ` with quadratic growth and a controlled six-derivative mass, the
`ℤ³`-lattice sum of `σ` against the bridge state `winState ℓ ψ = χ_Λ(ψ − mean)` is dominated by the
continuum integral of `σ` plus the reserve `K‖D⁶σ‖₁ℓ⁻³·gapBare`.

Its mathematical content is split between two independent inputs:

* **W1′** (`lattice_symbol_eq_alias`, in flight) — the *identity*
  `lattice = continuum + Σ_{m≠0} image_m`, i.e. polarised Parseval on the cell;
* **the image bound** (`Work.BoseBoxFock.winState_image_sum_le`, in flight) — the quantitative
  bound `‖Σ_{m≠0} image_m‖ ≤ C‖D⁶σ‖₁ℓ⁻³·gapBare`, which is where the flatness of `χ_Λ` at the
  sphere and the off-support decay `‖symOp σ g y‖ ≲ ‖D⁶σ‖₁∫‖g‖/‖y−·‖⁶` (W2) are consumed.

This module performs the (short) bookkeeping between them, so that `windowAlias_le` is available as
soon as those two land.

⚠ **Parenthesisation**: the continuum integral on the right-hand side is written with explicit
parentheses, `((2π)³)⁻¹ * (∫ p, …) + K * …`.  Without them Lean parses the reserve *inside* the
integrand over `ℝ³`, which makes the statement unsatisfiable — see
`FINDING_parse_bug_integral_plus.md`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

set_option maxHeartbeats 4000000

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **(W3) from W1′ and the image bound.**  Given the lattice/continuum identity for smooth
ball-supported complex states and the quantitative bound on its nonzero-image sum for the bridge
state, the windowed alias bound holds. -/
theorem windowAlias_of_pieces
    (hW1 : ∀ {ℓ : ℝ} (hℓ : 0 < ℓ) {σ : E3 → ℝ}
      (hσ : ContDiff ℝ (⊤ : ℕ∞) σ) (hσg : ∃ A : ℝ, ∀ p, |σ p| ≤ A * (1 + ‖p‖) ^ 2)
      (hσ6 : MeasureTheory.Integrable (fun p : E3 => ‖iteratedFDeriv ℝ 6 σ p‖))
      {g : E3 → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
      (hgs : tsupport g ⊆ Metric.closedBall 0 (ℓ / 2)),
      (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * σ (kmomInt ℓ n) *
          ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2)
        = ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3, σ p * ‖Submission.BoseGases.kinFT g p‖ ^ 2)
          + ∑' m : Fin 3 → ℤ, (if m = 0 then 0 else
              (∫ x : E3, (starRingEnd ℂ) (g x) * symOp σ g (x + ℓ • latVec m)).re))
    (hImg : ∃ C : ℝ, 0 ≤ C ∧ ∀ {ℓ : ℝ}, 0 < ℓ → ∀ (σ : E3 → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) σ →
      (∃ A : ℝ, ∀ p, |σ p| ≤ A * (1 + ‖p‖) ^ 2) →
      MeasureTheory.Integrable (fun p : E3 => ‖iteratedFDeriv ℝ 6 σ p‖) →
      ∀ (ψ : E3 → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
      ‖∑' m : Fin 3 → ℤ, (if m = 0 then 0 else
          (∫ x : E3, (starRingEnd ℂ) (winState ℓ ψ x) *
            symOp σ (winState ℓ ψ) (x + ℓ • latVec m)).re)‖
        ≤ C * (∫ p : E3, ‖iteratedFDeriv ℝ 6 σ p‖) * (ℓ ^ 3)⁻¹ * Work.BoseKinLoc.gapBare ℓ 0 ψ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {ℓ : ℝ}, 0 < ℓ → ∀ (σ : E3 → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) σ → (∀ p, 0 ≤ σ p) →
      (∃ A : ℝ, ∀ p, |σ p| ≤ A * (1 + ‖p‖) ^ 2) →
      MeasureTheory.Integrable (fun p : E3 => ‖iteratedFDeriv ℝ 6 σ p‖) →
      ∀ (ψ : E3 → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
      (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * σ (kmomInt ℓ n) *
          ‖Submission.BoseGases.kinFT (winState ℓ ψ) (kmomInt ℓ n)‖ ^ 2)
        ≤ ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3,
            σ p * ‖Submission.BoseGases.kinFT (winState ℓ ψ) p‖ ^ 2)
          + K * (∫ p : E3, ‖iteratedFDeriv ℝ 6 σ p‖) * (ℓ ^ 3)⁻¹
              * Work.BoseKinLoc.gapBare ℓ 0 ψ := by
  obtain ⟨C, hC0, hImg'⟩ := hImg
  refine ⟨C, hC0, ?_⟩
  intro ℓ hℓ σ hσ _hσnn hσg hσ6 ψ hψ
  -- the identity at the bridge state
  have hident := hW1 hℓ hσ hσg hσ6 (winState_contDiff hℓ hψ)
    (winState_tsupport_subset hℓ ψ)
  -- the image sum is bounded by the reserve
  have himg := hImg' hℓ σ hσ hσg hσ6 ψ hψ
  have himg' : |∑' m : Fin 3 → ℤ, (if m = 0 then 0 else
        (∫ x : E3, (starRingEnd ℂ) (winState ℓ ψ x) *
          symOp σ (winState ℓ ψ) (x + ℓ • latVec m)).re)|
      ≤ C * (∫ p : E3, ‖iteratedFDeriv ℝ 6 σ p‖) * (ℓ ^ 3)⁻¹
          * Work.BoseKinLoc.gapBare ℓ 0 ψ := by
    simpa only [Real.norm_eq_abs] using himg
  calc (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * σ (kmomInt ℓ n) *
        ‖Submission.BoseGases.kinFT (winState ℓ ψ) (kmomInt ℓ n)‖ ^ 2)
      = ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3,
            σ p * ‖Submission.BoseGases.kinFT (winState ℓ ψ) p‖ ^ 2)
          + ∑' m : Fin 3 → ℤ, (if m = 0 then 0 else
              (∫ x : E3, (starRingEnd ℂ) (winState ℓ ψ x) *
                symOp σ (winState ℓ ψ) (x + ℓ • latVec m)).re) := hident
    _ ≤ ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3,
            σ p * ‖Submission.BoseGases.kinFT (winState ℓ ψ) p‖ ^ 2)
          + C * (∫ p : E3, ‖iteratedFDeriv ℝ 6 σ p‖) * (ℓ ^ 3)⁻¹
              * Work.BoseKinLoc.gapBare ℓ 0 ψ := by
        exact add_le_add (le_refl _) (le_trans (le_abs_self _) himg')

end Work.BoseBoxFock
