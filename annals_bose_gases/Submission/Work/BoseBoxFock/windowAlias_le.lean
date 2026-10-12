import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.lattice_symbol_eq_alias
import Submission.Work.BoseBoxFock.norm_symOp_le_of_dist
import Submission.Work.BoseBoxFock.winState_image_sum_le
import Submission.Work.BoseBoxFock.windowAlias_of_pieces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.windowAlias_le` — the design's W3 leaf

The windowed alias bound of `LEAD_DESIGN_formrowkin_v2.md` §1, stated with the continuum integral
**parenthesised** (the un-parenthesised transcription puts the reserve inside the integrand and has
no instance — `FINDING_parse_bug_integral_plus.md`).

It is `Work.BoseBoxFock.windowAlias_of_pieces` applied to its two inputs:

* **W1′** `Work.BoseBoxFock.lattice_symbol_eq_alias` — the lattice/continuum identity;
* **the image bound** `Work.BoseBoxFock.winState_image_sum_le` (which itself consumes **W2**
  `Work.BoseBoxFock.norm_symOp_le_of_dist`).

⚠ Status of the imports at the time of writing: `winState_image_sum_le` is proved; W1′ and W2 are
the two remaining leaves of this file's cone (their bodies are still being filled in, so this
module compiles but its `#print axioms` currently shows `sorryAx`).  **Once W1′ and W2 are proved,
rebuilding this module makes the leaf axiom-clean with no edit.**
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

set_option maxHeartbeats 4000000

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **(W3)** the windowed alias bound (design `windowAlias_le`). -/
theorem windowAlias_le : ∃ K : ℝ, 0 ≤ K ∧ ∀ {ℓ : ℝ}, 0 < ℓ → ∀ (σ : E3 → ℝ),
    ContDiff ℝ (⊤ : ℕ∞) σ → (∀ p, 0 ≤ σ p) →
    (∃ A : ℝ, ∀ p, |σ p| ≤ A * (1 + ‖p‖) ^ 2) →
    MeasureTheory.Integrable (fun p : E3 => ‖iteratedFDeriv ℝ 6 σ p‖) →
    ∀ (ψ : E3 → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
    (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ * σ (kmomInt ℓ n) *
        ‖Submission.BoseGases.kinFT (winState ℓ ψ) (kmomInt ℓ n)‖ ^ 2)
      ≤ ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : E3,
          σ p * ‖Submission.BoseGases.kinFT (winState ℓ ψ) p‖ ^ 2)
        + K * (∫ p : E3, ‖iteratedFDeriv ℝ 6 σ p‖) * (ℓ ^ 3)⁻¹
            * Work.BoseKinLoc.gapBare ℓ 0 ψ :=
  windowAlias_of_pieces lattice_symbol_eq_alias
    (winState_image_sum_le norm_symOp_le_of_dist)

end Work.BoseBoxFock
