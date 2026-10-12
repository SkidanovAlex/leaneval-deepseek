import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.sharpRowSummable
import Submission.Work.BoseBoxFock.sharpShiftRow
import Submission.Work.BoseBoxFock.tauPhi_row_reduction
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.tauPhi_row_closedBall` — the closed-ball kinetic row at the explicit profile

`FINDING_tauPhi_row_closedBall.md` records the analysis of this node.  The proof below is the
*assembly* of `Submission/Work/BoseBoxFock/tauPhi_row_reduction.lean`:

* `tauPhi_scaled_le_fsKinCoeff` (PROVED there) gives the sharp pointwise bound
  `c²·tauPhi(r/c) ≤ fsKinCoeff (5c/4) r`, so `(T)` follows termwise from the **sharp** row at the
  single cutoff `λ = 5c/4`;
* `Work.BoseBoxFock.sharpShiftRow` is that sharp row (`λ ∈ [5c/4, 7c/4]`, tauPhi-free) — the
  aliasing layer of the chapter;
* `Work.BoseBoxFock.sharpRowSummable` is the summability that makes the termwise comparison of the
  two `tsum`s legitimate.

So this node rests exactly on the sharp-cutoff aliasing row, and on nothing else.
-/

namespace Work.BoseBoxFock

theorem tauPhi_row_closedBall {ℓ c : ℝ} (hℓ : 0 < ℓ) (hc : 0 < c) (hcℓ : 4 * Real.pi ≤ c * ℓ)
    {g : EuclideanSpace ℝ (Fin 3) → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g) (hgc : HasCompactSupport g)
    (hgsupp : tsupport g ⊆ Metric.closedBall 0 (ℓ / 2)) :
    (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ *
        (c ^ 2 * Work.BoseBoxFock.tauPhi (‖Work.BoseBoxFock.kmomInt ℓ n‖ / c)) *
        ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2)
      ≤ ((2 * Real.pi) ^ 3)⁻¹ *
        (∫ p : EuclideanSpace ℝ (Fin 3),
          Submission.BoseGases.fsKinCoeff c ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2) := by
  have hlam : (0 : ℝ) ≤ 5 * c / 4 := by linarith
  have hle : 5 * c / 4 ≤ 7 * c / 4 := by linarith
  exact tauPhi_row_of_sharpShiftRow hℓ hc hcℓ hg hgc hgsupp
    (sharpRowSummable hℓ hlam hg hgc hgsupp)
    (sharpShiftRow hℓ hc hcℓ (le_refl _) hle hg hgc hgsupp)

end Work.BoseBoxFock
