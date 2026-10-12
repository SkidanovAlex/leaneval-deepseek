import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.KinPSuperadd.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.KinPSuperadd

open Submission

/-- The square-of-a-sum kinetic word of the D1 chain is dominated by `(n+2)` times the
faithful one-particle-sum (diagonal) word.  Two ingredients, both already in the tree:

* `Work.SmallBoxBridge.ModeIdent.kinPWord_eq_pModeForm` identifies the D1 word with the
  corpus mode form `(2π)⁻³∫_p F(‖p‖)·pModeContent s p Φ` (`Re² + Im² = ‖·‖²`);
* `Work.SmallBoxBridge.Cauchy.pModeForm_le_pDiagForm` is the Cauchy--Schwarz step
  `‖Σ_i A_i‖² ≤ (N+1)Σ_i‖A_i‖²` applied to the `N = n+1` slot amplitudes and integrated. -/
theorem kinPWord_le_diagWord {n : ℕ} {s c : ℝ} (hs : 0 < s)
    {Φ : Submission.BoseGases.X (n + 1) → ℝ} (hΦ : Continuous Φ)
    (hint : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.fsKinCoeff c ‖p‖ * ∑ i : Fin (n + 1), (s ^ 3)⁻¹ *
        ∫ x in Submission.BoseGases.abox (n + 1) s,
          ‖Submission.BoseGases.pSlotAmp s p Φ i x‖ ^ 2)) :
    @Submission.BoseGases.kinPWord s c n Φ
      ≤ ((((n + 1 : ℕ) : ℝ) + 1)) *
          @Submission.BoseGases.pDiagForm s (Submission.BoseGases.fsKinCoeff c) (n + 1) Φ
    := by
  rw [Work.SmallBoxBridge.ModeIdent.kinPWord_eq_pModeForm hs hΦ]
  exact Work.SmallBoxBridge.Cauchy.pModeForm_le_pDiagForm (N := n + 1) hs
    (fun r => Submission.BoseGases.fsKinCoeff_nonneg c r) hΦ hint

end Work.KinPSuperadd
