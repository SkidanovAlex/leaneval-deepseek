import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.WinAuxAssembly
import Submission.Work.BoseBoxFock.winAux_geom
import Submission.Work.BoseBoxFock.winAux_winW_cs
import Submission.Work.BoseBoxFock.winAux_winW_integrable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

theorem winState_image_sum_le
    (hW2 : ∀ {σ : EuclideanSpace ℝ (Fin 3) → ℝ} {g : EuclideanSpace ℝ (Fin 3) → ℂ}
      (hσ : ContDiff ℝ (⊤ : ENat) σ)
      (hσ6 : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => ‖iteratedFDeriv ℝ 6 σ p‖))
      (hσg : ∃ A : ℝ, ∀ p : EuclideanSpace ℝ (Fin 3), |σ p| ≤ A * (1 + ‖p‖) ^ 2)
      (hg : ContDiff ℝ (⊤ : ENat) g) (hgc : HasCompactSupport g) {x : EuclideanSpace ℝ (Fin 3)}
      (hx : x ∉ tsupport g),
      ‖Work.BoseBoxFock.symOp σ g x‖ ≤ 27 * ((2 * Real.pi) ^ 3)⁻¹ * Work.BoseBoxFock.iterDerivL1 6 σ *
        ∫ y : EuclideanSpace ℝ (Fin 3), ‖g y‖ / ‖x - y‖ ^ 6) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ℓ : ℝ}, 0 < ℓ → ∀ (σ : EuclideanSpace ℝ (Fin 3) → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) σ →
      (∃ A : ℝ, ∀ p, |σ p| ≤ A * (1 + ‖p‖) ^ 2) →
      MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => ‖iteratedFDeriv ℝ 6 σ p‖) →
      ∀ (ψ : EuclideanSpace ℝ (Fin 3) → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
      ‖∑' m : Fin 3 → ℤ, (if m = 0 then 0 else
          (∫ x : EuclideanSpace ℝ (Fin 3),
            (starRingEnd ℂ) (Work.BoseBoxFock.winState ℓ ψ x) *
              Work.BoseBoxFock.symOp σ (Work.BoseBoxFock.winState ℓ ψ)
                (x + ℓ • Work.BoseBoxFock.latVec m)).re)‖
        ≤ C * (∫ p : EuclideanSpace ℝ (Fin 3), ‖iteratedFDeriv ℝ 6 σ p‖) * (ℓ ^ 3)⁻¹ *
            Work.BoseKinLoc.gapBare ℓ 0 ψ :=
  Work.BoseBoxFock.winAuxAssembly hW2 Work.BoseBoxFock.winAux_geom
    Work.BoseBoxFock.winAux_winW_integrable Work.BoseBoxFock.winAux_winW_cs

end Work.BoseBoxFock
