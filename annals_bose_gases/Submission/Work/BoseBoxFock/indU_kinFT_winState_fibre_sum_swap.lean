import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.frkCore
import Submission.Work.BoseBoxFock.integrableOn_kinFT_winState_fibre
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

theorem indU_kinFT_winState_fibre_sum_swap {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {N : ℕ} (j : Fin n)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (τ : Work.BoseBoxFock.Lab N → ℝ) :
    (∑ k : Work.BoseBoxFock.Lab N, τ k * ∫ x in Submission.BoseGases.abox n ℓ,
        Work.BoseKinLoc.indU ℓ 0 (x j)
          * ((ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT
              (Work.BoseBoxFock.winState ℓ (Work.BoseKinLoc.fibre n j Φ x))
              (Work.BoseBoxFock.kmomLab ℓ N k)‖ ^ 2))
      = ∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x j)
          * (∑ k : Work.BoseBoxFock.Lab N, τ k * ((ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT
              (Work.BoseBoxFock.winState ℓ (Work.BoseKinLoc.fibre n j Φ x))
              (Work.BoseBoxFock.kmomLab ℓ N k)‖ ^ 2)) := by
  -- Each slot summand is integrable on the box: the window indicator times the squared
  -- modulus of the fibre's Fourier transform, multiplied by the constant `(ℓ³)⁻¹`.
  have hInt : ∀ k : Work.BoseBoxFock.Lab N, MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X n =>
        Work.BoseKinLoc.indU ℓ 0 (x j) *
          ((ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT
            (Work.BoseBoxFock.winState ℓ (Work.BoseKinLoc.fibre n j Φ x))
            (Work.BoseBoxFock.kmomLab ℓ N k)‖ ^ 2)) (Submission.BoseGases.abox n ℓ) := by
    intro k
    have h0 := Work.BoseBoxFock.integrableOn_kinFT_winState_fibre hℓ j hΦ
      (Work.BoseBoxFock.kmomLab ℓ N k)
    refine MeasureTheory.IntegrableOn.congr_fun
      (MeasureTheory.Integrable.const_mul h0 ((ℓ ^ 3)⁻¹)) ?_
      (Submission.BoseGases.abox_measurable n ℓ)
    intro x _
    ring
  -- Pointwise, the integrand of the right-hand side is the sum of the summands.
  have hpt : (fun x : Submission.BoseGases.X n => Work.BoseKinLoc.indU ℓ 0 (x j) *
        (∑ k : Work.BoseBoxFock.Lab N, τ k * ((ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT
          (Work.BoseBoxFock.winState ℓ (Work.BoseKinLoc.fibre n j Φ x))
          (Work.BoseBoxFock.kmomLab ℓ N k)‖ ^ 2)))
      = (fun x : Submission.BoseGases.X n => ∑ k : Work.BoseBoxFock.Lab N,
          τ k * (Work.BoseKinLoc.indU ℓ 0 (x j) *
            ((ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT
              (Work.BoseBoxFock.winState ℓ (Work.BoseKinLoc.fibre n j Φ x))
              (Work.BoseBoxFock.kmomLab ℓ N k)‖ ^ 2))) := by
    funext x
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  -- The sum/integral swap, with the constant `τ k` pulled out of each integral.
  have hswap : (∫ x in Submission.BoseGases.abox n ℓ, Work.BoseKinLoc.indU ℓ 0 (x j) *
        (∑ k : Work.BoseBoxFock.Lab N, τ k * ((ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT
          (Work.BoseBoxFock.winState ℓ (Work.BoseKinLoc.fibre n j Φ x))
          (Work.BoseBoxFock.kmomLab ℓ N k)‖ ^ 2)))
      = ∑ k : Work.BoseBoxFock.Lab N, ∫ x in Submission.BoseGases.abox n ℓ,
          τ k * (Work.BoseKinLoc.indU ℓ 0 (x j) *
            ((ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT
              (Work.BoseBoxFock.winState ℓ (Work.BoseKinLoc.fibre n j Φ x))
              (Work.BoseBoxFock.kmomLab ℓ N k)‖ ^ 2)) := by
    rw [hpt]
    exact MeasureTheory.integral_finsetSum Finset.univ
      (f := fun k (x : Submission.BoseGases.X n) => τ k * (Work.BoseKinLoc.indU ℓ 0 (x j) *
            ((ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT
              (Work.BoseBoxFock.winState ℓ (Work.BoseKinLoc.fibre n j Φ x))
              (Work.BoseBoxFock.kmomLab ℓ N k)‖ ^ 2)))
      (fun k _ => MeasureTheory.Integrable.const_mul (hInt k) (τ k))
  rw [hswap]
  exact Finset.sum_congr rfl (fun k _ => (MeasureTheory.integral_const_mul (τ k) _).symm)

end Work.BoseBoxFock
