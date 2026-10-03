import Mathlib
import Submission.Work.KMTAreas.A7.Tle_varphiNt_bounded

namespace Work.KMTAreas.A7

/-- The `ℓ¹` norm of the Ionescu--Wainger kernel of a compactly supported `C²` function `F` is
bounded by the pointwise quadratic decay proved in `iwKernel_decay_of_bump`, summed against the
comparison weight `kmtKernWeight`. -/
theorem tsum_norm_iwKernel_le (A : Finset Work.Analysis.IonescuWainger.Circle) (F : ℝ → ℂ)
    {S : ℝ} (hS : 0 ≤ S) (hcd : ContDiff ℝ 2 F) (hcs : HasCompactSupport F)
    (h1 : (∫ y, ‖F y‖) ≤ S) (h2 : (∫ y, ‖iteratedDeriv 2 F y‖) ≤ S) :
    (∑' j : ℤ, ‖Work.Analysis.IWMultiplier.iwKernel
        (Work.Analysis.IonescuWainger.iwSymbolSet A (Work.Analysis.IonescuWainger.periodize F)) j‖)
      ≤ (4 * ((A.card : ℝ) * S) + 1) * (∑' j : ℤ, ‖Work.KMTAreas.A7.kmtKernWeight j‖) := by
  have hdec := iwKernel_decay_of_bump A hcd hcs hS h1 h2
  have hsummR : Summable (fun j : ℤ => (4 * ((A.card : ℝ) * S) + 1) * ‖kmtKernWeight j‖) :=
    summable_kmtKernWeight.mul_left _
  have hsummL : Summable (fun j : ℤ => ‖Work.Analysis.IWMultiplier.iwKernel
      (Work.Analysis.IonescuWainger.iwSymbolSet A
        (Work.Analysis.IonescuWainger.periodize F)) j‖) :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) hdec hsummR
  have h := Summable.tsum_le_tsum hdec hsummL hsummR
  rwa [tsum_mul_left] at h

end Work.KMTAreas.A7
