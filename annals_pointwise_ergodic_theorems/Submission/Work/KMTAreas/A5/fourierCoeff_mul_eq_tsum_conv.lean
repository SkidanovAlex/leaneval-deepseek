import Mathlib
import Submission.Work.Analysis.Fourier.fourierCoeff_summable_series
import Submission.Work.Analysis.Fourier.fourierCoeff_mul_summable_series
import Submission.Work.Analysis.IonescuWainger.EtaCut
import Submission.Work.Analysis.IonescuWainger.exists_goodMajorArcs_nonAliasing
import Submission.Work.Analysis.IonescuWainger.iwQl_le
import Submission.Work.Analysis.IonescuWainger.iw_height_card_le
import Submission.Work.Analysis.IonescuWainger.memLp_periodize
import Submission.Work.Analysis.IonescuWainger.multiplier_add
import Submission.Work.Analysis.IonescuWainger.multiplier_comp
import Submission.Work.Analysis.IonescuWainger.norm_iwOpSet_le
import Submission.Work.Analysis.IonescuWainger.one_div_le_norm_of_ne
import Submission.Work.Analysis.IonescuWainger.supportedInArc_periodize

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A5

open MeasureTheory
open scoped BigOperators

theorem fourierCoeff_mul_eq_tsum_conv {F G : Work.Analysis.IonescuWainger.Circle → ℂ}
    (hF : MeasureTheory.MemLp F 2 Work.Analysis.IonescuWainger.circleMeasure)
    (hG : MeasureTheory.MemLp G 2 Work.Analysis.IonescuWainger.circleMeasure)
    (hFs : Summable (fun j : ℤ => ‖fourierCoeff F j‖)) (m : ℤ) :
    fourierCoeff (fun ξ => F ξ * G ξ) m
      = ∑' j : ℤ, fourierCoeff F j * fourierCoeff G (m - j) := by
  set a : ℤ → ℂ := fun j => fourierCoeff F j with ha
  have ha_summ : Summable (fun j : ℤ => ‖a j‖) := by simpa [ha] using hFs
  -- ### The Fourier series of `F`, as a continuous function `Fc`.
  have hsummC : Summable
      (fun j : ℤ => a j • (fourier (T := 1) j : C(AddCircle (1:ℝ), ℂ))) := by
    refine Summable.of_norm_bounded ha_summ (fun j => ?_)
    rw [norm_smul, fourier_norm, mul_one]
  obtain ⟨Fc, hFc⟩ : ∃ Fc : C(AddCircle (1:ℝ), ℂ),
      ∀ ξ, HasSum (fun j => a j * fourier (T := 1) j ξ) (Fc ξ) :=
    ⟨∑' j, a j • (fourier (T := 1) j : C(AddCircle (1:ℝ), ℂ)), fun ξ => by
      simpa using (ContinuousMap.evalCLM ℂ ξ).hasSum hsummC.hasSum⟩
  have hFc_lp : MemLp (⇑Fc) 2 Work.Analysis.IonescuWainger.circleMeasure :=
    MemLp.of_bound Fc.continuous.aestronglyMeasurable ‖Fc‖
      (ae_of_all _ fun ξ => ContinuousMap.norm_coe_le_norm Fc ξ)
  -- ### The Fourier coefficients of `Fc` are `a`.
  have hFc_coeff : fourierCoeff (⇑Fc) = a :=
    Work.Analysis.Fourier.fourierCoeff_summable_series ha_summ hFc
  -- ### `F =ᵐ Fc`
  have hF_eq : F =ᵐ[Work.Analysis.IonescuWainger.circleMeasure] ⇑Fc := by
    have h1 := hasSum_fourier_series_L2 (hF.toLp F)
    have h2 := hasSum_fourier_series_L2 (hFc_lp.toLp (⇑Fc))
    have h1' : HasSum (fun j : ℤ => a j • fourierLp (T:=1) 2 j) (hF.toLp F) := by
      have hcoeff : (fun j : ℤ => a j • fourierLp (T:=1) 2 j)
          = (fun j : ℤ => fourierCoeff (⇑(hF.toLp F)) j • fourierLp (T:=1) 2 j) := by
        funext j
        rw [ha]
        simp only
        rw [← congrFun (fourierCoeff_congr_ae hF.coeFn_toLp) j]
      rw [hcoeff]; exact h1
    have h2' : HasSum (fun j : ℤ => a j • fourierLp (T:=1) 2 j) (hFc_lp.toLp (⇑Fc)) := by
      have hcoeff : (fun j : ℤ => a j • fourierLp (T:=1) 2 j)
          = (fun j : ℤ => fourierCoeff (⇑(hFc_lp.toLp (⇑Fc))) j • fourierLp (T:=1) 2 j) := by
        funext j
        rw [congrFun (fourierCoeff_congr_ae hFc_lp.coeFn_toLp) j, congrFun hFc_coeff j]
      rw [hcoeff]; exact h2
    have heq : hF.toLp F = hFc_lp.toLp (⇑Fc) := HasSum.unique h1' h2'
    have h3 : ⇑(hF.toLp F) =ᵐ[Work.Analysis.IonescuWainger.circleMeasure] ⇑(hFc_lp.toLp (⇑Fc)) := by rw [heq]
    exact hF.coeFn_toLp.symm.trans (h3.trans hFc_lp.coeFn_toLp)
  -- ### The convolution identity for `Fc`.
  have hkey : fourierCoeff (fun ξ => ⇑Fc ξ * G ξ) m
      = ∑' j : ℤ, a j * fourierCoeff G (m - j) :=
    Work.Analysis.Fourier.fourierCoeff_mul_summable_series ha_summ hFc hG m
  have hcongr : fourierCoeff (fun ξ => F ξ * G ξ) = fourierCoeff (fun ξ => ⇑Fc ξ * G ξ) :=
    fourierCoeff_congr_ae (hF_eq.mul (Filter.EventuallyEq.refl _ G))
  rw [congrFun hcongr m, hkey]

end Work.KMTAreas.A5
