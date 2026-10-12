import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Submission.Work.FourierDerivEnergy
import Submission.Work.SmallBoxBridge.Resolve.dirichlet_sum_eq
import Submission.Work.SmallBoxBridge.Resolve.kinFT_eq_fourier
import Submission.Work.SmallBoxBridge.Resolve.sum_integral_inner_sq_fourier
import Submission.Work.SmallBoxBridge.Resolve.winMode_scaling_identity
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory
open scoped ContDiff FourierTransform SchwartzMap

namespace Work.SmallBoxBridge.Resolve

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

theorem winModeForm_sq_eq_dirichlet (χ : EuclideanSpace ℝ (Fin 3) → ℝ)
    (u : EuclideanSpace ℝ (Fin 3) → ℝ) (hχ : ContDiff ℝ ∞ χ) (hu : ContDiff ℝ ∞ u)
    (hcs : HasCompactSupport u) :
    Submission.BoseGases.winModeForm χ (fun r => r ^ 2) u
      = ∫ x : EuclideanSpace ℝ (Fin 3), ∑ k : Fin 3,
          (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 3) => χ y * u y) x
            (Submission.BoseGases.kcStdBasis k)) ^ 2 := by
  set v : ℝ³ → ℝ := fun y => χ y * u y with hv
  have hv_smooth : ContDiff ℝ ∞ v := hχ.mul hu
  have hv1 : ContDiff ℝ 1 v := hv_smooth.of_le (by norm_num)
  have hcs_v : HasCompactSupport v := hcs.mul_left
  set F : ℝ³ → ℂ := fun y => (v y : ℂ) with hF
  have hF_smooth : ContDiff ℝ ∞ F := by
    simpa only [hF, Function.comp_def, Complex.ofRealCLM_apply] using
      (Complex.ofRealCLM.contDiff.comp hv_smooth)
  have hF_cs : HasCompactSupport F := by
    simpa only [hF, Function.comp_def, Complex.ofRealCLM_apply] using
      (hcs_v.comp_left (show ((0 : ℝ) : ℂ) = 0 by simp))
  let f : SchwartzMap ℝ³ ℂ := hF_cs.toSchwartzMap hF_smooth
  have hf_coe : (f : ℝ³ → ℂ) = F := rfl
  have step1 : Submission.BoseGases.winModeForm χ (fun r => r ^ 2) u
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, ‖p‖ ^ 2 * ‖(𝓕 f) ((2 * Real.pi)⁻¹ • p)‖ ^ 2 := by
    rw [Submission.BoseGases.winModeForm]
    congr 1
    apply integral_congr_ae
    filter_upwards with p
    rw [kinFT_eq_fourier]
    have hfun : (fun y : ℝ³ => (χ y : ℂ) * u y) = (f : ℝ³ → ℂ) := by
      rw [hf_coe, hF]
      funext y
      exact (Complex.ofReal_mul (χ y) (u y)).symm
    rw [hfun, ← SchwartzMap.fourier_coe]
  have step2 : ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, ‖p‖ ^ 2 * ‖(𝓕 f) ((2 * Real.pi)⁻¹ • p)‖ ^ 2
      = (2 * Real.pi) ^ 2 * ∫ ξ : ℝ³, ‖ξ‖ ^ 2 * ‖(𝓕 f) ξ‖ ^ 2 :=
    winMode_scaling_identity (fun ξ => ‖(𝓕 f) ξ‖ ^ 2)
  have step3 : (2 * Real.pi) ^ 2 * ∫ ξ : ℝ³, ‖ξ‖ ^ 2 * ‖(𝓕 f) ξ‖ ^ 2
      = ∫ x : ℝ³, ∑ k : Fin 3, ‖fderiv ℝ (f : ℝ³ → ℂ) x
          (Submission.BoseGases.kcStdBasis k)‖ ^ 2 := by
    rw [← sum_integral_inner_sq_fourier f]
    exact (Submission.BoseGases.integral_fderiv_sq_eq_fourier f).symm
  have step4 : (∫ x : ℝ³, ∑ k : Fin 3, ‖fderiv ℝ (f : ℝ³ → ℂ) x
        (Submission.BoseGases.kcStdBasis k)‖ ^ 2)
      = ∫ x : ℝ³, ∑ k : Fin 3, (fderiv ℝ v x (Submission.BoseGases.kcStdBasis k)) ^ 2 := by
    rw [hf_coe]
    exact dirichlet_sum_eq v hv1
  rw [step1, step2, step3, step4]

end Work.SmallBoxBridge.Resolve
