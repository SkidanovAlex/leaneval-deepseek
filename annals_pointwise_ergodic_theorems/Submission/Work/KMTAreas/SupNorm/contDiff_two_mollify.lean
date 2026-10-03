import Mathlib

namespace Work.KMTAreas.SupNorm

open MeasureTheory

/-- Smoothing (mollification) against a `C²` compactly supported bump is `C²`: this is the
differentiability-under-the-integral-sign step.  Concretely, writing the average as the
convolution `b ↦ (ρ (-b)) ⋆ φ`, it follows from the general `contDiff_convolution_left`
(for a compactly supported `C²` left factor and a locally integrable right factor). -/
theorem contDiff_two_mollify {φ : ℝ → ℂ} (hφ : Continuous φ) {ρ : ℝ → ℝ}
    (hρ : ContDiff ℝ 2 ρ) (hρs : HasCompactSupport ρ) :
    ContDiff ℝ 2 (fun ξ => ∫ b, (ρ b : ℂ) * φ (ξ + b)) := by
  -- The reflected bump is again `C²` with compact support.
  have hρneg : ContDiff ℝ 2 (fun b : ℝ => (ρ (-b) : ℂ)) :=
    (Complex.ofRealCLM.contDiff).comp (hρ.comp contDiff_neg)
  have hρsneg : HasCompactSupport (fun b : ℝ => (ρ (-b) : ℂ)) := by
    have h1 : HasCompactSupport (fun b : ℝ => ρ (-b)) :=
      hρs.comp_homeomorph (Homeomorph.neg ℝ)
    exact h1.comp_left (g := fun x : ℝ => (x : ℂ)) (by simp)
  -- Convolution with a compactly supported `C²` factor is `C²`.
  have hpc := hρsneg.contDiff_convolution_left (L := ContinuousLinearMap.mul ℝ ℂ) hρneg
    (hφ.locallyIntegrable (μ := volume))
  -- Identify the requested average with that convolution (substituting `b ↦ -b`).
  have key : (fun ξ : ℝ => ∫ b, (ρ b : ℂ) * φ (ξ + b))
      = (fun ξ : ℝ => (convolution (fun b : ℝ => (ρ (-b) : ℂ)) φ
          (ContinuousLinearMap.mul ℝ ℂ) volume) ξ) := by
    funext ξ
    rw [convolution_def]
    simp only [ContinuousLinearMap.mul_apply']
    rw [← integral_neg_eq_self (fun b : ℝ => (ρ b : ℂ) * φ (ξ + b)) volume]
    simp only [sub_eq_add_neg]
  rw [key]
  exact hpc

end Work.KMTAreas.SupNorm
