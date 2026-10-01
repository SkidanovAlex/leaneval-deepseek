import Mathlib
import Submission.Work.LinnikAreas.Density4.TestFun
import Submission.Work.LinnikAreas.Density4.testfun_conv

namespace Work.LinnikAreas.Density4

open MeasureTheory
noncomputable section

/-- The full-line representation of `fT`: since `gT` is supported on `[-γ,γ]`, the convolution
over all of `ℝ` agrees with the interval integral over `[-γ,γ]` (which is `testfun_conv`). -/
theorem fT_eq_convT {θ lam : ℝ} (hθ1 : Real.pi / 2 < θ) (hθ2 : θ < Real.pi) (hlam : 0 < lam) :
    ∀ v ∈ Set.Icc (0:ℝ) (2 * gammaT θ lam),
      fT θ lam v = ∫ s : ℝ, gT θ lam s * gT θ lam (v - s) := by
  intro v hv
  have hγ : 0 < gammaT θ lam := gammaT_pos hθ1 hθ2 hlam
  rw [testfun_conv θ lam v hθ1 hθ2 hlam hv.1]
  rw [intervalIntegral.integral_of_le (by linarith : -(gammaT θ lam) ≤ gammaT θ lam),
      integral_Ioc_eq_integral_Ioo]
  refine setIntegral_eq_integral_of_forall_compl_eq_zero (fun t ht => ?_)
  have habs : gammaT θ lam ≤ |t| := by
    have h1 : t ≤ -(gammaT θ lam) ∨ gammaT θ lam ≤ t := by
      by_contra h
      push Not at h
      exact ht ⟨h.1, h.2⟩
    rcases h1 with h | h
    · rw [abs_of_nonpos (by linarith)]; linarith
    · rw [abs_of_nonneg (by linarith)]; exact h
  rw [gT_eq_zero_of_gamma_le_abs hθ1 hθ2 hlam habs, zero_mul]

end

end Work.LinnikAreas.Density4
