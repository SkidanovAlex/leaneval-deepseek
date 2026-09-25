import Mathlib.Analysis.CStarAlgebra.Classes
import Submission.Commons.Analysis.SpecialFunctions.Gamma.digamma_logRem_kernel_nonneg
import Submission.Commons.Analysis.SpecialFunctions.Gamma.digamma_logRem_kernel_le_t_div_12
import Submission.Commons.Analysis.Integral.exp_neg_mul_rpow_integrableOn_Ioi

open Set MeasureTheory Filter Complex
open scoped Real Topology
noncomputable section

namespace Commons.Analysis.SpecialFunctions.Gamma

/-- The digamma log-remainder kernel `1/(e^t-1) - 1/t + 1/2`. -/
private def kernel (t : ℝ) : ℝ := 1 / (Real.exp t - 1) - 1 / t + 1 / 2

/-- pointwise norm of `K(t)·e^{-zt}` on `(0,∞)` is `K(t)·e^{-Re z · t}`. -/
private lemma norm_kernel_cexp {z : ℂ} {t : ℝ} (ht : 0 < t) :
    ‖((kernel t : ℂ) * cexp (-(z * (t : ℂ))))‖ =
      kernel t * Real.exp (-(z.re * t)) := by
  rw [norm_mul]
  have hk0 : ‖(kernel t : ℂ)‖ = |kernel t| := by
    exact RCLike.norm_ofReal (K := ℂ) (r := kernel t)
  have hk : ‖(kernel t : ℂ)‖ = kernel t := by
    rw [hk0]
    exact abs_of_nonneg (digamma_logRem_kernel_nonneg ht)
  have he : ‖cexp (-(z * (t : ℂ)))‖ = Real.exp (-(z.re * t)) := by
    rw [Complex.norm_exp]
    congr 1
    have hre : (-(z * (t : ℂ))).re = -(z.re * t) := by simp
    rw [hre]
  rw [hk, he]

/-- The kernel is continuous on `(0,∞)`. -/
private lemma continuousOn_kernel : ContinuousOn kernel (Ioi (0 : ℝ)) := by
  have hc1 : ContinuousOn (fun t : ℝ => (1 / (Real.exp t - 1) : ℝ)) (Ioi (0 : ℝ)) := by
    have hcont : ContinuousOn (fun t : ℝ => (Real.exp t - 1 : ℝ)) (Ioi (0 : ℝ)) := by
      fun_prop
    have hne : ∀ x ∈ Ioi (0 : ℝ), (Real.exp x - 1 : ℝ) ≠ 0 := by
      intro x hx
      have hx0 : 0 < x := hx
      have hgt : 1 < Real.exp x := (Real.one_lt_exp_iff.mpr hx0)
      linarith
    exact ContinuousOn.div continuousOn_const hcont hne
  have hc2 : ContinuousOn (fun t : ℝ => (1 / t : ℝ)) (Ioi (0 : ℝ)) := by
    exact ContinuousOn.div continuousOn_const continuousOn_id
      (by intro x hx; exact ne_of_gt hx)
  have hc3 : ContinuousOn (fun t : ℝ => ((1 : ℝ) / 2)) (Ioi (0 : ℝ)) := continuousOn_const
  have hmain : ContinuousOn (fun t : ℝ => (1 / (Real.exp t - 1) - 1 / t + 1 / 2)) (Ioi (0 : ℝ)) := by
    exact (hc1.sub hc2).add hc3
  change ContinuousOn (fun t : ℝ => (1 / (Real.exp t - 1) - 1 / t + 1 / 2)) (Ioi (0 : ℝ))
  exact hmain

/-- A.e. strong measurability of `K(t)·e^{-zt}` on `(0,∞)`. -/
private lemma aemeasurable_f (z : ℂ) :
    AEStronglyMeasurable (fun t : ℝ => (kernel t : ℂ) * cexp (-(z * (t : ℂ))))
      (volume.restrict (Ioi (0 : ℝ))) := by
  refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
  have hk : ContinuousOn (fun t : ℝ => (kernel t : ℂ)) (Ioi (0 : ℝ)) := by
    exact Complex.continuous_ofReal.comp_continuousOn continuousOn_kernel
  have he : ContinuousOn (fun t : ℝ => cexp (-(z * (t : ℂ)))) (Ioi (0 : ℝ)) := by
    fun_prop
  exact hk.mul he

/-- `∫₀^∞ (t/12)·e^{-Re z · t}` converges for `0 < Re z`. -/
private lemma integrable_dom (z : ℂ) (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => (t / 12) * Real.exp (-(z.re * t))) (Ioi (0 : ℝ)) := by
  have hσ : (0 : ℝ) < 2 := by norm_num
  have hbase : IntegrableOn (fun r : ℝ => Real.exp (-(z.re * r)) * r ^ ((2 : ℝ) - 1)) (Ioi (0 : ℝ)) := by
    exact Commons.Analysis.Integral.exp_neg_mul_rpow_integrableOn_Ioi (c := z.re) (σ := (2 : ℝ)) hz hσ
  have h2 : IntegrableOn (fun r : ℝ => r * Real.exp (-(z.re * r))) (Ioi (0 : ℝ)) := by
    refine hbase.congr_fun ?_ measurableSet_Ioi
    intro r hr
    change rexp (-(z.re * r)) * r ^ ((2 : ℝ) - 1) = r * rexp (-(z.re * r))
    rw [show ((2 : ℝ) - 1) = (1 : ℝ) by norm_num, Real.rpow_one]
    ring
  have h3 : IntegrableOn (fun r : ℝ => ((1 : ℝ) / 12) * (r * Real.exp (-(z.re * r)))) (Ioi (0 : ℝ)) :=
    h2.const_mul ((1 : ℝ) / 12)
  convert h3 using 1
  ext t
  ring

/-- Domination of `|f|` by the integrable bound `(t/12)·e^{-Re z · t}` on `(0,∞)`. -/
private lemma dom (z : ℂ) (hz : 0 < z.re) :
    ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      ‖(kernel t : ℂ) * cexp (-(z * (t : ℂ)))‖ ≤
        ‖((t / 12) * Real.exp (-(z.re * t)) : ℝ)‖ := by
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
  have hle : kernel t * Real.exp (-(z.re * t)) ≤ (t / 12) * Real.exp (-(z.re * t)) := by
    exact mul_le_mul_of_nonneg_right (digamma_logRem_kernel_le_t_div_12 t ht)
      (le_of_lt (Real.exp_pos (-(z.re * t))))
  have hLHS : ‖(kernel t : ℂ) * cexp (-(z * (t : ℂ)))‖ = kernel t * Real.exp (-(z.re * t)) :=
    norm_kernel_cexp ht
  have ht0 : (0 : ℝ) < t := ht
  have hRHS : ‖((t / 12) * Real.exp (-(z.re * t)) : ℝ)‖ =
      (t / 12) * Real.exp (-(z.re * t)) := by
    rw [Real.norm_eq_abs]
    exact abs_of_nonneg (by positivity)
  rw [hLHS, hRHS]
  exact hle

/-- Complex integrability of `K(t)·e^{-zt}` on `(0,∞)` for `0 < Re z`. -/
private lemma main_aux (z : ℂ) (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => (kernel t : ℂ) * cexp (-(z * (t : ℂ)))) (Ioi (0 : ℝ)) := by
  exact Integrable.mono (integrable_dom z hz) (aemeasurable_f z) (dom z hz)

/-- The digamma log-remainder kernel `1/(e^t-1) - 1/t + 1/2` times `e^{-zt}` is
(absolutely) integrable on `(0,∞)` whenever `0 < Re z`. -/
theorem digamma_logRem_kernel_exp_integrable (z : ℂ) (hz : 0 < z.re) :
    MeasureTheory.IntegrableOn (fun t : ℝ =>
      ((((1 : ℝ) / (Real.exp t - 1) - 1 / t + (1 : ℝ) / 2) : ℝ) : ℂ) *
        Complex.exp (-(z * (t : ℂ)))) (Set.Ioi (0 : ℝ)) := by
  simpa [kernel] using main_aux z hz

end Commons.Analysis.SpecialFunctions.Gamma