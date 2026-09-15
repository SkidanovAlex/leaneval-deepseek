import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Submission.Commons.Analysis.Calculus.integral_Ioi_mul_inv_sq_eq_integral_Ioi_deriv_mul_inv

open MeasureTheory Set Filter
open scoped Topology

namespace Commons.Analysis.Calculus

/-- If `f` is continuous, compactly supported and vanishes on `[-1,1]`, then `t ↦ f t / t²`
is integrable. -/
theorem integrable_div_sq_of_continuous_hasCompactSupport {f : ℝ → ℝ} (hf : Continuous f)
    (hs : HasCompactSupport f) (h0 : ∀ t : ℝ, |t| ≤ 1 → f t = 0) :
    Integrable (fun t : ℝ => f t / t ^ 2) := by
  have hcont : Continuous (fun t : ℝ => f t / t ^ 2) := by
    rw [continuous_iff_continuousAt]
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · have hmem : Set.Ioo (-1:ℝ) 1 ∈ 𝓝 (0:ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
      have heq : (fun t : ℝ => f t / t ^ 2) =ᶠ[𝓝 (0:ℝ)] (fun _ => (0:ℝ)) := by
        filter_upwards [hmem] with t ht
        have hlt : |t| < 1 := by rw [abs_lt]; exact ⟨ht.1, ht.2⟩
        rw [h0 t (le_of_lt hlt)]
        simp
      exact continuousAt_const.congr heq.symm
    · exact (hf.continuousAt).div ((continuous_id.pow 2).continuousAt) (pow_ne_zero 2 hx)
  have hsupp : HasCompactSupport (fun t : ℝ => f t / t ^ 2) := by
    refine hs.mono' ?_
    intro x hx
    rw [Function.mem_support] at hx
    exact subset_tsupport f (by rw [Function.mem_support]; intro hfx; exact hx (by rw [hfx]; simp))
  exact hcont.integrable_of_hasCompactSupport hsupp

theorem integral_Ioi_slope_eq_integral_div_sq {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hs : HasCompactSupport f) (h0 : ∀ t : ℝ, |t| ≤ 1 → f t = 0) :
    (∫ t in Set.Ioi (0 : ℝ), (deriv f t - deriv f (-t)) / t) = ∫ t : ℝ, f t / t ^ 2 := by
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  set φ : ℝ → ℝ := fun t => f t + f (-t) with hφdef
  have hφcd : ContDiff ℝ 1 φ := by
    have h : ContDiff ℝ 2 φ := by
      rw [hφdef]
      exact hf.add (hf.comp contDiff_neg)
    exact h.of_le (by norm_num)
  have hφsupp : HasCompactSupport φ := by
    rw [hφdef]
    exact hs.add (hs.comp_homeomorph (Homeomorph.neg ℝ))
  have hφ0 : ∀ t : ℝ, 0 < t → t ≤ 1 → φ t = 0 := by
    intro t ht0 ht1
    rw [hφdef]
    show f t + f (-t) = 0
    rw [h0 t (by rw [abs_of_pos ht0]; exact ht1),
        h0 (-t) (by rw [abs_neg, abs_of_pos ht0]; exact ht1)]
    ring
  have hkey := integral_Ioi_mul_inv_sq_eq_integral_Ioi_deriv_mul_inv hφcd hφsupp hφ0
  have hA : (∫ t in Ioi (0:ℝ), deriv φ t * t⁻¹)
      = ∫ t in Ioi (0:ℝ), (deriv f t - deriv f (-t))/t := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    show deriv φ t * t⁻¹ = (deriv f t - deriv f (-t))/t
    have h1 : deriv φ t = deriv f t - deriv f (-t) := by
      rw [hφdef]
      change deriv (f + (f ∘ Neg.neg)) t = deriv f t - deriv f (-t)
      rw [deriv_add hfd.differentiableAt
            (hfd.differentiableAt.comp t (differentiable_neg.differentiableAt))]
      have hc : deriv (f ∘ Neg.neg) t = -deriv f (-t) := deriv_comp_neg f t
      rw [hc]
      ring
    rw [h1, div_eq_mul_inv]
  have hF : Integrable (fun t : ℝ => f t / t ^ 2) :=
    integrable_div_sq_of_continuous_hasCompactSupport hf.continuous hs h0
  have hFneg : Integrable (fun t : ℝ => f (-t) / t ^ 2) := by
    refine integrable_div_sq_of_continuous_hasCompactSupport (hf.continuous.comp continuous_neg)
      (hs.comp_homeomorph (Homeomorph.neg ℝ)) ?_
    intro t ht
    rw [h0 (-t) (by rwa [abs_neg])]
  have hrefl : (∫ t in Ioi (0:ℝ), f (-t) / t ^ 2) = ∫ t in Iic (0:ℝ), f t / t ^ 2 := by
    have h := integral_comp_neg_Iic (c := (0:ℝ)) (f := fun x : ℝ => f (-x) / x ^ 2)
    simpa using h.symm
  have hsplit : (∫ t in Ioi (0:ℝ), f t / t ^ 2) + (∫ t in Iic (0:ℝ), f t / t ^ 2)
      = ∫ t : ℝ, f t / t ^ 2 := by
    have h := integral_add_compl (s := Ioi (0:ℝ)) measurableSet_Ioi hF
    rwa [Set.compl_Ioi] at h
  have hsymm : (∫ t in Ioi (0:ℝ), (f t / t ^ 2 + f (-t) / t ^ 2)) = ∫ t : ℝ, f t / t ^ 2 := by
    rw [MeasureTheory.integral_add hF.integrableOn hFneg.integrableOn, hrefl]
    exact hsplit
  have hB : (∫ t in Ioi (0:ℝ), φ t * (t^2)⁻¹) = ∫ t : ℝ, f t / t ^ 2 := by
    rw [hφdef]
    trans ∫ t in Ioi (0:ℝ), (f t / t ^ 2 + f (-t) / t ^ 2)
    · apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      ring
    · exact hsymm
  rw [hA, hB] at hkey
  exact hkey.symm

end Commons.Analysis.Calculus