import Mathlib
import Submission.Lib.Unif2.Work.Drive.polarPtBasics

namespace Work.Drive

open MeasureTheory Set

/-- **The fundamental theorem of calculus along a ray.**  For a `C¹` compactly supported function
`ψ : ℂ → ℝ` and any direction `θ`, the integral over `r ∈ (0,∞)` of the negative radial derivative
of `ψ` along the ray `r ↦ a + r e^{iθ}` equals `ψ a`.

This is `HasCompactSupport.integral_Ioi_deriv_eq` applied to `g r = ψ (a + r e^{iθ})`: the radial
derivative is the ordinary derivative of `g`, `g` is `C¹` (composition of `ψ` with the affine
map `r ↦ a + r e^{iθ}`) and compactly supported (its support is contained in the closed bounded
preimage of `tsupport ψ`, hence so is `tsupport g`), and `g 0 = ψ a`. -/
theorem integral_polar_deriv_eq {ψ : ℂ → ℝ} {a : ℂ} (hψ : ContDiff ℝ 1 ψ)
    (hψc : HasCompactSupport ψ) (θ : ℝ) :
    (∫ r in Set.Ioi (0 : ℝ), -deriv (fun r : ℝ => ψ (a + Work.Drive.polarPt (r, θ))) r)
      = ψ a := by
  set u : ℂ := (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I with hu
  have hu_norm_sq : ‖u‖ ^ 2 = 1 := by
    rw [hu, ← Complex.normSq_eq_norm_sq, Complex.normSq_add_mul_I]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hu_norm : ‖u‖ = 1 := by
    have := norm_nonneg u
    nlinarith
  have hfun_eq : (fun r : ℝ => ψ (a + Work.Drive.polarPt (r, θ)))
      = fun r : ℝ => ψ (a + r • u) := by
    funext r
    rw [Work.Drive.polarPt_eq_smul, hu]
  have hcd : ContDiff ℝ 1 (fun r : ℝ => ψ (a + r • u)) :=
    hψ.comp (contDiff_const.add (contDiff_id.smul contDiff_const))
  have hgc : HasCompactSupport (fun r : ℝ => ψ (a + r • u)) := by
    obtain ⟨C, hC⟩ := hψc.isBounded.exists_norm_le
    refine IsCompact.of_isClosed_subset (isCompact_Icc (a := -(C + ‖a‖)) (b := C + ‖a‖))
      (isClosed_tsupport _) ?_
    refine closure_minimal ?_ isClosed_Icc
    intro r hr
    have h1 : a + r • u ∈ Function.support ψ := by
      simpa [Function.mem_support] using hr
    have h2 : a + r • u ∈ tsupport ψ := subset_tsupport ψ h1
    have h3 : ‖a + r • u‖ ≤ C := hC _ h2
    have hnorm : ‖r‖ * ‖u‖ ≤ C + ‖a‖ := by
      calc ‖r‖ * ‖u‖ = ‖r • u‖ := by rw [norm_smul]
        _ = ‖(a + r • u) - a‖ := by rw [add_sub_cancel_left]
        _ ≤ ‖a + r • u‖ + ‖a‖ := norm_sub_le _ _
        _ ≤ C + ‖a‖ := by linarith
    have hrle : ‖r‖ ≤ C + ‖a‖ := by rwa [hu_norm, mul_one] at hnorm
    rw [Set.mem_Icc]
    exact abs_le.mp (by rwa [Real.norm_eq_abs] at hrle)
  rw [hfun_eq]
  rw [MeasureTheory.integral_neg]
  rw [HasCompactSupport.integral_Ioi_deriv_eq hcd hgc 0]
  simp

end Work.Drive
