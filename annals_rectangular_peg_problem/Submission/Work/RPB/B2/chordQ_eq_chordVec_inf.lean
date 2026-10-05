import Mathlib
import Submission.Work.RPB.B2.PhaseDefs
import Submission.Work.RPB.B2.chordVec_eq_mul_chordW_inf
import Submission.Work.RPB.B2.omegaC_real_scale

/-!
# `chordQ` computed with the true chord vector, under mere smoothness (`C^∞`)

`chordQ c τ t r = ω_ℂ(W, ∂_τ W)/‖W‖²` with `W = chordW c τ t r` is, away from the singularities
`r = 0` of `chordW`, the logarithmic derivative `∂_τ arg (chordVec c τ t r)` of the true chord
vector `chordVec c τ t r = c τ (t + r) - c τ (t - r)`.

This file proves that identity from `C^∞`-regularity alone (the sibling statement
`chordQ_eq_chordVec` uses the analytic exponent).  The three ingredients are

* `chordVec c σ t r = r * chordW c σ t r` (`chordVec_eq_mul_chordW_inf`) with `r ≠ 0`, which
  identifies the slice `σ ↦ chordVec c σ t r` as `r` times a differentiable slice, whence
  `deriv (chordVec) = r * deriv (chordW)` (`deriv_const_mul`);
* both `ω_ℂ` and `‖·‖²` are homogeneous of degree `2` in a real scaling
  (`ωC_real_scale`), and the two factors `r²` cancel because `r ≠ 0`.
-/

namespace Work.RPB.B2

theorem chordQ_eq_chordVec_inf (c : ℝ → ℝ → ℂ)
    (hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℝ × ℝ => c z.1 z.2)) (τ t r : ℝ) (hr : r ≠ 0) :
    Work.RPB.B2.chordQ c τ t r = Work.RPV.ωC (Work.RPB.chordVec c τ t r)
      (deriv (fun σ => Work.RPB.chordVec c σ t r) τ) / ‖Work.RPB.chordVec c τ t r‖ ^ 2 := by
  -- the slice `σ ↦ chordVec c σ t r` is smooth, being the difference of two smooth slices of `c`
  have hcv : DifferentiableAt ℝ (fun σ => Work.RPB.chordVec c σ t r) τ := by
    have h1 : DifferentiableAt ℝ (fun σ : ℝ => c σ (t + r)) τ := by
      have hF : DifferentiableAt ℝ (fun z : ℝ × ℝ => c z.1 z.2) (τ, t + r) :=
        (hc.differentiable (by simp)).differentiableAt
      have hG : DifferentiableAt ℝ (fun σ : ℝ => (σ, t + r)) τ := by fun_prop
      exact hF.comp τ hG
    have h2 : DifferentiableAt ℝ (fun σ : ℝ => c σ (t - r)) τ := by
      have hF : DifferentiableAt ℝ (fun z : ℝ × ℝ => c z.1 z.2) (τ, t - r) :=
        (hc.differentiable (by simp)).differentiableAt
      have hG : DifferentiableAt ℝ (fun σ : ℝ => (σ, t - r)) τ := by fun_prop
      exact hF.comp τ hG
    convert h1.sub h2 using 1
    ext σ; rfl
  -- hence so is the slice `σ ↦ chordW c σ t r = chordVec c σ t r / r` (`r ≠ 0`)
  have hWdiff : DifferentiableAt ℝ (fun σ => Work.RPB.B2.chordW c σ t r) τ := by
    have hWfun : (fun σ => Work.RPB.B2.chordW c σ t r)
        = fun σ => Work.RPB.chordVec c σ t r / (r : ℂ) := by
      funext σ
      rw [Work.RPB.B2.chordVec_eq_mul_chordW_inf c hc σ t r, mul_div_cancel_left₀]
      exact_mod_cast hr
    rw [hWfun]
    exact hcv.div_const (r : ℂ)
  -- the `τ`-derivative of `chordVec` is `r` times that of `chordW`
  have hderiv : deriv (fun σ => Work.RPB.chordVec c σ t r) τ
      = (r : ℂ) * Work.RPB.B2.chordWd c τ t r := by
    have hslice : (fun σ => Work.RPB.chordVec c σ t r)
        = fun σ => (r : ℂ) * Work.RPB.B2.chordW c σ t r := by
      funext σ; exact Work.RPB.B2.chordVec_eq_mul_chordW_inf c hc σ t r
    rw [hslice, deriv_const_mul _ hWdiff]
    rw [Work.RPB.B2.chordWd]
  rw [Work.RPB.B2.chordQ, hderiv, Work.RPB.B2.chordVec_eq_mul_chordW_inf c hc τ t r]
  -- both `ωC` and `‖·‖²` scale by `r²`, and the two factors cancel since `r ≠ 0`
  exact (omegaC_real_scale r _ _ hr).symm

end Work.RPB.B2
