import Mathlib
import Submission.Work.Analysis.Complex.DbarCauchy.dbarBar
import Submission.Work.Analysis.Complex.DbarCauchy.integral_dbar_eq_zero

/-!
# Calculus for the conjugate Cauchy--Riemann operator `dbarBar`

The companion facts about `dbarBar = ∂_x - i ∂_y` needed by the weighted `L²` theory of `∂̄`
(the Hörmander basic estimate):

* `integral_dbarBar_eq_zero`: `∫ ∂̄*G = 0` for compactly supported `C¹` `G` — the conjugate of
  `integral_dbar_eq_zero`, immediate from `integral_fderiv_eq_zero`;
* `dbarBar_mul`: the product rule (the analogue of `dbar_mul`).
-/

open MeasureTheory

noncomputable section

open scoped Topology

namespace Work.Analysis.Complex.DbarCauchy

/-- **The integral of `dbarBar G` vanishes** for compactly supported `C¹` `G`. -/
theorem integral_dbarBar_eq_zero (G : ℂ → ℂ) (hG : ContDiff ℝ 1 G) (hc : HasCompactSupport G) :
    ∫ z : ℂ, dbarBar G z = 0 := by
  obtain ⟨R₀, hR₀⟩ := hc.isBounded.subset_closedBall (0 : ℂ)
  set R : ℝ := max R₀ 0 with hRdef
  have hR : tsupport G ⊆ Metric.closedBall 0 R :=
    hR₀.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  have hzero' : ∀ z : ℂ, R < ‖z‖ → fderiv ℝ G z = 0 := by
    intro z hz
    have hopen : IsOpen {z' : ℂ | R < ‖z'‖} := isOpen_lt continuous_const continuous_norm
    have hev : G =ᶠ[𝓝 z] 0 := by
      have hzmem : z ∈ {z' : ℂ | R < ‖z'‖} := hz
      filter_upwards [hopen.mem_nhds hzmem] with w hw
      by_contra hne
      have hmem : w ∈ tsupport G := subset_tsupport G (Function.mem_support.mpr hne)
      have h := hR hmem
      rw [Metric.mem_closedBall, dist_zero_right] at h
      exact absurd h (not_le_of_gt hw)
    rw [hev.fderiv_eq]
    simp
  have hcs : ∀ vec : ℂ, HasCompactSupport fun z : ℂ => fderiv ℝ G z vec := by
    intro vec
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 R) ?_
    intro z hz
    simp only [Function.mem_support] at hz
    by_contra hmem
    rw [Metric.mem_closedBall, dist_zero_right] at hmem
    exact hz (by rw [hzero' z (not_le.mp hmem)]; simp)
  have hint1 : Integrable (fun z : ℂ => fderiv ℝ G z 1) volume :=
    Continuous.integrable_of_hasCompactSupport
      ((hG.continuous_fderiv one_ne_zero).clm_apply continuous_const) (hcs 1)
  have hint2 : Integrable (fun z : ℂ => fderiv ℝ G z Complex.I) volume :=
    Continuous.integrable_of_hasCompactSupport
      ((hG.continuous_fderiv one_ne_zero).clm_apply continuous_const) (hcs Complex.I)
  have key1 := integral_fderiv_eq_zero G hG hc 1
  have key2 := integral_fderiv_eq_zero G hG hc Complex.I
  have hfun : (fun z : ℂ => dbarBar G z)
      = fun z => fderiv ℝ G z 1 - Complex.I * fderiv ℝ G z Complex.I := by
    funext z; rfl
  have hdecomp : ∫ z, dbarBar G z ∂volume
      = (∫ z, fderiv ℝ G z 1 ∂volume) - Complex.I * ∫ z, fderiv ℝ G z Complex.I ∂volume := by
    rw [hfun, integral_sub hint1 (hint2.const_mul Complex.I), integral_const_mul]
  rw [hdecomp, key1, key2]
  simp

/-- **The product rule for `dbarBar`.** -/
theorem dbarBar_mul (f g : ℂ → ℂ) (z : ℂ) (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) :
    dbarBar (fun w => f w * g w) z = dbarBar f z * g z + f z * dbarBar g z := by
  have h1 : fderiv ℝ (fun w => f w * g w) z 1
      = fderiv ℝ f z 1 * g z + f z * fderiv ℝ g z 1 := by
    rw [fderiv_fun_mul hf hg]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
    ring
  have h2 : fderiv ℝ (fun w => f w * g w) z Complex.I
      = fderiv ℝ f z Complex.I * g z + f z * fderiv ℝ g z Complex.I := by
    rw [fderiv_fun_mul hf hg]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
    ring
  simp only [dbarBar, h1, h2]
  ring

/-- **The radial chain rule for `dbarBar`**: `∂̄* (h ∘ ‖·‖²) z = 2 h'(‖z‖²) · conj z`. -/
theorem dbarBar_radialC (h : ℝ → ℝ) (h' : ℝ → ℝ) (hh : ∀ σ, HasDerivAt h (h' σ) σ) (z : ℂ) :
    dbarBar (fun w : ℂ => (h (‖w‖ ^ 2) : ℂ)) z = 2 * (h' (‖z‖ ^ 2) : ℂ) * star z := by
  have hfd := (hasFDerivAt_radialC h h' hh z).fderiv
  rw [dbarBar, hfd]
  have e1 : (((ContinuousLinearMap.toSpanSingleton ℝ ((h' (‖z‖ ^ 2) : ℝ) : ℂ)).comp
      ((2 : ℝ) • (innerSL ℝ z))) 1) = (2 * z.re : ℝ) • ((h' (‖z‖ ^ 2) : ℝ) : ℂ) := by
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply]
    congr 1
    simp only [smul_apply, innerSL_apply_apply, Complex.inner]
    simp [Complex.conj_re]
  have e2 : (((ContinuousLinearMap.toSpanSingleton ℝ ((h' (‖z‖ ^ 2) : ℝ) : ℂ)).comp
      ((2 : ℝ) • (innerSL ℝ z))) Complex.I) = (2 * z.im : ℝ) • ((h' (‖z‖ ^ 2) : ℝ) : ℂ) := by
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply]
    congr 1
    simp only [smul_apply, innerSL_apply_apply, Complex.inner]
    simp [Complex.conj_re, Complex.mul_re]
  rw [e1, e2]
  rw [Complex.real_smul, Complex.real_smul]
  have hconj : star z = (z.re : ℂ) - (z.im : ℂ) * Complex.I := by
    refine Complex.ext ?_ ?_ <;> simp [Complex.mul_re, Complex.mul_im]
  rw [hconj]
  push_cast
  ring

end Work.Analysis.Complex.DbarCauchy
