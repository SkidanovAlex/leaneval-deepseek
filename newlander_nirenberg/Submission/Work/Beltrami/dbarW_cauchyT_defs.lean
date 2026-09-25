import Mathlib
import Submission.Work.Beltrami.Cauchy

noncomputable section
namespace Work.Beltrami

open MeasureTheory
open scoped ContDiff RealInnerProductSpace

/-! ## The radial cutoff kernel -/

/-- The radial cutoff profile `s ↦ ψ(s/ε² - 1)`, where `ψ` is the standard smooth
step function (`0` on `(-∞,0]`, `1` on `[1,∞)`). -/
def cutProfile (ε : ℝ) (s : ℝ) : ℝ := Real.smoothTransition (s / ε^2 - 1)

theorem differentiable_cutProfile (ε : ℝ) : Differentiable ℝ (cutProfile ε) := by
  unfold cutProfile
  exact (Real.smoothTransition.contDiff (n := 1)).differentiable (by simp) |>.comp (by fun_prop)

/-- The cutoff kernel `ψ(‖u‖²/ε² - 1) · u⁻¹`. -/
def cutK (ε : ℝ) (u : ℂ) : ℂ := (cutProfile ε (‖u‖^2) : ℂ) * u⁻¹

/-- `dbarW` is a derivation. -/
theorem dbarW_mul {F G : ℂ → ℂ} {u : ℂ} (hF : DifferentiableAt ℝ F u)
    (hG : DifferentiableAt ℝ G u) :
    dbarW (fun y => F y * G y) u = dbarW F u * G u + F u * dbarW G u := by
  unfold dbarW dzbarCoeff
  rw [fderiv_fun_mul hF hG]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- `dbarW` of `u ↦ 1/u` vanishes (off the origin). -/
theorem dbarW_inv {u : ℂ} (hu : u ≠ 0) : dbarW (fun z : ℂ => z⁻¹) u = 0 := by
  have h1 := (hasDerivAt_inv hu).hasFDerivAt
  have h2 : HasFDerivAt (fun z : ℂ => z⁻¹)
      ((ContinuousLinearMap.toSpanSingleton ℂ (-(u ^ 2)⁻¹)).restrictScalars ℝ) u :=
    h1.restrictScalars ℝ
  unfold dbarW dzbarCoeff
  rw [h2.fderiv]
  simp only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul]
  rw [I_mul_I_mul]; ring

/-- `dbarW` of a radial function `u ↦ h(‖u‖²)`. -/
theorem dbarW_radial {h : ℝ → ℝ} (hh : Differentiable ℝ h) (u : ℂ) :
    dbarW (fun u : ℂ => (h (‖u‖^2) : ℂ)) u = ((deriv h (‖u‖^2) : ℝ) : ℂ) * u := by
  have h2 : HasFDerivAt h (ContinuousLinearMap.toSpanSingleton ℝ (deriv h (‖u‖^2))) (‖u‖^2) :=
    (hh (‖u‖^2)).hasDerivAt.hasFDerivAt
  have h1 : HasFDerivAt (fun u : ℂ => ‖u‖^2) (2 • innerSL ℝ u) u := by
    rw [← fderiv_norm_sq_apply u]
    exact ((contDiffAt_id.norm_sq ℝ).differentiableAt one_ne_zero).hasFDerivAt
  have h3 : HasFDerivAt (fun u : ℂ => h (‖u‖^2))
      ((ContinuousLinearMap.toSpanSingleton ℝ (deriv h (‖u‖^2))).comp (2 • innerSL ℝ u)) u :=
    h2.comp u h1
  have h4 : HasFDerivAt (fun u : ℂ => (h (‖u‖^2) : ℂ))
      (Complex.ofRealCLM.comp
        ((ContinuousLinearMap.toSpanSingleton ℝ (deriv h (‖u‖^2))).comp (2 • innerSL ℝ u))) u :=
    (Complex.ofRealCLM.hasFDerivAt).comp u h3
  unfold dbarW dzbarCoeff
  rw [h4.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
    smul_apply, smul_eq_mul, Complex.ofRealCLM_apply, innerSL_apply_apply]
  rw [show inner ℝ u (1:ℂ) = u.re by simp, show inner ℝ u Complex.I = u.im by simp]
  set c : ℝ := deriv h (‖u‖^2) with hc
  push_cast
  conv_rhs => rw [← Complex.re_add_im u]
  ring_nf

/-- **Key computation.**  The `∂̄`-derivative of the cutoff kernel is the (rescaled)
smooth step function, independent of the direction. -/
theorem dbarW_cutK (ε : ℝ) (hε : 0 < ε) (u : ℂ) :
    dbarW (cutK ε) u = ((deriv (cutProfile ε) (‖u‖^2) : ℝ) : ℂ) := by
  by_cases hu : u = 0
  · subst hu
    have hd0 : deriv (cutProfile ε) 0 = 0 := by
      have hl : cutProfile ε =ᶠ[nhds (0:ℝ)] (fun _ => 0) := by
        rw [Filter.eventuallyEq_iff_exists_mem]
        refine ⟨Set.Iio (ε^2), IsOpen.mem_nhds isOpen_Iio (pow_pos hε 2), ?_⟩
        intro s hs
        rw [Set.mem_Iio] at hs
        have h3 : s/ε^2 < 1 := by rw [div_lt_one (pow_pos hε 2)]; exact hs
        have h4 : s/ε^2 - 1 < 0 := by linarith
        simp [cutProfile, Real.smoothTransition.zero_of_nonpos (le_of_lt h4)]
      rw [hl.deriv_eq]; simp
    have hloc : cutK ε =ᶠ[nhds (0:ℂ)] (fun _ => 0) := by
      rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨Metric.ball 0 ε, Metric.ball_mem_nhds 0 hε, ?_⟩
      intro u hu
      have h2 : ‖u‖^2 < ε^2 := by
        rw [Metric.mem_ball, dist_zero_right] at hu
        nlinarith [norm_nonneg u]
      have h3 : ‖u‖^2/ε^2 < 1 := by rw [div_lt_one (pow_pos hε 2)]; exact h2
      have h4 : ‖u‖^2/ε^2 - 1 < 0 := by linarith
      simp [cutK, cutProfile, Real.smoothTransition.zero_of_nonpos (le_of_lt h4)]
    have hf : fderiv ℝ (cutK ε) 0 = 0 := by rw [hloc.fderiv_eq]; simp
    unfold dbarW dzbarCoeff
    rw [hf]
    simp only [ContinuousLinearMap.zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow]
    rw [hd0]; simp
  · have hhd := differentiable_cutProfile ε
    have hFd : DifferentiableAt ℝ (fun u : ℂ => (cutProfile ε (‖u‖^2) : ℂ)) u := by
      have hd : Differentiable ℝ (fun u : ℂ => cutProfile ε (‖u‖^2)) :=
        hhd.comp ((contDiff_norm_sq (𝕜 := ℝ) (n := 1)).differentiable (by simp))
      exact Complex.ofRealCLM.differentiableAt.comp u hd.differentiableAt
    have hGd : DifferentiableAt ℝ (fun z : ℂ => z⁻¹) u := differentiableAt_id.inv hu
    have hmul := dbarW_mul (F := fun u : ℂ => (cutProfile ε (‖u‖^2) : ℂ))
      (G := fun z : ℂ => z⁻¹) hFd hGd
    have hker : cutK ε = fun y => (cutProfile ε (‖y‖^2) : ℂ) * y⁻¹ := rfl
    rw [hker, hmul, dbarW_radial hhd, dbarW_inv hu]
    simp only [mul_zero, add_zero]
    rw [mul_assoc, mul_inv_cancel₀ hu, mul_one]


/-! ## The Cauchy integral in convolution form -/

/-- The Cauchy potential written as a convolution with `u ↦ u⁻¹`:
`∫ u, u⁻¹ * f (z + u)`. -/
def cauchyInt (f : ℂ → ℂ) (z : ℂ) : ℂ := ∫ u, u⁻¹ * f (z + u) ∂volume

/-- The Cauchy potential of the definition agrees with the convolution form. -/
theorem cauchyT_eq_cauchyInt (f : ℂ → ℂ) (z : ℂ) :
    cauchyT f z = ((-(Real.pi : ℝ)⁻¹ : ℝ) : ℂ) * cauchyInt f z := by
  unfold cauchyT cauchyInt
  rw [Complex.real_smul]
  congr 1
  have h := MeasureTheory.integral_sub_right_eq_self
    (fun u : ℂ => u⁻¹ * f (u + z)) (μ := volume) (g := z)
  rw [show (∫ ζ, (ζ - z)⁻¹ * f ζ) = ∫ x, (x - z)⁻¹ * f (x - z + z) by
      apply integral_congr_ae; filter_upwards with x; rw [sub_add_cancel]]
  rw [h]
  apply integral_congr_ae; filter_upwards with x
  rw [add_comm]


/-! ## Integration by parts for `∂̄` -/

/-- **Integration by parts for the `∂̄`-operator.** -/
theorem integral_mul_dbarW_eq_neg (F G : ℂ → ℂ)
    (hFG : Integrable (fun u => F u * G u) volume)
    (hF1 : Integrable (fun u => (fderiv ℝ F u 1) * G u) volume)
    (hFI : Integrable (fun u => (fderiv ℝ F u Complex.I) * G u) volume)
    (h1G : Integrable (fun u => F u * (fderiv ℝ G u 1)) volume)
    (hIG : Integrable (fun u => F u * (fderiv ℝ G u Complex.I)) volume)
    (hFd : ∀ u ∈ tsupport G, DifferentiableAt ℝ F u)
    (hGd : ∀ u ∈ tsupport F, DifferentiableAt ℝ G u) :
    ∫ u, F u * dbarW G u ∂volume = -∫ u, dbarW F u * G u ∂volume := by
  have h1 := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (v := (1:ℂ))
    hF1 h1G hFG hFd hGd
  have hI := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (v := Complex.I)
    hFI hIG hFG hFd hGd
  have hL : ∫ u, F u * dbarW G u
      = (2:ℂ)⁻¹ * ((∫ u, F u * (fderiv ℝ G u 1))
          + Complex.I * (∫ u, F u * (fderiv ℝ G u Complex.I))) := by
    rw [show (∫ u, F u * dbarW G u)
        = ∫ u, (2:ℂ)⁻¹ * (F u * (fderiv ℝ G u 1)
            + Complex.I * (F u * (fderiv ℝ G u Complex.I))) by
        congr 1 with u; rw [dbarW, dzbarCoeff]; ring]
    rw [integral_const_mul, integral_add h1G (hIG.const_mul Complex.I), integral_const_mul]
  have hR : ∫ u, dbarW F u * G u
      = (2:ℂ)⁻¹ * ((∫ u, (fderiv ℝ F u 1) * G u)
          + Complex.I * (∫ u, (fderiv ℝ F u Complex.I) * G u)) := by
    rw [show (∫ u, dbarW F u * G u)
        = ∫ u, (2:ℂ)⁻¹ * ((fderiv ℝ F u 1) * G u
            + Complex.I * ((fderiv ℝ F u Complex.I) * G u)) by
        congr 1 with u; rw [dbarW, dzbarCoeff]; ring]
    rw [integral_const_mul, integral_add hF1 (hFI.const_mul Complex.I), integral_const_mul]
  rw [hL, hR, h1, hI]
  ring

