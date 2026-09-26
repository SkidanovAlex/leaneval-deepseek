/-
# The logarithmic derivative of `λ` is bounded at the cusp `i∞`

The modular lambda function `λ = θ₁₀⁴/θ₀₀⁴` has a simple zero at the cusp `i∞`: writing
`q = 𝕢₂ τ = e^{π i τ}` one has `λ(τ) = Flam q` with `Flam q = 16 q + O(q²)`.  Consequently the
logarithmic derivative

  `λ'(τ)/λ(τ) = π i · q · Flam'(q)/Flam(q) = π i · Flam'(q) / (Flam(q)/q)`

tends to `π i · 16/16 = π i` as `q → 0`, hence as `Im τ → ∞`.  In particular it is bounded at
`i∞`, which is the statement proved here.

The argument only uses the cusp function `Flam = UpperHalfPlane.cuspFunction 2 lambdaFun`
(which is holomorphic near `0` by `UpperHalfPlane.analyticAt_cuspFunction_zero`) together with
the hypothesis `Flam q / q → 16`:
* `Flam 0 = 0` and, since the slope of `Flam` at `0` is `Flam q / q`, `Flam'(0) = 16`;
* the chain rule along `τ ↦ q = 𝕢₂ τ` gives `λ'(τ) = Flam'(q) · π i q`;
* the two limits `Flam'(q) → 16` and `Flam(q)/q → 16` combine to give `λ'/λ → π i`.
-/
import Mathlib
import Submission.Work.Rigidity.LambdaDerivDefs

noncomputable section

open UpperHalfPlane Filter Topology
open scoped Topology

namespace Work.Rigidity

/-- The derivative of the `q`-parameter of level `2`, `𝕢₂ z = e^{π i z}`, is `π i 𝕢₂ z`. -/
lemma deriv_qParam_two (z : ℂ) :
    deriv (Function.Periodic.qParam 2) z = Real.pi * Complex.I * Function.Periodic.qParam 2 z := by
  have hfun : Function.Periodic.qParam 2
      = fun y : ℂ => Complex.exp ((2 * (Real.pi : ℂ) * Complex.I / 2) * y) := by
    funext y
    simp only [Function.Periodic.qParam]
    norm_num
    ring_nf
  have h2 : HasDerivAt (fun y : ℂ => Complex.exp ((2 * (Real.pi : ℂ) * Complex.I / 2) * y))
      (Complex.exp ((2 * (Real.pi : ℂ) * Complex.I / 2) * z)
        * (2 * (Real.pi : ℂ) * Complex.I / 2)) z := by
    have h3 := ((hasDerivAt_id z).const_mul (2 * (Real.pi : ℂ) * Complex.I / 2)).cexp
    simpa using h3
  rw [hfun, h2.deriv]
  have hthis : (2 * (Real.pi : ℂ) * Complex.I / 2) = Real.pi * Complex.I := by ring
  rw [hthis]
  ring

/-- The `q`-expansion `Flam` of `λ` reproduces `λ` on the upper half plane. -/
lemma lamC_eq_Flam_qParam
    (hper : Function.Periodic
      (fun z : ℂ => Work.Kernels.lambdaFun (UpperHalfPlane.ofComplex z)) 2)
    (τ : ℍ) :
    Work.Kernels.LogLambda.lamC (τ : ℂ) =
      Work.Rigidity.Flam (Function.Periodic.qParam 2 (τ : ℂ)) := by
  rw [Work.Kernels.LogLambda.lamC_of_mem τ.im_pos]
  exact (UpperHalfPlane.eq_cuspFunction (h := 2) (f := fun τ : ℍ => Work.Kernels.lambdaFun τ)
    τ (by norm_num) hper).symm

/-- The chain rule along `τ ↦ q = 𝕢₂ τ`:
`λ'(τ) = Flam'(𝕢₂ τ) · π i 𝕢₂ τ`. -/
lemma deriv_lamC_eq
    (hper : Function.Periodic
      (fun z : ℂ => Work.Kernels.lambdaFun (UpperHalfPlane.ofComplex z)) 2)
    (hbdd : UpperHalfPlane.IsBoundedAtImInfty (fun τ : UpperHalfPlane => Work.Kernels.lambdaFun τ))
    (τ : ℍ) :
    deriv Work.Kernels.LogLambda.lamC (τ : ℂ) =
      deriv Work.Rigidity.Flam (Function.Periodic.qParam 2 (τ : ℂ)) *
        (Real.pi * Complex.I * Function.Periodic.qParam 2 (τ : ℂ)) := by
  have hdiffOn : DifferentiableOn ℂ Work.Rigidity.Flam (Metric.ball 0 1) :=
    UpperHalfPlane.differentiableOn_cuspFunction_ball (h := 2)
      (f := fun τ : ℍ => Work.Kernels.lambdaFun τ) (by norm_num) hper
      Work.Rigidity.mdifferentiable_lambdaFun hbdd
  have hwball : Function.Periodic.qParam 2 (τ : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right, Function.Periodic.norm_qParam, Real.exp_lt_one_iff]
    have h : (τ : ℂ).im = (τ.im : ℝ) := rfl
    rw [h]
    nlinarith [Real.pi_pos, τ.im_pos]
  have hFlam_at : DifferentiableAt ℂ Work.Rigidity.Flam (Function.Periodic.qParam 2 (τ : ℂ)) :=
    hdiffOn.differentiableAt (Metric.isOpen_ball.mem_nhds hwball)
  have hqdiff : DifferentiableAt ℂ (Function.Periodic.qParam 2) (τ : ℂ) :=
    Function.Periodic.differentiable_qParam.differentiableAt
  have hEq : Work.Kernels.LogLambda.lamC =ᶠ[𝓝 (τ : ℂ)]
      (Work.Rigidity.Flam ∘ Function.Periodic.qParam 2) := by
    filter_upwards [Work.Kernels.LogLambda.isOpen_U.mem_nhds τ.im_pos] with z hz
    rw [Function.comp_apply, Work.Kernels.LogLambda.lamC_of_mem hz]
    exact (UpperHalfPlane.eq_cuspFunction (h := 2) (f := fun τ : ℍ => Work.Kernels.lambdaFun τ)
      (⟨z, hz⟩ : ℍ) (by norm_num) hper).symm
  rw [Filter.EventuallyEq.deriv_eq hEq, deriv_comp (τ : ℂ) hFlam_at hqdiff, deriv_qParam_two]

theorem isBoundedAtImInfty_deriv_lamC_div_lamC
    (hper : Function.Periodic
      (fun z : ℂ => Work.Kernels.lambdaFun (UpperHalfPlane.ofComplex z)) 2)
    (hbdd : UpperHalfPlane.IsBoundedAtImInfty (fun τ : UpperHalfPlane => Work.Kernels.lambdaFun τ))
    (hlim : Filter.Tendsto (fun q : ℂ => Work.Rigidity.Flam q / q)
      (nhdsWithin 0 {q : ℂ | q ≠ 0}) (nhds 16)) :
    UpperHalfPlane.IsBoundedAtImInfty (fun τ : UpperHalfPlane =>
      deriv Work.Kernels.LogLambda.lamC (τ : ℂ) / Work.Kernels.LogLambda.lamC (τ : ℂ)) := by
  -- `Flam` is holomorphic at `0` (it is the cusp function of the holomorphic, bounded function
  -- `λ`).
  have hFlam_analytic : AnalyticAt ℂ Work.Rigidity.Flam 0 :=
    UpperHalfPlane.analyticAt_cuspFunction_zero (h := 2)
      (f := fun τ : ℍ => Work.Kernels.lambdaFun τ) (by norm_num) hper
      Work.Rigidity.mdifferentiable_lambdaFun hbdd
  -- `Flam 0 = 0`, because `Flam q = q · (Flam q / q) → 0` and `Flam` is continuous at `0`.
  have hFlam0 : Work.Rigidity.Flam 0 = 0 := by
    have hcont : ContinuousAt Work.Rigidity.Flam 0 := hFlam_analytic.continuousAt
    have hiden : Tendsto (fun q : ℂ => q) (𝓝[≠] (0 : ℂ)) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have h1 : Tendsto Work.Rigidity.Flam (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
      have h2 : Tendsto (fun q : ℂ => (Work.Rigidity.Flam q / q) * q)
          (𝓝[≠] (0 : ℂ)) (𝓝 (16 * 0)) := hlim.mul hiden
      simp only [mul_zero] at h2
      refine h2.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with q hq
      exact div_mul_cancel₀ (Work.Rigidity.Flam q) hq
    exact tendsto_nhds_unique (hcont.tendsto.mono_left nhdsWithin_le_nhds) h1
  -- The slope of `Flam` at `0` is `Flam q / q`, so `Flam'(0) = 16`.
  have hderiv0 : deriv Work.Rigidity.Flam 0 = 16 := by
    have hd : DifferentiableAt ℂ Work.Rigidity.Flam 0 := hFlam_analytic.differentiableAt
    have hslope := hd.hasDerivAt.tendsto_slope
    have hfun : slope Work.Rigidity.Flam 0 = fun q : ℂ => Work.Rigidity.Flam q / q := by
      funext q
      simp only [slope, hFlam0, vsub_eq_sub, sub_zero, smul_eq_mul, div_eq_inv_mul]
    rw [hfun] at hslope
    exact tendsto_nhds_unique hslope hlim
  -- `‖Flam q / q‖` is bounded below, and `Flam q ≠ 0`, for `q` near `0`.
  have hB : ∀ᶠ w in 𝓝[≠] (0 : ℂ), (8 : ℝ) ≤ ‖Work.Rigidity.Flam w / w‖ := by
    filter_upwards [hlim.eventually (Metric.ball_mem_nhds (16 : ℂ) (by norm_num : (0 : ℝ) < 8))]
      with w hw
    rw [dist_eq_norm] at hw
    have h16 : ‖(16 : ℂ)‖ = 16 := by norm_num
    have h1 := abs_norm_sub_norm_le (Work.Rigidity.Flam w / w) (16 : ℂ)
    rw [h16] at h1
    have h2 : (16 : ℝ) - ‖Work.Rigidity.Flam w / w‖ ≤ ‖Work.Rigidity.Flam w / w - 16‖ := by
      have h := neg_le_abs (‖Work.Rigidity.Flam w / w‖ - 16); linarith
    linarith
  have hBne : ∀ᶠ w in 𝓝[≠] (0 : ℂ), Work.Rigidity.Flam w ≠ 0 := by
    filter_upwards [hB, self_mem_nhdsWithin] with w hBw _ hzero
    rw [hzero, zero_div, norm_zero] at hBw
    norm_num at hBw
  -- `𝕢₂ τ → 0` as `Im τ → ∞`.
  have hw : Tendsto (fun τ : ℍ => Function.Periodic.qParam 2 (τ : ℂ)) atImInfty (𝓝[≠] (0 : ℂ)) :=
    (Function.Periodic.qParam_tendsto (h := 2) (by norm_num)).comp
      UpperHalfPlane.tendsto_coe_atImInfty
  -- The limit of `Flam'(q)/(Flam(q)/q)` is `Flam'(0)/16 = 1`.
  have h1 : Tendsto (fun w : ℂ => deriv Work.Rigidity.Flam w) (𝓝[≠] (0 : ℂ))
      (𝓝 (deriv Work.Rigidity.Flam 0)) :=
    (hFlam_analytic.deriv.continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  have hratio : Tendsto (fun w : ℂ => deriv Work.Rigidity.Flam w / (Work.Rigidity.Flam w / w))
      (𝓝[≠] (0 : ℂ)) (𝓝 (deriv Work.Rigidity.Flam 0 / 16)) :=
    h1.div hlim (by norm_num)
  have hratio1 : Tendsto (fun w : ℂ => deriv Work.Rigidity.Flam w / (Work.Rigidity.Flam w / w))
      (𝓝[≠] (0 : ℂ)) (𝓝 1) := by
    rw [hderiv0] at hratio
    norm_num at hratio
    exact hratio
  have hpsi : Tendsto (fun w : ℂ => Real.pi * Complex.I *
        (deriv Work.Rigidity.Flam w / (Work.Rigidity.Flam w / w)))
      (𝓝[≠] (0 : ℂ)) (𝓝 (Real.pi * Complex.I)) := by
    have := hratio1.const_mul (Real.pi * Complex.I)
    simpa using this
  -- Transfer the identity `λ'/λ = π i · Flam'(q)/(Flam(q)/q)` to `atImInfty`.
  have hev : (fun τ : ℍ => Real.pi * Complex.I *
        (deriv Work.Rigidity.Flam (Function.Periodic.qParam 2 (τ : ℂ)) /
          (Work.Rigidity.Flam (Function.Periodic.qParam 2 (τ : ℂ))
            / Function.Periodic.qParam 2 (τ : ℂ))))
      =ᶠ[atImInfty] (fun τ : ℍ =>
        deriv Work.Kernels.LogLambda.lamC (τ : ℂ) / Work.Kernels.LogLambda.lamC (τ : ℂ)) := by
    filter_upwards [hw.eventually hBne] with τ hFne
    rw [deriv_lamC_eq hper hbdd τ, lamC_eq_Flam_qParam hper τ]
    have hwne : Function.Periodic.qParam 2 (τ : ℂ) ≠ 0 := Function.Periodic.qParam_ne_zero (τ : ℂ)
    field_simp
  have hlimit : Tendsto (fun τ : ℍ =>
        deriv Work.Kernels.LogLambda.lamC (τ : ℂ) / Work.Kernels.LogLambda.lamC (τ : ℂ))
      atImInfty (𝓝 (Real.pi * Complex.I)) := (hpsi.comp hw).congr' hev
  -- A function tending to `π i` at `i∞` is bounded there.
  rw [UpperHalfPlane.isBoundedAtImInfty_iff]
  have hbd : ∀ᶠ (τ : ℍ) in UpperHalfPlane.atImInfty,
      ‖deriv Work.Kernels.LogLambda.lamC (τ : ℂ) / Work.Kernels.LogLambda.lamC (τ : ℂ)‖
        ≤ ‖(Real.pi : ℂ) * Complex.I‖ + 1 := by
    filter_upwards [hlimit.eventually
      (Metric.ball_mem_nhds (Real.pi * Complex.I) (by norm_num : (0 : ℝ) < 1))] with τ hτ
    rw [dist_eq_norm] at hτ
    calc ‖deriv Work.Kernels.LogLambda.lamC (τ : ℂ) / Work.Kernels.LogLambda.lamC (τ : ℂ)‖
        = ‖(deriv Work.Kernels.LogLambda.lamC (τ : ℂ) / Work.Kernels.LogLambda.lamC (τ : ℂ) -
            Real.pi * Complex.I) + Real.pi * Complex.I‖ := by ring_nf
      _ ≤ ‖deriv Work.Kernels.LogLambda.lamC (τ : ℂ) / Work.Kernels.LogLambda.lamC (τ : ℂ) -
            Real.pi * Complex.I‖ + ‖Real.pi * Complex.I‖ := norm_add_le _ _
      _ ≤ 1 + ‖Real.pi * Complex.I‖ := by linarith [le_of_lt hτ]
      _ = ‖(Real.pi : ℂ) * Complex.I‖ + 1 := by ring
  exact ⟨_, (UpperHalfPlane.atImInfty_mem _).mp hbd⟩

end Work.Rigidity
