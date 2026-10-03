import Mathlib

/-!
# The `∂̄` operator and the regularized Cauchy transform on `ℂ`

This module sets up the objects used to prove Cauchy–Pompeiu solvability of the inhomogeneous
Cauchy–Riemann equation on `ℂ` for `C^∞` **compactly supported** data:

* `dbar f z = ∂_x f z + i ∂_y f z`, expressed through the real Fréchet derivative;
* `cut`, a smooth radial cutoff which is `1` on `closedBall 0 (1/2)` and `0` off `ball 0 1`;
* `cauchyT ω`, the *regularized* Cauchy transform
  `cauchyT ω z = -(1/π) ∫ η, (ω (z+η) - ω z * cut η) / η`,
  the regularization making the integrand absolutely integrable in dimension two;
* `cutFam ε`, the smooth cutoff used in the `ε → 0` argument.

We also record the elementary algebraic properties of `dbar` (additivity, product rule, the fact
that the identity is `∂̄`-closed, `∂̄` of the inverse, and the radial chain rule
`∂̄ (h ∘ ‖·‖²) z = 2 h'(‖z‖²) z`).

Note on notation: in this Mathlib revision the regularity index of `ContDiff` lives in
`ℕ∞ω = WithTop ℕ∞`, whose top element `⊤` is the *analytic* level `ω`; `C^∞` is the level `∞`
(`cinf` below).  The Cauchy transform is `C^∞` but not real-analytic, so `cinf` is the right index.
-/

open MeasureTheory
open scoped Topology

noncomputable section

namespace Work.Analysis.Complex.DbarCauchy

/-- The `C^∞` regularity level as an element of `ℕ∞ω = WithTop ℕ∞` (the notation `∞` of the
`ContDiff` scope, spelled out so that the identifier `ω` stays available for functions). -/
abbrev cinf : WithTop ℕ∞ := ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- **The `∂̄` operator on `ℂ`**: `∂̄f z = ∂_x f z + i ∂_y f z`, written with the real Fréchet
derivative (`fderiv ℝ f z 1` is `∂_x f z` and `fderiv ℝ f z Complex.I` is `∂_y f z`). -/
def dbar (f : ℂ → ℂ) (z : ℂ) : ℂ := fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I

/-- The smooth radial cutoff `Ψ η = smoothTransition (2 - 4‖η‖²)`.  It equals `1` on
`closedBall 0 (1/2)` and vanishes outside `ball 0 1`. -/
def cut (z : ℂ) : ℝ := Real.smoothTransition (2 - 4 * ‖z‖ ^ 2)

/-- `cut`, as a complex-valued function. -/
def cutC (z : ℂ) : ℂ := (cut z : ℂ)

/-- The smooth cutoff family used in the divergence computation:
`cutFam ε η = Ã(‖η‖²/ε² - 1)` where `Ã = smoothTransition`; it vanishes on `ball 0 ε` and equals
`1` off `ball 0 (√2 ε)`. -/
def cutFam (ε : ℝ) (z : ℂ) : ℂ := (Real.smoothTransition (‖z‖ ^ 2 / ε ^ 2 - 1) : ℂ)

/-- The **regularized Cauchy transform** of `ω` (with respect to the cutoff `cut`):
`cauchyT ω z = -(1/π) ∫ η, (ω (z + η) - ω z * cut η) / η`. -/
def cauchyT (ω : ℂ → ℂ) : ℂ → ℂ :=
  fun z => -((Real.pi : ℂ)⁻¹) * ∫ η, (ω (z + η) - ω z * cutC η) / η

/-- The derivative in `z` of the regularized Cauchy integrand
`z ↦ (ω (z + η) - ω z * cut η)/η`, as a continuous linear map:
`h ↦ η⁻¹ * (dω_{z+η} h - cut η * dω_z h)`. -/
abbrev dIntegrand (ω : ℂ → ℂ) (z η : ℂ) : ℂ →L[ℝ] ℂ :=
  η⁻¹ • ((fderiv ℝ ω (z + η)) - (cutC η) • fderiv ℝ ω z)

/-- The value of `dIntegrand` on a vector. -/
lemma dIntegrand_apply (ω : ℂ → ℂ) (z η h : ℂ) :
    dIntegrand ω z η h
      = η⁻¹ * ((fderiv ℝ ω (z + η)) h - cutC η * (fderiv ℝ ω z) h) := by
  simp only [dIntegrand, smul_apply, sub_apply, smul_apply, smul_eq_mul]

/-! ### Elementary properties of the cutoff -/

@[simp] theorem cut_zero : cut 0 = 1 := by
  simp [cut, Real.smoothTransition.eq_one_iff_one_le]

theorem cut_eq_one {z : ℂ} (hz : ‖z‖ ^ 2 ≤ 1 / 4) : cut z = 1 := by
  refine Real.smoothTransition.one_of_one_le ?_
  nlinarith [norm_nonneg z]

theorem cut_eq_zero {z : ℂ} (hz : 3 / 4 ≤ ‖z‖ ^ 2) : cut z = 0 := by
  refine Real.smoothTransition.zero_of_nonpos ?_
  nlinarith [norm_nonneg z]

theorem cut_nonneg (z : ℂ) : 0 ≤ cut z := Real.smoothTransition.nonneg _

theorem cut_le_one (z : ℂ) : cut z ≤ 1 := Real.smoothTransition.le_one _

theorem cut_neg (z : ℂ) : cut (-z) = cut z := by simp [cut]

theorem cutC_eq_one {z : ℂ} (hz : ‖z‖ ^ 2 ≤ 1 / 4) : cutC z = 1 := by
  simp [cutC, cut_eq_one hz]

theorem cutC_neg (z : ℂ) : cutC (-z) = cutC z := by simp [cutC, cut_neg]

theorem contDiff_inner_cut : ContDiff ℝ cinf fun z : ℂ => 2 - 4 * ‖z‖ ^ 2 :=
  ContDiff.sub contDiff_const ((contDiff_norm_sq (𝕜 := ℝ)).const_smul (4 : ℝ))

theorem contDiff_cut : ContDiff ℝ cinf cut :=
  Real.smoothTransition.contDiff.comp contDiff_inner_cut

theorem hasCompactSupport_cut : HasCompactSupport cut := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℂ) 1) ?_
  intro z hz
  simp only [Function.mem_support] at hz
  by_contra h
  simp only [Metric.mem_closedBall, dist_zero_right, not_le] at h
  exact hz (cut_eq_zero (by nlinarith [norm_nonneg z]))

theorem contDiff_cutC : ContDiff ℝ cinf cutC :=
  ContDiff.comp Complex.ofRealCLM.contDiff contDiff_cut

theorem hasCompactSupport_cutC : HasCompactSupport cutC :=
  hasCompactSupport_cut.comp_left (by simp [cutC])

/-! ### Elementary properties of `∂̄` -/

/-- `∂̄` only depends on the germ of the function. -/
theorem dbar_congr {f g : ℂ → ℂ} {z : ℂ} (h : f =ᶠ[𝓝 z] g) : dbar f z = dbar g z := by
  rw [dbar, dbar, h.fderiv_eq]

@[simp] theorem dbar_zero (z : ℂ) : dbar (fun _ : ℂ => (0 : ℂ)) z = 0 := by simp [dbar]

@[simp] theorem dbar_const (c : ℂ) (z : ℂ) : dbar (fun _ : ℂ => c) z = 0 := by simp [dbar]

theorem dbar_add (f g : ℂ → ℂ) (z : ℂ) (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    dbar (fun w => f w + g w) z = dbar f z + dbar g z := by
  change dbar (f + g) z = dbar f z + dbar g z
  rw [dbar, fderiv_add hf hg]
  simp only [dbar, add_apply]
  ring

theorem dbar_mul (f g : ℂ → ℂ) (z : ℂ) (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    dbar (fun w => f w * g w) z = dbar f z * g z + f z * dbar g z := by
  rw [dbar, dbar, dbar, fderiv_fun_mul hf hg]
  simp only [add_apply, smul_apply]
  ring

@[simp] theorem dbar_id (z : ℂ) : dbar (fun w : ℂ => w) z = 0 := by
  simp [dbar]

/-- `∂̄` annihilates the inverse (a holomorphic function), away from the origin. -/
theorem dbar_inv (z : ℂ) (hz : z ≠ 0) : dbar (fun w : ℂ => w⁻¹) z = 0 := by
  have hprod := dbar_mul (fun w : ℂ => w) (fun w : ℂ => w⁻¹) z differentiableAt_id
    (differentiableAt_inv hz)
  rw [dbar_id, zero_mul] at hprod
  have hconst : dbar (fun w : ℂ => w * w⁻¹) z = 0 := by
    have hev : (fun w : ℂ => w * w⁻¹) =ᶠ[𝓝 z] (fun _ : ℂ => (1 : ℂ)) := by
      filter_upwards [isOpen_ne.mem_nhds hz] with w hw
      exact mul_inv_cancel₀ hw
    rw [dbar_congr hev]
    simp
  rw [hconst] at hprod
  have hz0 : z * dbar (fun w : ℂ => w⁻¹) z = 0 := by simpa using hprod.symm
  exact (mul_eq_zero.mp hz0).resolve_left hz

/-- The Fréchet derivative of a radial `ℂ`-valued function. -/
theorem hasFDerivAt_radialC (h : ℝ → ℝ) (h' : ℝ → ℝ) (hh : ∀ σ, HasDerivAt h (h' σ) σ) (z : ℂ) :
    HasFDerivAt (fun w : ℂ => (h (‖w‖ ^ 2) : ℂ))
      ((ContinuousLinearMap.toSpanSingleton ℝ ((h' (‖z‖ ^ 2) : ℝ) : ℂ)).comp
        ((2 : ℝ) • (innerSL ℝ z))) z := by
  have h1 : HasFDerivAt (fun w : ℂ => ‖w‖ ^ 2) ((2 : ℝ) • (innerSL ℝ z)) z := by
    have hd : DifferentiableAt ℝ (fun w : ℂ => ‖w‖ ^ 2) z :=
      ((contDiff_norm_sq (𝕜 := ℝ) (n := 1)).differentiable (by norm_num)) z
    have hh1 := hd.hasFDerivAt
    rw [fderiv_norm_sq] at hh1
    have hcast : ((2 : ℕ) • (innerSL ℝ z) : ℂ →L[ℝ] ℝ) = ((2 : ℝ) • (innerSL ℝ z)) := by
      ext v
      simp only [smul_apply, innerSL_apply_apply, Complex.inner]
      ring
    rwa [Pi.smul_apply, hcast] at hh1
  have h2 : HasFDerivAt h (ContinuousLinearMap.toSpanSingleton ℝ (h' (‖z‖ ^ 2))) (‖z‖ ^ 2) :=
    (hh _).hasFDerivAt
  have h3 := h2.comp z h1
  have h4 := Complex.ofRealCLM.hasFDerivAt.comp z h3
  have key : (Complex.ofRealCLM.comp
      ((ContinuousLinearMap.toSpanSingleton ℝ (h' (‖z‖ ^ 2))).comp ((2 : ℝ) • (innerSL ℝ z))))
      = (ContinuousLinearMap.toSpanSingleton ℝ ((h' (‖z‖ ^ 2) : ℝ) : ℂ)).comp
        ((2 : ℝ) • (innerSL ℝ z)) := by
    ext v
    simp [ContinuousLinearMap.toSpanSingleton_apply, Complex.ofRealCLM_apply]
  rw [key] at h4
  have key2 : (fun w : ℂ => (h (‖w‖ ^ 2) : ℂ)) =
      (⇑Complex.ofRealCLM ∘ h ∘ fun w : ℂ => ‖w‖ ^ 2) := by
    funext w; simp [Function.comp_apply, Complex.ofRealCLM_apply]
  rwa [key2]

/-- **The radial chain rule for `∂̄`**: `∂̄ (h ∘ ‖·‖²) z = 2 h'(‖z‖²) z`. -/
theorem dbar_radialC (h : ℝ → ℝ) (h' : ℝ → ℝ) (hh : ∀ σ, HasDerivAt h (h' σ) σ) (z : ℂ) :
    dbar (fun w : ℂ => (h (‖w‖ ^ 2) : ℂ)) z = 2 * (h' (‖z‖ ^ 2) : ℂ) * z := by
  have hfd := (hasFDerivAt_radialC h h' hh z).fderiv
  rw [dbar, hfd]
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
  generalize hc : ((h' (‖z‖ ^ 2) : ℝ) : ℂ) = c
  rw [Complex.real_smul, Complex.real_smul]
  rw [← Complex.re_add_im z]
  simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero,
    zero_mul, sub_zero, add_zero]
  push_cast
  ring

/-- A continuous function vanishing outside a compact set is bounded. -/
theorem exists_bound_of_cont_of_support {E : Type*} [NormedAddCommGroup E] {f : ℂ → E}
    (hf : Continuous f) {K : Set ℂ} (hK : IsCompact K) (hsupp : ∀ w, w ∉ K → f w = 0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ w : ℂ, ‖f w‖ ≤ M := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun w => ?_⟩
  by_cases hw : w ∈ K
  · exact le_trans (hC w hw) (le_max_left _ _)
  · rw [hsupp w hw]; simp

/-- The norm of the real-valued cutoff. -/
theorem norm_cutC (η : ℂ) : ‖cutC η‖ = |cut η| := by
  have h : ‖cutC η‖ ^ 2 = |cut η| ^ 2 := by
    have h1 : ‖cutC η‖ ^ 2 = cut η * cut η := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp [cutC]
    rw [h1, sq_abs]; ring
  nlinarith [norm_nonneg (cutC η), abs_nonneg (cut η)]

/-- The norm of `1 - cut`. -/
theorem norm_one_sub_cutC (η : ℂ) : ‖1 - cutC η‖ = |1 - cut η| := by
  have h : ‖1 - cutC η‖ ^ 2 = |1 - cut η| ^ 2 := by
    have h1 : ‖1 - cutC η‖ ^ 2 = (1 - cut η) * (1 - cut η) := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp [cutC]
    rw [h1, sq_abs]; ring
  nlinarith [norm_nonneg (1 - cutC η), abs_nonneg (1 - cut η)]

theorem norm_cutC_le_one (η : ℂ) : ‖cutC η‖ ≤ 1 := by
  rw [norm_cutC η, abs_le]
  exact ⟨by linarith [cut_nonneg η], cut_le_one η⟩

/-- `1 - cut` vanishes to first order at the origin: the key bound making the regularized Cauchy
integrand bounded. -/
theorem norm_one_sub_cutC_le (η : ℂ) : ‖1 - cutC η‖ ≤ 2 * ‖η‖ := by
  by_cases hη : ‖η‖ ≤ 1 / 2
  · rw [cutC_eq_one (by nlinarith [norm_nonneg η]), sub_self, norm_zero]
    positivity
  · have h2 : ‖1 - cutC η‖ ≤ 1 := by
      rw [norm_one_sub_cutC η, abs_le]
      exact ⟨by linarith [cut_le_one η], by linarith [cut_nonneg η]⟩
    linarith [not_le.mp hη]

/-- Every finite regularity level is below `C^∞`. -/
theorem natCast_le_cinf (n : ℕ) : (((n : ℕ∞) : WithTop ℕ∞)) ≤ cinf := by
  rw [cinf]
  exact WithTop.coe_le_coe.mpr le_top

end Work.Analysis.Complex.DbarCauchy

end
