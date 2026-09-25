import Mathlib
import Submission.Work.Beltrami.dbarW_cauchyT_defs

noncomputable section

open MeasureTheory Filter Bornology
open scoped Topology ContDiff

namespace Work.Beltrami

/-!
## The limit of the `∂̄`-derivative of the cutoff kernel

This file evaluates the limit, as `ε → 0⁺`, of the integral

  `∫ u, F u * (deriv (cutProfile ε) (‖u‖²) : ℂ) ∂volume`

for a continuous compactly supported `F : ℂ → ℂ`.  The cutoff profile is
`cutProfile ε s = ψ (s/ε² - 1)` with `ψ = Real.smoothTransition`, so that its
derivative is `ε⁻² ψ'(‖u‖²/ε² - 1)`, an approximate identity at the origin of total
mass `π` (the area form on `ℂ ≅ ℝ²`).  Hence the limit is `π * F 0`.

The proof proceeds by identifying the family `ε ↦ ε⁻² ψ'(‖u‖²/ε² - 1)` with the
standard peak-function family `c ↦ c² φ (c • u)` with `φ = π⁻¹ ψ'(‖·‖² - 1)`,
`c = ε⁻¹`, and applying Mathlib's `tendsto_integral_comp_smul_smul_of_integrable`.
The two analytic inputs are the chain rule for `cutProfile` and the radial
computation `∫_ℂ ψ'(‖x‖² - 1) dx = π`.
-/

/-- The derivative of the standard smooth transition vanishes above `1` (where the
transition is locally constant, equal to one). -/
theorem deriv_smoothTransition_of_one_lt {t : ℝ} (ht : 1 < t) :
    deriv Real.smoothTransition t = 0 := by
  have h : Real.smoothTransition =ᶠ[𝓝 t] (fun _ => (1:ℝ)) := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    exact ⟨Set.Ioi 1, IsOpen.mem_nhds isOpen_Ioi ht,
      fun x hx => Real.smoothTransition.one_of_one_le hx.le⟩
  rw [h.deriv_eq]
  simp

/-- The derivative of the standard smooth transition is nonnegative (the transition
is monotone). -/
theorem deriv_smoothTransition_nonneg (t : ℝ) : 0 ≤ deriv Real.smoothTransition t :=
  Real.smoothTransition.monotone.deriv_nonneg

/-- Chain rule for the cutoff profile: `(cutProfile ε)' s = ψ'(s/ε² - 1)/ε²`. -/
theorem deriv_cutProfile (ε : ℝ) (_hε : ε ≠ 0) (s : ℝ) :
    deriv (cutProfile ε) s = deriv Real.smoothTransition (s / ε^2 - 1) / ε^2 := by
  have h1 : HasDerivAt (fun s : ℝ => s / ε^2 - 1) (1/ε^2) s := by
    have h := (hasDerivAt_id s).div_const (ε^2)
    exact h.sub_const 1
  have h2 : HasDerivAt Real.smoothTransition
      (deriv Real.smoothTransition (s / ε^2 - 1)) (s / ε^2 - 1) :=
    (((Real.smoothTransition.contDiff (n := ⊤)).differentiable (by simp)).differentiableAt).hasDerivAt
  have h3 : HasDerivAt (Real.smoothTransition ∘ fun s : ℝ => s / ε^2 - 1)
      (deriv Real.smoothTransition (s / ε^2 - 1) * (1/ε^2)) s := h2.comp s h1
  change deriv (Real.smoothTransition ∘ fun s : ℝ => s / ε^2 - 1) s = _
  rw [h3.deriv]
  ring

/-- The one-dimensional radial integral: `∫₀^∞ y ψ'(y² - 1) dy = 1/2`, which is the
fundamental theorem of calculus applied to `y ↦ ψ(y² - 1)/2`. -/
theorem integral_Ioi_mul_deriv_smoothTransition :
    ∫ y in Set.Ioi (0:ℝ), y * deriv Real.smoothTransition (y^2 - 1) = 1/2 := by
  have hderiv : ∀ y ∈ Set.Ici (0:ℝ),
      HasDerivAt (fun y : ℝ => (1/2) * Real.smoothTransition (y^2 - 1))
        (y * deriv Real.smoothTransition (y^2 - 1)) y := by
    intro y _
    have h1 : HasDerivAt (fun y : ℝ => y^2 - 1) (2*y) y := by
      have h := (hasDerivAt_pow 2 y).sub_const 1
      simpa using h
    have h2 : HasDerivAt Real.smoothTransition
        (deriv Real.smoothTransition (y^2 - 1)) (y^2 - 1) :=
      (((Real.smoothTransition.contDiff (n := ⊤)).differentiable (by simp)).differentiableAt).hasDerivAt
    have h3 := h2.comp y h1
    have h4 : HasDerivAt (fun y : ℝ => (1/2) * Real.smoothTransition (y^2 - 1))
        ((1/2) * (deriv Real.smoothTransition (y^2 - 1) * (2*y))) y := h3.const_mul (1/2)
    convert h4 using 1
    ring
  have hcont : Continuous (fun y : ℝ => y * deriv Real.smoothTransition (y^2 - 1)) :=
    continuous_id.mul
      (((Real.smoothTransition.contDiff (n := ⊤)).continuous_deriv (by simp)).comp (by fun_prop))
  have hsupp : Function.support (fun y : ℝ => y * deriv Real.smoothTransition (y^2 - 1))
      ⊆ Set.Icc (-2:ℝ) 2 := by
    intro y hy
    rw [Function.mem_support] at hy
    by_contra hcon
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hcon
    have hy2 : 1 < y^2 - 1 := by rcases hcon with h | h <;> nlinarith
    have hz : deriv Real.smoothTransition (y^2 - 1) = 0 := deriv_smoothTransition_of_one_lt hy2
    exact hy (by rw [hz, mul_zero])
  have hint : IntegrableOn (fun y : ℝ => y * deriv Real.smoothTransition (y^2 - 1)) (Set.Ioi 0) :=
    (hcont.integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp)).integrableOn
  have hlim : Tendsto (fun y : ℝ => (1/2) * Real.smoothTransition (y^2 - 1)) atTop (𝓝 (1/2)) := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop (2:ℝ)] with y hy
    rw [Real.smoothTransition.one_of_one_le (by nlinarith)]
    ring
  rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim]
  rw [show (0:ℝ)^2 - 1 = -1 by norm_num,
    Real.smoothTransition.zero_of_nonpos (by norm_num : (-1:ℝ) ≤ 0), mul_zero, sub_zero]

/-- **The radial computation.**  The two-dimensional integral of the approximate
identity is `π`: in polar coordinates `∫_ℂ ψ'(‖x‖² - 1) dx = 2π ∫₀^∞ y ψ'(y² - 1) dy = π`. -/
theorem integral_radial_deriv_smoothTransition :
    ∫ x : ℂ, deriv Real.smoothTransition (‖x‖^2 - 1) = Real.pi := by
  have hball : (volume : Measure ℂ).real (Metric.ball (0:ℂ) 1) = Real.pi := by
    rw [Measure.real, Complex.volume_ball]
    norm_num
  rw [MeasureTheory.integral_fun_norm_addHaar (volume : Measure ℂ)
      (fun y : ℝ => deriv Real.smoothTransition (y^2 - 1))]
  rw [Complex.finrank_real_complex, hball]
  simp only [Nat.reduceSub, pow_one, smul_eq_mul]
  rw [integral_Ioi_mul_deriv_smoothTransition]
  ring

/-- The limit of the `∂̄`-derivative of the cutoff kernel: for a continuous compactly
supported `F`, `∫ u, F u * (deriv (cutProfile ε) (‖u‖²) : ℂ) → π * F 0` as `ε → 0⁺`. -/
theorem tendsto_cutProfile_deriv (F : ℂ → ℂ) (hF : Continuous F) (hFc : HasCompactSupport F) :
    Filter.Tendsto (fun ε : ℝ => ∫ u, F u * ((deriv (cutProfile ε) (‖u‖^2) : ℝ) : ℂ) ∂volume)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ((Real.pi : ℂ) * F 0)) := by
  -- the normalised approximate identity
  set φ : ℂ → ℝ := fun x => Real.pi⁻¹ * deriv Real.smoothTransition (‖x‖^2 - 1) with hφdef
  have hφ_nonneg : ∀ x, 0 ≤ φ x :=
    fun x => mul_nonneg (by positivity) (deriv_smoothTransition_nonneg _)
  have hφ_int : ∫ x, φ x ∂volume = 1 := by
    rw [hφdef, MeasureTheory.integral_const_mul, integral_radial_deriv_smoothTransition]
    rw [inv_mul_cancel₀ Real.pi_ne_zero]
  -- `φ` decays fast enough at infinity, being compactly supported
  have hφ_decay : Tendsto (fun x : ℂ => ‖x‖ ^ Module.finrank ℝ ℂ * φ x) (cobounded ℂ) (𝓝 0) := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨(Metric.closedBall (0:ℂ) 2)ᶜ,
      Metric.cobounded_le_cocompact (isCompact_closedBall 0 2).compl_mem_cocompact, ?_⟩
    intro x hx
    simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hx
    have hd : deriv Real.smoothTransition (‖x‖^2 - 1) = 0 :=
      deriv_smoothTransition_of_one_lt (by nlinarith [norm_nonneg x])
    simp [hφdef, hd]
  -- peak-function convergence of the rescaled family
  have hpeak := tendsto_integral_comp_smul_smul_of_integrable
    (F := ℂ) (E := ℂ) (μ := volume) (φ := φ) (g := F)
    hφ_nonneg hφ_int hφ_decay (hF.integrable_of_hasCompactSupport hFc) hF.continuousAt
  -- reparametrise `c = ε⁻¹`, so that `c → ∞` becomes `ε → 0⁺`
  have h1 : Tendsto (fun ε : ℝ => ∫ x, ((ε⁻¹) ^ 2 * φ (ε⁻¹ • x)) • F x)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (F 0)) := by
    have hinv : Tendsto (fun ε : ℝ => ε⁻¹) (nhdsWithin 0 (Set.Ioi 0)) atTop :=
      tendsto_inv_nhdsGT_zero
    have hcomp := hpeak.comp hinv
    have hcomp' : ((fun c : ℝ => ∫ x, (c ^ Module.finrank ℝ ℂ * φ (c • x)) • F x) ∘ fun ε : ℝ => ε⁻¹)
        = fun ε : ℝ => ∫ x, ((ε⁻¹) ^ 2 * φ (ε⁻¹ • x)) • F x := by
      funext ε
      simp only [Function.comp_apply, Complex.finrank_real_complex]
    rw [hcomp'] at hcomp
    exact hcomp
  have h2 : Tendsto (fun ε : ℝ => (Real.pi : ℂ) * ∫ x, ((ε⁻¹) ^ 2 * φ (ε⁻¹ • x)) • F x)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 ((Real.pi : ℂ) * F 0)) := h1.const_mul (Real.pi : ℂ)
  -- identify the integrands pointwise for `ε > 0`
  refine Filter.Tendsto.congr' ?_ h2
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hεpos : 0 < ε := hε
  have hεne : ε ≠ 0 := ne_of_gt hεpos
  rw [← MeasureTheory.integral_const_mul (Real.pi : ℂ)]
  apply integral_congr_ae
  filter_upwards with x
  have hnorm : ‖(ε⁻¹ : ℝ) • x‖^2 - 1 = ‖x‖^2 / ε^2 - 1 := by
    congr 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hεpos)]
    field_simp
  have hkey : Real.pi * ((ε⁻¹) ^ 2 * φ ((ε⁻¹ : ℝ) • x))
      = deriv Real.smoothTransition (‖x‖^2 / ε^2 - 1) / ε^2 := by
    rw [hφdef]
    simp only []
    rw [hnorm]
    field_simp
  rw [Complex.real_smul, deriv_cutProfile ε hεne (‖x‖^2)]
  have ha : (Real.pi : ℂ) * ((((ε⁻¹) ^ 2 * φ ((ε⁻¹ : ℝ) • x) : ℝ)) : ℂ)
      = ((deriv Real.smoothTransition (‖x‖^2 / ε^2 - 1) / ε^2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    exact congrArg (fun t : ℝ => (t : ℂ)) hkey
  rw [← mul_assoc, ha, mul_comm]

end Work.Beltrami
