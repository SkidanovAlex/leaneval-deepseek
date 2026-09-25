/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# Polar coordinates for the flat `∂_z`-operator

This file collects the polar-coordinate calculus needed for the `∂_z` Cauchy–Green identity
`∫_{‖w‖<ρ} (∂_z F)(w)/w = ∫_{‖w‖<ρ} (F w - F 0)/w²` (proved in
`Submission/Work/CR/Flat/Cauchy/integral_dzC_div_eq_integral_sub_div_sq.lean`).

Writing `ζ = Complex.polarCoord.symm p = p.1 · e^{i p.2}` and `u = polarUnit p.2 = e^{i p.2}`,
put `M(ρ,θ) = e^{-2iθ}(F(ρ e^{iθ}) - F 0) = u⁻² (F ζ - F 0)`.  The polar form of
`ρ · ∂_z((F - F 0)/w)(ζ)` is

  `(1/2) ∂_ρ M - (i/2) ∂_θ (M/ρ)
     = (1/2) u⁻² ∂_ρ(F ζ - F 0) - (i/2) u⁻² (∂_θ(F ζ - F 0) - 2 i (F ζ - F 0))/ρ`,

which is the sum of the two functions `polZ1 F p` and `polZ2 F p` defined below; these are the
integrands of the two fundamental-theorem-of-calculus steps in the proof of the main identity
(`∫ polZ1 = 0` by the `ρ`-FTC, `∫ polZ2 = 0` by the `θ`-FTC and periodicity).

The pointwise identity is `polar_dzC_diff`; the algebra behind it is `dzC_polar_algebra`,
the `∂_z`-analogue (with a sign flipped) of `polar_algebra` in `cauchyGreen_origin.lean`.
-/
import Mathlib
import Submission.Work.CR.Flat.Cauchy
import Submission.Work.CR.Flat.Cauchy.cauchyGreen_origin

noncomputable section

open scoped NNReal ENNReal Real Topology
open MeasureTheory Set

namespace Work.CR.Flat.Cauchy

/-! ## The polar integrands -/

/-- `M(ρ,θ) = e^{-2iθ}(F(ρ e^{iθ}) - F 0)`, the polar numerator of the `∂_z` Cauchy–Green
computation. -/
noncomputable def polM (F : ℂ → ℂ) (p : ℝ × ℝ) : ℂ :=
  (polarUnit p.2)⁻¹ * ((polarUnit p.2)⁻¹ * (F (Complex.polarCoord.symm p) - F 0))

/-- The `ρ`-part of the polar form of `ρ ∂_z((F - F 0)/w)`: `(1/2) e^{-2iθ} ∂_ρ(F(ρe^{iθ}) - F 0)`. -/
noncomputable def polZ1 (F : ℂ → ℂ) (p : ℝ × ℝ) : ℂ :=
  (1 / 2) * ((polarUnit p.2)⁻¹ * ((polarUnit p.2)⁻¹ * polA F p))

/-- The `θ`-part of the polar form of `ρ ∂_z((F - F 0)/w)`:
`-(i/2) e^{-2iθ} (∂_θ(F(ρe^{iθ}) - F 0) - 2 i (F(ρe^{iθ}) - F 0))/ρ`. -/
noncomputable def polZ2 (F : ℂ → ℂ) (p : ℝ × ℝ) : ℂ :=
  -((Complex.I / 2) * ((polarUnit p.2)⁻¹ * ((polarUnit p.2)⁻¹ *
      (polB F p - 2 * Complex.I * (F (Complex.polarCoord.symm p) - F 0)))) / (p.1 : ℂ))

/-! ## The algebra of the polar form of `∂_z` -/

/-- The algebraic kernel of the Cauchy–Green formula for `∂_z`:
`L u - i L (u i) = u (L 1 - i L i)` for `u = e^{iθ}` — the `∂_z`-analogue of `polar_algebra`,
with the sign of the `i` flipped. -/
lemma dzC_polar_algebra (L : ℂ →L[ℝ] ℂ) (θ : ℝ) :
    L (polarUnit θ) - Complex.I * L (polarUnit θ * Complex.I)
      = polarUnit θ * (L 1 - Complex.I * L Complex.I) := by
  have h2 : L (polarUnit θ * Complex.I)
      = -(Real.sin θ : ℂ) * L 1 + (Real.cos θ : ℂ) * L Complex.I := by
    rw [polarUnit_mul_I,
      show -(Real.sin θ : ℂ) = (((-(Real.sin θ)) : ℝ) : ℂ) by push_cast; ring]
    exact apply_real_decomp L (-(Real.sin θ)) (Real.cos θ)
  rw [h2, polarUnit_apply, apply_real_decomp L (Real.cos θ) (Real.sin θ)]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The pointwise relation between `ρ ∂_z F(ρ e^{iθ})` and the polar partial derivatives
of `F`: `ρ (∂_z F)(ζ) = (1/2) u⁻¹ (ρ polA F p - i polB F p)`. -/
lemma polar_dzC_mul {F : ℂ → ℂ} (p : ℝ × ℝ) :
    (p.1 : ℂ) * dzC F (Complex.polarCoord.symm p)
      = (1 / 2) * (polarUnit p.2)⁻¹ *
          ((p.1 : ℂ) * polA F p - Complex.I * polB F p) := by
  have hu : polarUnit p.2 ≠ 0 := by
    intro h; have := norm_polarUnit p.2; rw [h] at this; simp at this
  have hL : (p.1 : ℂ) * polA F p - Complex.I * polB F p
      = (p.1 : ℂ) * ((fderiv ℝ F (Complex.polarCoord.symm p)) (polarUnit p.2)
          - Complex.I * (fderiv ℝ F (Complex.polarCoord.symm p)) (polarUnit p.2 * Complex.I)) := by
    rw [polA, polB,
      show ((p.1 : ℂ) * (polarUnit p.2 * Complex.I))
          = (p.1 : ℝ) • (polarUnit p.2 * Complex.I) by rw [Complex.real_smul],
      map_smul, Complex.real_smul]
    ring
  rw [hL, dzC_polar_algebra (fderiv ℝ F (Complex.polarCoord.symm p)) p.2, dzC]
  field_simp

/-- Pure algebra: the polar form of `ρ ∂_z G` for `G = (F - F 0)/w`, with `ζ = ρ u`. -/
lemma dzC_diff_polar_algebra (u : ℂ) (ρ : ℝ) (a b Ψ : ℂ) (hu : u ≠ 0) (hρ : (ρ : ℂ) ≠ 0) :
    (1 / 2) * u⁻¹ * ((ρ : ℂ) * a - Complex.I * b) / ((ρ : ℂ) * u)
        - (ρ : ℂ) * Ψ / ((ρ : ℂ) * u) ^ 2
      = (1 / 2) * (u⁻¹ * (u⁻¹ * a))
        - (Complex.I / 2) * (u⁻¹ * (u⁻¹ * (b - 2 * Complex.I * Ψ))) / (ρ : ℂ) := by
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **The pointwise polar identity.**  On the disc (`0 < p.1`) the polar integrand
`p.1 · (∂_zF(ζ)/ζ - (F ζ - F 0)/ζ²)` is `polZ1 F p + polZ2 F p`. -/
lemma polar_dzC_diff {F : ℂ → ℂ} (p : ℝ × ℝ) (hp : 0 < p.1) :
    (p.1 : ℂ) * (dzC F (Complex.polarCoord.symm p) / Complex.polarCoord.symm p
        - (F (Complex.polarCoord.symm p) - F 0) / Complex.polarCoord.symm p ^ 2)
      = polZ1 F p + polZ2 F p := by
  have hρ : (p.1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hp)
  have hu : polarUnit p.2 ≠ 0 := by
    intro h; have := norm_polarUnit p.2; rw [h] at this; simp at this
  rw [mul_sub, ← mul_div_assoc, ← mul_div_assoc, polar_dzC_mul p, polZ1, polZ2,
    polarCoord_symm_eq p]
  exact dzC_diff_polar_algebra (polarUnit p.2) p.1 (polA F p) (polB F p)
    (F ((p.1 : ℂ) * polarUnit p.2) - F 0) hu hρ

/-! ## The two one-variable differentiation steps -/

lemma hasDerivAt_polarUnit_inv (θ : ℝ) :
    HasDerivAt (fun θ : ℝ => (polarUnit θ)⁻¹) (-Complex.I * (polarUnit θ)⁻¹) θ := by
  have hu : polarUnit θ ≠ 0 := by
    intro h; have := norm_polarUnit θ; rw [h] at this; simp at this
  have h := (hasDerivAt_polarUnit θ).inv hu
  convert h using 1
  field_simp

lemma hasDerivAt_polarUnit_inv_sq (θ : ℝ) :
    HasDerivAt (fun θ : ℝ => (polarUnit θ)⁻¹ * (polarUnit θ)⁻¹)
      (-2 * Complex.I * ((polarUnit θ)⁻¹ * (polarUnit θ)⁻¹)) θ := by
  have h := (hasDerivAt_polarUnit_inv θ).mul (hasDerivAt_polarUnit_inv θ)
  convert h using 1
  ring

/-- `∫_{-π}^{π} e^{-2iθ} dθ = 0`. -/
lemma integral_polarUnit_inv_sq :
    ∫ θ in (-Real.pi)..Real.pi, (polarUnit θ)⁻¹ * (polarUnit θ)⁻¹ = 0 := by
  have hderiv : ∀ θ ∈ uIcc (-Real.pi) Real.pi,
      HasDerivAt (fun θ : ℝ => (Complex.I / 2) * ((polarUnit θ)⁻¹ * (polarUnit θ)⁻¹))
        ((polarUnit θ)⁻¹ * (polarUnit θ)⁻¹) θ := by
    intro θ _
    have h := (hasDerivAt_polarUnit_inv_sq θ).const_mul (Complex.I / 2)
    convert h using 1
    ring_nf
    rw [Complex.I_sq]
    ring
  have hcont : Continuous (fun θ : ℝ => (polarUnit θ)⁻¹ * (polarUnit θ)⁻¹) := by
    rw [show (fun θ : ℝ => (polarUnit θ)⁻¹ * (polarUnit θ)⁻¹)
        = fun θ : ℝ => polarUnit (-θ) * polarUnit (-θ) by
      funext θ; rw [polarUnit_neg]]
    exact (continuous_polarUnit.comp continuous_neg).mul
      (continuous_polarUnit.comp continuous_neg)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _)]
  rw [polarUnit_pi, polarUnit_neg_pi]
  ring

/-- The `ρ`-derivative of `M`: `∂_ρ M = e^{-2iθ} ∂_ρ(F(ρe^{iθ}) - F 0)`. -/
lemma hasDerivAt_polM_rho {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F) (p : ℝ × ℝ) :
    HasDerivAt (fun ρ : ℝ => polM F (ρ, p.2))
      ((polarUnit p.2)⁻¹ * ((polarUnit p.2)⁻¹ * polA F p)) p.1 := by
  have h1 : HasDerivAt (fun ρ : ℝ => F (Complex.polarCoord.symm (ρ, p.2)) - F 0)
      (polA F p) p.1 := (hasDerivAt_rho hF p).sub_const (F 0)
  have h2 := (h1.const_mul (polarUnit p.2)⁻¹).const_mul (polarUnit p.2)⁻¹
  simpa only [polM] using h2

/-- The `θ`-derivative of `M`:
`∂_θ M = e^{-2iθ} (∂_θ(F(ρe^{iθ}) - F 0) - 2 i (F(ρe^{iθ}) - F 0))`. -/
lemma hasDerivAt_polM_theta {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F) (p : ℝ × ℝ) :
    HasDerivAt (fun θ : ℝ => polM F (p.1, θ))
      ((polarUnit p.2)⁻¹ * ((polarUnit p.2)⁻¹ *
        (polB F p - 2 * Complex.I * (F (Complex.polarCoord.symm p) - F 0)))) p.2 := by
  have h1 : HasDerivAt (fun θ : ℝ => F (Complex.polarCoord.symm (p.1, θ)) - F 0)
      (polB F p) p.2 := (hasDerivAt_theta hF p).sub_const (F 0)
  have h2 := (hasDerivAt_polarUnit_inv_sq p.2).mul h1
  have h3 : (fun θ : ℝ => (polarUnit θ)⁻¹ * (polarUnit θ)⁻¹) *
      (fun θ : ℝ => F (Complex.polarCoord.symm (p.1, θ)) - F 0)
      = fun θ : ℝ => polM F (p.1, θ) := by
    funext θ
    simp only [Pi.mul_apply, polM]
    ring
  rw [h3] at h2
  convert h2 using 1
  ring_nf

/-- `θ ↦ M(ρ,θ)` is `2π`-periodic: its values at `θ = ±π` agree (both equal `ρ`-times the value
of `F` at the point `-ρ`). -/
lemma polM_pi (F : ℂ → ℂ) (ρ : ℝ) : polM F (ρ, Real.pi) = polM F (ρ, -Real.pi) := by
  rw [polM, polM, polarUnit_pi, polarUnit_neg_pi, polarCoord_symm_pi]

/-! ## Continuity, measurability and the elementary bounds -/

lemma continuous_polarUnit_inv_sq :
    Continuous (fun θ : ℝ => (polarUnit θ)⁻¹ * (polarUnit θ)⁻¹) := by
  rw [show (fun θ : ℝ => (polarUnit θ)⁻¹ * (polarUnit θ)⁻¹)
      = fun θ : ℝ => polarUnit (-θ) * polarUnit (-θ) by
    funext θ; rw [polarUnit_neg]]
  exact (continuous_polarUnit.comp continuous_neg).mul
    (continuous_polarUnit.comp continuous_neg)

lemma continuous_polZ1 {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F) : Continuous (polZ1 F) := by
  rw [show polZ1 F = fun p : ℝ × ℝ =>
      (1/2 : ℂ) * (((polarUnit p.2)⁻¹ * (polarUnit p.2)⁻¹) * polA F p) by
    funext p; rw [polZ1]; ring]
  exact continuous_const.mul ((continuous_polarUnit_inv_sq.comp continuous_snd).mul
    (continuous_polA hF))

lemma measurable_polZ2 {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F) : Measurable (polZ2 F) := by
  have hp : Measurable (fun p : ℝ × ℝ => (polarUnit p.2)⁻¹) := by
    rw [show (fun p : ℝ × ℝ => (polarUnit p.2)⁻¹) = fun p : ℝ × ℝ => polarUnit (-p.2) by
      funext p; rw [polarUnit_neg]]
    exact continuous_polarUnit.measurable.comp (measurable_snd.neg)
  have h1 : Measurable (fun p : ℝ × ℝ =>
      (polarUnit p.2)⁻¹ * ((polarUnit p.2)⁻¹ *
        (polB F p - 2 * Complex.I * (F (Complex.polarCoord.symm p) - F 0)))) := by
    refine hp.mul (hp.mul ?_)
    refine ((continuous_polB hF).measurable).sub ?_
    exact measurable_const.mul (hF.continuous.measurable.comp
      continuous_polarCoord_symm.measurable |>.sub measurable_const)
  have h2 : Measurable (fun p : ℝ × ℝ => (p.1 : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp measurable_fst
  exact ((measurable_const.mul h1).div h2).neg

/-- A `C¹` function supported in the closed ball of radius `ρ` has bounded differential; the
bound is global because the differential vanishes off the compact ball. -/
lemma exists_norm_fderiv_le_of_supported {ρ : ℝ} {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F)
    (hsupp : SupportedInBall ρ F) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ z : ℂ, ‖fderiv ℝ F z‖ ≤ Λ := by
  have hcont : Continuous fun z : ℂ => ‖fderiv ℝ F z‖ :=
    (hF.continuous_fderiv (by norm_num)).norm
  have hzero : ∀ z : ℂ, ρ < ‖z‖ → fderiv ℝ F z = 0 := by
    intro z hz
    have hε : 0 < ‖z‖ - ρ := by linarith
    have hev : F =ᶠ[nhds z] (fun _ : ℂ => (0 : ℂ)) := by
      filter_upwards [Metric.ball_mem_nhds z hε] with w hw
      rw [Metric.mem_ball, dist_eq_norm] at hw
      refine hsupp w ?_
      have h1 : ‖z‖ ≤ ‖w‖ + ‖z - w‖ := by
        have := norm_add_le w (z - w)
        simpa using this
      have h2 : ‖z - w‖ = ‖w - z‖ := norm_sub_rev z w
      linarith [hw]
    rw [hev.fderiv_eq]
    simp
  obtain ⟨Λ₀, hΛ₀⟩ :=
    (isCompact_closedBall (0 : ℂ) ρ).bddAbove_image hcont.continuousOn
  refine ⟨max Λ₀ 0, le_max_right _ _, fun z => ?_⟩
  by_cases hz : ‖z‖ ≤ ρ
  · have hzmem : z ∈ Metric.closedBall (0 : ℂ) ρ := by
      rw [Metric.mem_closedBall, dist_zero_right]; exact hz
    exact (hΛ₀ (Set.mem_image_of_mem _ hzmem)).trans (le_max_left _ _)
  · rw [hzero z (not_le.mp hz), norm_zero]
    exact le_max_right Λ₀ 0

/-- Mean value inequality on the segment `[0,z]`: `‖F z - F 0‖ ≤ Λ ‖z‖` when `‖(dF)_x‖ ≤ Λ`
everywhere. -/
lemma norm_sub_zero_le {Λ : ℝ} {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F)
    (hΛ : ∀ z : ℂ, ‖fderiv ℝ F z‖ ≤ Λ) (z : ℂ) :
    ‖F z - F 0‖ ≤ Λ * ‖z‖ := by
  have hdiff : ∀ x ∈ Metric.closedBall (0 : ℂ) ‖z‖, DifferentiableAt ℝ F x :=
    fun x _ => hF.differentiable_one x
  have hbound : ∀ x ∈ Metric.closedBall (0 : ℂ) ‖z‖, ‖fderiv ℝ F x‖ ≤ Λ :=
    fun x _ => hΛ x
  have h0 : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) ‖z‖ := by simp
  have hz : z ∈ Metric.closedBall (0 : ℂ) ‖z‖ := by
    rw [Metric.mem_closedBall, dist_zero_right]
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) hdiff hbound
    (convex_closedBall (0 : ℂ) ‖z‖) h0 hz
  simpa using this

/-- Pointwise bound on the angular polar integrand: `‖polZ2 F p‖ ≤ 3 Λ/2` on the disc, where
`Λ` bounds `‖fderiv ℝ F‖`. -/
lemma norm_polZ2_le {Λ : ℝ} {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F)
    (hΛ : ∀ z : ℂ, ‖fderiv ℝ F z‖ ≤ Λ) {p : ℝ × ℝ} (hp1 : 0 < p.1) :
    ‖polZ2 F p‖ ≤ 3 / 2 * Λ := by
  have hζ : ‖Complex.polarCoord.symm p‖ = p.1 := by
    rw [Complex.norm_polarCoord_symm, abs_of_pos hp1]
  have hu : ‖polarUnit p.2‖ = 1 := norm_polarUnit p.2
  have hu2 : ‖(polarUnit p.2)⁻¹ * (polarUnit p.2)⁻¹‖ = 1 := by
    rw [norm_mul, norm_inv, hu]; norm_num
  have hprod : ‖(p.1 : ℂ) * (polarUnit p.2 * Complex.I)‖ = p.1 := by
    rw [norm_mul, norm_mul, hu, Complex.norm_I, mul_one, mul_one]
    simp [hp1.le]
  have hpolB : ‖polB F p‖ ≤ Λ * p.1 := by
    rw [polB]
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    rw [hprod]
    exact mul_le_mul_of_nonneg_right (hΛ _) hp1.le
  have hΨ : ‖F (Complex.polarCoord.symm p) - F 0‖ ≤ Λ * p.1 := by
    have h := norm_sub_zero_le hF hΛ (Complex.polarCoord.symm p)
    rwa [hζ] at h
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  have hnum : ‖(polarUnit p.2)⁻¹ * ((polarUnit p.2)⁻¹ *
      (polB F p - 2 * Complex.I * (F (Complex.polarCoord.symm p) - F 0)))‖ ≤ 3 * (Λ * p.1) := by
    rw [← mul_assoc, norm_mul, hu2, one_mul]
    calc ‖polB F p - 2 * Complex.I * (F (Complex.polarCoord.symm p) - F 0)‖
        ≤ ‖polB F p‖ + ‖2 * Complex.I * (F (Complex.polarCoord.symm p) - F 0)‖ :=
          norm_sub_le _ _
      _ ≤ Λ * p.1 + 2 * (Λ * p.1) := by
          refine add_le_add hpolB ?_
          rw [norm_mul, norm_mul, h2, Complex.norm_I, mul_one]
          exact mul_le_mul_of_nonneg_left hΨ (by norm_num)
      _ = 3 * (Λ * p.1) := by ring
  calc ‖polZ2 F p‖
      = ‖Complex.I / 2‖ * ‖(polarUnit p.2)⁻¹ * ((polarUnit p.2)⁻¹ *
          (polB F p - 2 * Complex.I * (F (Complex.polarCoord.symm p) - F 0)))‖ / ‖(p.1 : ℂ)‖ := by
        rw [polZ2, norm_neg, norm_div, norm_mul]
    _ ≤ ‖Complex.I / 2‖ * (3 * (Λ * p.1)) / ‖(p.1 : ℂ)‖ := by
        gcongr
    _ = 3 / 2 * Λ := by
        rw [show ‖Complex.I / 2‖ = 1/2 by norm_num,
          show ‖(p.1 : ℂ)‖ = p.1 by simp [hp1.le]]
        field_simp

/-! ## Integrability on the disc `(0,ρ) × (-π,π)` -/

lemma integrableOn_polZ1 {ρ : ℝ} {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F) :
    IntegrableOn (polZ1 F) (Ioo 0 ρ ×ˢ Ioo (-Real.pi) Real.pi) (volume.prod volume) := by
  rw [← Measure.volume_eq_prod ℝ ℝ]
  exact integrableOn_Ioo_prod_of_continuous (continuous_polZ1 hF) 0 ρ (-Real.pi) Real.pi

lemma integrableOn_polZ2 {ρ : ℝ} {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F)
    (hsupp : SupportedInBall ρ F) :
    IntegrableOn (polZ2 F) (Ioo 0 ρ ×ˢ Ioo (-Real.pi) Real.pi) (volume.prod volume) := by
  obtain ⟨Λ, _, hΛ⟩ := exists_norm_fderiv_le_of_supported hF hsupp
  refine MeasureTheory.IntegrableOn.of_bound ?_ (measurable_polZ2 hF).aestronglyMeasurable
    (3 / 2 * Λ) ?_
  · rw [Measure.prod_prod]
    exact ENNReal.mul_lt_top (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top)
      (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top)
  · rw [MeasureTheory.ae_restrict_iff' (measurableSet_Ioo.prod measurableSet_Ioo)]
    exact Filter.Eventually.of_forall (fun p hp => norm_polZ2_le hF hΛ hp.1.1)

end Work.CR.Flat.Cauchy
