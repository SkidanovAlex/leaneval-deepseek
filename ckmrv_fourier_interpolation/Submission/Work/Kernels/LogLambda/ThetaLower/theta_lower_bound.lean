import Mathlib
import Submission.Work.Kernels.LogLambda.ThetaLaws
import Submission.Work.Kernels.ClassicalFacts.theta00Fun_mem_InP
import Submission.Work.Kernels.ClassicalFacts.theta01Fun_mem_InP
import Submission.Work.Kernels.LogLambda.ThetaLower.theta_smul_SL2
import Submission.Work.Kernels.LogLambda.ThetaLower.ratio_estimate

noncomputable section

open UpperHalfPlane ModularGroup Matrix
open scoped MatrixGroups

namespace Work.Kernels.LogLambda.ThetaLower

/-! ## Lower bounds on the region `im ξ ≥ 1/2`

The three Jacobi theta functions do not vanish on `ℍ`, but two of them vanish at cusps, so a
uniform lower bound on all of `ℍ` is false.  On the region `im ξ ≥ 1/2`, however, the defining
series give explicit lower bounds: `‖θ₀₀‖, ‖θ₀₁‖ ≥ 1/8` and `‖θ₁₀ ξ‖ ≥ (1/8) exp (-π im ξ / 4)`
(`θ₁₀` decays exponentially at the cusp `i∞`, and the exponential rate `π/4` is sharp). -/

/-- `‖θ₀₀ z‖ = ‖jacobiTheta z‖ ≥ 1/8` for `im z ≥ 1/2`.  Indeed
`‖jacobiTheta z - 1‖ ≤ 2 e^{-π y}/(1 - e^{-π y}) ≤ 7/8` when `π y ≥ 3/2`. -/
lemma jacobiTheta_lower_region (z : ℂ) (hz : (1 / 2 : ℝ) ≤ z.im) :
    (1 / 8 : ℝ) ≤ ‖jacobiTheta z‖ := by
  have hzpos : 0 < z.im := lt_of_lt_of_le (by norm_num) hz
  have h3 : (23 : ℝ) / 7 ≤ Real.exp (3 / 2) := by
    have h := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 3 / 2 by norm_num)
    nlinarith
  have hu : (3 : ℝ) / 2 ≤ Real.pi * z.im := by nlinarith [Real.pi_gt_three, hz]
  have hEu : (23 : ℝ) / 7 ≤ Real.exp (Real.pi * z.im) := h3.trans (Real.exp_le_exp.mpr hu)
  have he : Real.exp (-Real.pi * z.im) ≤ 7 / 23 := by
    rw [show -Real.pi * z.im = -(Real.pi * z.im) by ring, Real.exp_neg]
    have h := one_div_le_one_div_of_le (show (0 : ℝ) < (23 : ℝ) / 7 by norm_num) hEu
    rw [one_div, one_div, show (((23 : ℝ) / 7)⁻¹) = 7 / 23 from by norm_num] at h
    exact h
  have hlt1 : Real.exp (-Real.pi * z.im) < 1 := by
    rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos, hzpos]
  have hden : 0 < 1 - Real.exp (-Real.pi * z.im) := by linarith
  have htail : 2 / (1 - Real.exp (-Real.pi * z.im)) * Real.exp (-Real.pi * z.im) ≤ 7 / 8 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hden]
    nlinarith
  have hb : ‖jacobiTheta z - 1‖ ≤ 7 / 8 :=
    (norm_jacobiTheta_sub_one_le (τ := z) hzpos).trans htail
  have htri : (1 : ℝ) ≤ ‖jacobiTheta z‖ + ‖jacobiTheta z - 1‖ := by
    have := norm_sub_le (jacobiTheta z) (jacobiTheta z - 1)
    simpa using this
  linarith

/-- `‖θ₀₀ ξ‖ ≥ 1/8` for `im ξ ≥ 1/2`. -/
lemma theta00_region_lower (ξ : ℍ) (hξ : (1 / 2 : ℝ) ≤ ξ.im) :
    (1 / 8 : ℝ) ≤ ‖Work.Kernels.theta00Fun ξ‖ := by
  simpa only [Work.Kernels.theta00Fun] using jacobiTheta_lower_region (ξ : ℂ) (by simpa using hξ)

/-- `‖θ₀₁ ξ‖ ≥ 1/8` for `im ξ ≥ 1/2`: `θ₀₁ ξ = θ₀₀ (ξ + 1)`. -/
lemma theta01_region_lower (ξ : ℍ) (hξ : (1 / 2 : ℝ) ≤ ξ.im) :
    (1 / 8 : ℝ) ≤ ‖Work.Kernels.theta01Fun ξ‖ := by
  have h : Work.Kernels.theta01Fun ξ = jacobiTheta ((ξ : ℂ) + 1) :=
    Work.Kernels.ClassicalFacts.jacobiTheta₂_half_eq_jacobiTheta_add_one (ξ : ℂ)
  rw [h]
  exact jacobiTheta_lower_region _ (by simpa using hξ)

/-- `‖θ₁₀ ξ‖ ≥ (1/8) exp (-π im ξ / 4)` for `im ξ ≥ 1/2`.

The prefactor `exp (π i ξ / 4)` has norm `exp (-π im ξ / 4)`, and the remaining factor
`jacobiTheta₂ (ξ/2) ξ = 2 (1 + ∑_{k≥1} exp (π i ξ (k² + k)))` has norm at least `1/4` by
`ratio_estimate`. -/
lemma theta10_region_lower (ξ : ℍ) (hξ : (1 / 2 : ℝ) ≤ ξ.im) :
    (1 / 8 : ℝ) * Real.exp (-(Real.pi * ξ.im / 4)) ≤ ‖Work.Kernels.theta10Fun ξ‖ := by
  have hzpos : 0 < ξ.im := lt_of_lt_of_le (by norm_num) hξ
  have hpre : ‖Complex.exp (Real.pi * Complex.I * (ξ : ℂ) / 4)‖
      = Real.exp (-(Real.pi * ξ.im / 4)) := by
    rw [Complex.norm_exp]
    congr 1
    have h : Real.pi * Complex.I * (ξ : ℂ) / 4
        = ((Real.pi / 4 : ℝ) : ℂ) * (Complex.I * (ξ : ℂ)) := by push_cast; ring
    rw [h, Complex.re_ofReal_mul, Complex.I_mul_re, UpperHalfPlane.coe_im]
    ring
  have hA : (1 / 4 : ℝ) ≤ ‖jacobiTheta₂ ((ξ : ℂ) / 2) (ξ : ℂ)‖ := by
    have hr := ratio_estimate (ξ : ℂ) hzpos
    have h2 : (3 : ℝ) ≤ 2 * Real.pi * (ξ : ℂ).im := by
      rw [UpperHalfPlane.coe_im]; nlinarith [Real.pi_gt_three, hξ]
    have hexp3 : (8 : ℝ) ≤ Real.exp 3 := by
      have h := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 3 by norm_num)
      nlinarith
    have h8 : Real.exp (-(2 * Real.pi * (ξ : ℂ).im)) ≤ 1 / 8 := by
      have hmono : Real.exp (-(2 * Real.pi * (ξ : ℂ).im)) ≤ Real.exp (-3) :=
        Real.exp_le_exp.mpr (by linarith)
      have h3e : Real.exp (-3) = 1 / Real.exp 3 := by rw [Real.exp_neg]; ring
      calc Real.exp (-(2 * Real.pi * (ξ : ℂ).im)) ≤ Real.exp (-3) := hmono
        _ = 1 / Real.exp 3 := h3e
        _ ≤ 1 / 8 := one_div_le_one_div_of_le (by norm_num) hexp3
    have hlt1 : Real.exp (-(2 * Real.pi * (ξ : ℂ).im)) < 1 := by
      rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos, hzpos]
    have hden : 0 < 1 - Real.exp (-(2 * Real.pi * (ξ : ℂ).im)) := by linarith
    have hratio : Real.exp (-(2 * Real.pi * (ξ : ℂ).im)) / (1 - Real.exp (-(2 * Real.pi * (ξ : ℂ).im)))
        ≤ 7 / 8 := by
      rw [div_le_iff₀ hden]; nlinarith
    have htri : (1 : ℝ) ≤ ‖jacobiTheta₂ ((ξ : ℂ) / 2) (ξ : ℂ) / 2‖
        + ‖jacobiTheta₂ ((ξ : ℂ) / 2) (ξ : ℂ) / 2 - 1‖ := by
      have := norm_sub_le (jacobiTheta₂ ((ξ : ℂ) / 2) (ξ : ℂ) / 2)
        (jacobiTheta₂ ((ξ : ℂ) / 2) (ξ : ℂ) / 2 - 1)
      simpa using this
    have hhalf : (1 / 8 : ℝ) ≤ ‖jacobiTheta₂ ((ξ : ℂ) / 2) (ξ : ℂ) / 2‖ := by
      have := hr.trans hratio
      linarith
    have h2' : ‖jacobiTheta₂ ((ξ : ℂ) / 2) (ξ : ℂ) / 2‖
        = ‖jacobiTheta₂ ((ξ : ℂ) / 2) (ξ : ℂ)‖ / 2 := by
      rw [norm_div]; simp
    rw [h2'] at hhalf
    linarith
  have htheta : ‖Work.Kernels.theta10Fun ξ‖
      = Real.exp (-(Real.pi * ξ.im / 4)) * ‖jacobiTheta₂ ((ξ : ℂ) / 2) (ξ : ℂ)‖ := by
    simp only [Work.Kernels.theta10Fun]
    rw [norm_mul, hpre]
  rw [htheta]
  have he : 0 < Real.exp (-(Real.pi * ξ.im / 4)) := Real.exp_pos _
  nlinarith

/-- The uniform lower bound on the region `im ξ ≥ 1/2` for all three coordinates. -/
lemma region_lower (ξ : ℍ) (hξ : (1 / 2 : ℝ) ≤ ξ.im) (j : Fin 3) :
    (1 / 8 : ℝ) * Real.exp (-(Real.pi * ξ.im / 4)) ≤ ‖Work.Kernels.thetaVec j ξ‖ := by
  have hexp_le_one : Real.exp (-(Real.pi * ξ.im / 4)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos, ξ.im_pos]
  have hsmall : (1 / 8 : ℝ) * Real.exp (-(Real.pi * ξ.im / 4)) ≤ 1 / 8 := by
    calc (1 / 8 : ℝ) * Real.exp (-(Real.pi * ξ.im / 4)) ≤ (1 / 8) * 1 :=
          mul_le_mul_of_nonneg_left hexp_le_one (by norm_num)
      _ = 1 / 8 := by ring
  have hj : j = 0 ∨ j = 1 ∨ j = 2 := by fin_cases j <;> simp
  rcases hj with rfl | rfl | rfl
  · rw [Work.Kernels.thetaVec_zero]
    exact hsmall.trans (theta00_region_lower ξ hξ)
  · rw [Work.Kernels.thetaVec_one]
    exact hsmall.trans (theta01_region_lower ξ hξ)
  · rw [Work.Kernels.thetaVec_two]
    exact theta10_region_lower ξ hξ

/-! ## Transfer of the bound from a `SL(2,ℤ)`-translate -/

/-- If `‖j(γ,τ)‖ ≤ 1` then the `j`-th component of the theta vector at `τ` dominates some
component of the theta vector at `γ • τ`.  This is `theta_smul_SL2` together with
`‖j(γ,τ)‖^{1/2} ≤ 1`. -/
lemma thetaVec_transfer (γ : SL(2, ℤ)) (τ : ℍ) (h : ‖Work.Kernels.jFun γ (τ : ℂ)‖ ≤ 1)
    (j : Fin 3) :
    ∃ k : Fin 3, ‖Work.Kernels.thetaVec k (γ • τ)‖ ≤ ‖Work.Kernels.thetaVec j τ‖ := by
  obtain ⟨σ, hσ⟩ := theta_smul_SL2 γ
  refine ⟨σ j, ?_⟩
  rw [hσ τ j]
  exact mul_le_of_le_one_left (norm_nonneg _) (Real.rpow_le_one (norm_nonneg _) h (by norm_num))

/-! ## The imaginary part of a translate -/

/-- `(γ • τ).im ≤ max τ.im (im τ)⁻¹` for every `γ ∈ SL(2,ℤ)`. -/
lemma im_smul_le_max (γ : SL(2, ℤ)) (τ : ℍ) :
    (γ • τ).im ≤ max τ.im (τ.im)⁻¹ := by
  rw [ModularGroup.im_smul_eq_div_normSq, ModularGroup.denom_apply]
  by_cases hc : γ 1 0 = 0
  · -- `c = 0`: then `(γ • τ).im = τ.im / d²` with `d` a nonzero integer, so `d² ≥ 1`.
    have hd : γ 1 1 ≠ 0 := fun h' => zero_ne_one <| by
      simpa only [Matrix.det_fin_two, hc, h', mul_zero, mul_zero, sub_zero] using γ.det_coe
    have h1 : (1 : ℝ) ≤ (γ 1 1) ^ 2 :=
      mod_cast (one_le_sq_iff_one_le_abs _).mpr (Int.one_le_abs hd)
    refine le_trans ?_ (le_max_left _ _)
    rw [show Complex.normSq ((γ 1 0) * τ + (γ 1 1)) = (γ 1 1) ^ 2 by simp [hc, sq]]
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < (γ 1 1) ^ 2)]
    nlinarith [τ.im_pos.le]
  · -- `c ≠ 0`: `normSq ≥ (c im τ)² ≥ (im τ)²`, so `(γ • τ).im ≤ (im τ)⁻¹`.
    refine le_trans ?_ (le_max_right _ _)
    rw [show (τ.im)⁻¹ = τ.im / τ.im ^ 2 by field_simp]
    gcongr
    rw [show Complex.normSq ((γ 1 0) * τ + (γ 1 1)) =
        ((γ 1 0) * τ.re + (γ 1 1)) ^ 2 + (γ 1 0) ^ 2 * τ.im ^ 2 by
      simp [Complex.normSq_apply]; ring]
    have hc2 : (1 : ℝ) ≤ (γ 1 0) ^ 2 :=
      mod_cast (one_le_sq_iff_one_le_abs _).mpr (Int.one_le_abs hc)
    nlinarith [sq_nonneg ((γ 1 0) * τ.re + (γ 1 1)), τ.im_pos.le]

/-- `(γ • τ).im ≤ 1 + (im τ)⁻¹ + ‖τ‖`. -/
lemma im_smul_le_M (γ : SL(2, ℤ)) (τ : ℍ) :
    (γ • τ).im ≤ 1 + (τ.im)⁻¹ + ‖(τ : ℂ)‖ := by
  refine (im_smul_le_max γ τ).trans ?_
  refine max_le ?_ ?_
  · calc τ.im = ((τ : ℂ)).im := (UpperHalfPlane.coe_im τ).symm
      _ ≤ ‖(τ : ℂ)‖ := Complex.im_le_norm _
      _ ≤ 1 + (τ.im)⁻¹ + ‖(τ : ℂ)‖ := by
          have := inv_pos.mpr τ.im_pos; linarith
  · linarith [norm_nonneg (τ : ℂ)]

/-! ## The main theorem -/

theorem theta_lower_bound : ∃ C : ℝ, 0 < C ∧ ∀ (τ : UpperHalfPlane) (j : Fin 3),
    Real.exp (-(C * (1 + (τ.im)⁻¹ + ‖(τ : ℂ)‖))) ≤ ‖Work.Kernels.thetaVec j τ‖ := by
  refine ⟨Real.pi / 4 + Real.log 8 + 1, by positivity, ?_⟩
  intro τ j
  obtain ⟨γ, hγim, hγnorm⟩ := ModularGroup.exists_one_half_le_im_smul_and_norm_denom_le τ
  have hnorm : ‖Work.Kernels.jFun γ (τ : ℂ)‖ ≤ 1 := hγnorm
  obtain ⟨k, hk⟩ := thetaVec_transfer γ τ hnorm j
  have hreg := region_lower (γ • τ) hγim k
  set M : ℝ := 1 + (τ.im)⁻¹ + ‖(τ : ℂ)‖ with hM
  have hM1 : 1 ≤ M := by
    rw [hM]; have := inv_pos.mpr τ.im_pos; linarith [norm_nonneg (τ : ℂ)]
  have hlog : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
  have hexp8 : Real.exp (-(Real.log 8)) = 1 / 8 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have himle : (γ • τ).im ≤ M := im_smul_le_M γ τ
  calc Real.exp (-((Real.pi / 4 + Real.log 8 + 1) * M))
      ≤ Real.exp (-(Real.pi / 4 * M + Real.log 8)) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_nonneg hlog (by linarith : (0 : ℝ) ≤ M - 1)]
    _ = (1 / 8 : ℝ) * Real.exp (-(Real.pi / 4 * M)) := by
        rw [show -(Real.pi / 4 * M + Real.log 8) = -(Real.pi / 4 * M) + (-(Real.log 8)) by ring,
          Real.exp_add, hexp8]
        ring
    _ ≤ (1 / 8 : ℝ) * Real.exp (-(Real.pi * (γ • τ).im / 4)) := by
        have h : Real.exp (-(Real.pi / 4 * M)) ≤ Real.exp (-(Real.pi * (γ • τ).im / 4)) := by
          apply Real.exp_le_exp.mpr
          nlinarith [himle, Real.pi_pos]
        exact mul_le_mul_of_nonneg_left h (by norm_num)
    _ ≤ ‖Work.Kernels.thetaVec k (γ • τ)‖ := hreg
    _ ≤ ‖Work.Kernels.thetaVec j τ‖ := hk

end Work.Kernels.LogLambda.ThetaLower
