/-
# The `z`-bounds for `K_-` at the threshold `Im z ≥ 1/3`

This file proves `Work.Asymptotics.KMinusFunnelZBounds`, the bound on the `z`-atoms

  `E₈V`, `E₆(U² - W²)`, `V`, `jV`, `(E₁₀/Δ)(U² - W²)`

on the region `{Im z ≥ 1/3}`.  It is the `z`-part of the control of the `K_-` funnel
tails for `d = 8` and `d = 24`.

The two nontrivial inputs are the vanishing at the cusp `i∞` of `V = θ₁₀⁴ = θ₂⁴` and of
`U² - W²`:

* `θ₃ - 1 = O(e^{-π Im z})` and `θ₄ - 1 = O(e^{-π Im z})` — Mathlib's
  `norm_jacobiTheta_sub_one_le`, applied at `z` and at `z + 1` (since `θ₄(τ) = θ₃(τ + 1)`),
  gives this for every `z` with `Im z ≥ 1/3`; hence `U - 1, W - 1 = O(e^{-π Im z})`;
* Jacobi's quartic identity `U = W + V` (`Work.Kernels.TildeFacts.theta_quartic`) turns this
  into `V = O(e^{-π Im z})`, and then `U² - W² = (U - W)(U + W) = O(e^{-π Im z})`.

The remaining factors `E₄`, `E₆`, `E₁₀` are bounded on `{Im z ≥ 1/3}` by the cusp
expansions of `Work.Asymptotics.ZAtomsThird.first_order`, while
`1/Δ = O(e^{2π Im z})` comes from `Work.Asymptotics.delta_lower_third`.
-/
import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.TildeFacts.theta_quartic
import Submission.Work.Asymptotics.ZAtomsThird.first_order
import Submission.Work.Asymptotics.KPlusFunnel.ZFacts

namespace Work.Asymptotics

open UpperHalfPlane
open Work.Kernels

noncomputable section

/-! ## Elementary constants -/

/-- `2 ≤ exp (π / 3)`. -/
lemma two_le_exp_pi_div_three : (2 : ℝ) ≤ Real.exp (Real.pi / 3) := by
  have h1 : (1 : ℝ) ≤ Real.pi / 3 := by nlinarith [Real.pi_gt_three]
  have h2 := Real.add_one_le_exp (Real.pi / 3)
  linarith

/-- `exp (-(π / 3)) ≤ 1 / 2`. -/
lemma exp_neg_pi_div_three_le_half : Real.exp (-(Real.pi / 3)) ≤ 1 / 2 := by
  rw [Real.exp_neg]
  have h := (inv_le_inv₀ (Real.exp_pos (Real.pi / 3)) (by norm_num : (0 : ℝ) < 2)).mpr
    two_le_exp_pi_div_three
  simpa using h

/-- `exp (-(π y)) ≤ 1 / 2` for `y ≥ 1 / 3`. -/
lemma exp_neg_pi_mul_le_half {y : ℝ} (hy : 1 / 3 ≤ y) : Real.exp (-(Real.pi * y)) ≤ 1 / 2 := by
  calc Real.exp (-(Real.pi * y)) ≤ Real.exp (-(Real.pi / 3)) := by
        rw [Real.exp_le_exp]; nlinarith [Real.pi_pos, hy]
    _ ≤ 1 / 2 := exp_neg_pi_div_three_le_half

/-! ## Bounds for `θ₃` and `θ₄ = θ₃(· + 1)` -/

/-- `‖θ₃(τ) - 1‖ ≤ 4 exp (-π Im τ)` for `Im τ ≥ 1/3`. -/
lemma jacobiTheta_sub_one_le_of_im (τ : ℂ) (hτ : 1 / 3 ≤ τ.im) :
    ‖jacobiTheta τ - 1‖ ≤ 4 * Real.exp (-(Real.pi * τ.im)) := by
  have hy : 0 < τ.im := by linarith
  have h := norm_jacobiTheta_sub_one_le hy
  have he : Real.exp (-Real.pi * τ.im) ≤ 1 / 2 := by
    have h' := exp_neg_pi_mul_le_half hτ
    simpa only [show -Real.pi * τ.im = -(Real.pi * τ.im) by ring] using h'
  have hpos : 0 < 1 - Real.exp (-Real.pi * τ.im) := by linarith
  have hden : 2 / (1 - Real.exp (-Real.pi * τ.im)) ≤ 4 := by
    rw [div_le_iff₀ hpos]; linarith
  calc ‖jacobiTheta τ - 1‖
      ≤ 2 / (1 - Real.exp (-Real.pi * τ.im)) * Real.exp (-Real.pi * τ.im) := h
    _ ≤ 4 * Real.exp (-Real.pi * τ.im) := mul_le_mul_of_nonneg_right hden (Real.exp_pos _).le
    _ = 4 * Real.exp (-(Real.pi * τ.im)) := by
        rw [show -Real.pi * τ.im = -(Real.pi * τ.im) by ring]

/-- `‖θ₃(τ)‖ ≤ 4` for `Im τ ≥ 1/3`. -/
lemma jacobiTheta_norm_le_of_im (τ : ℂ) (hτ : 1 / 3 ≤ τ.im) : ‖jacobiTheta τ‖ ≤ 4 := by
  have h1 := jacobiTheta_sub_one_le_of_im τ hτ
  have he := exp_neg_pi_mul_le_half hτ
  have h2 : ‖jacobiTheta τ - 1‖ ≤ 2 := by
    have h4 : 4 * Real.exp (-(Real.pi * τ.im)) ≤ 4 * (1 / 2) :=
      mul_le_mul_of_nonneg_left he (by norm_num)
    linarith
  have h3 := norm_add_le (jacobiTheta τ - 1) (1 : ℂ)
  rw [sub_add_cancel, norm_one] at h3
  linarith

/-- `‖θ₃(z) - 1‖ ≤ 4 exp (-π Im z)` on `{Im z ≥ 1/3}`. -/
lemma jacobiTheta_coe_sub_one_le_third (z : ℍ) (hz : 1 / 3 ≤ z.im) :
    ‖jacobiTheta (z : ℂ) - 1‖ ≤ 4 * Real.exp (-(Real.pi * z.im)) := by
  have h := jacobiTheta_sub_one_le_of_im (z : ℂ) (by rw [UpperHalfPlane.coe_im]; exact hz)
  rwa [UpperHalfPlane.coe_im] at h

/-- `θ₄(z) = θ₃(z + 1)` differs from `1` by `O(e^{-π Im z})` on `{Im z ≥ 1/3}`. -/
lemma jacobiTheta_shift_sub_one_le_third (z : ℍ) (hz : 1 / 3 ≤ z.im) :
    ‖jacobiTheta ((z : ℂ) + 1) - 1‖ ≤ 4 * Real.exp (-(Real.pi * z.im)) := by
  have him : ((z : ℂ) + 1).im = z.im := by simp
  have h := jacobiTheta_sub_one_le_of_im ((z : ℂ) + 1) (by rw [him]; exact hz)
  rwa [him] at h

/-- `‖θ₃(z)‖ ≤ 4` on `{Im z ≥ 1/3}`. -/
lemma jacobiTheta_coe_norm_le_four (z : ℍ) (hz : 1 / 3 ≤ z.im) :
    ‖jacobiTheta (z : ℂ)‖ ≤ 4 :=
  jacobiTheta_norm_le_of_im (z : ℂ) (by rw [UpperHalfPlane.coe_im]; exact hz)

/-- If `‖w - 1‖ ≤ A e` and `‖w‖ ≤ 4` then `‖w ^ 4 - 1‖ ≤ 85 A e`. -/
lemma norm_pow_four_sub_one_le_four {w : ℂ} {A e : ℝ} (hA : 0 ≤ A) (he : 0 ≤ e)
    (h1 : ‖w - 1‖ ≤ A * e) (h2 : ‖w‖ ≤ 4) : ‖w ^ 4 - 1‖ ≤ 85 * A * e := by
  have hfac : w ^ 4 - 1 = (w - 1) * (w ^ 3 + w ^ 2 + w + 1) := by ring
  have hw3 : ‖w ^ 3‖ ≤ 64 := by
    rw [norm_pow]
    exact le_trans (pow_le_pow_left₀ (norm_nonneg w) h2 3) (by norm_num)
  have hw2 : ‖w ^ 2‖ ≤ 16 := by
    rw [norm_pow]
    exact le_trans (pow_le_pow_left₀ (norm_nonneg w) h2 2) (by norm_num)
  have hb : ‖w ^ 3 + w ^ 2 + w + 1‖ ≤ 85 := by
    have ha := norm_add_le (w ^ 3 + w ^ 2 + w) (1 : ℂ)
    rw [norm_one] at ha
    have hb' := norm_add_le (w ^ 3 + w ^ 2) w
    have hb'' := norm_add_le (w ^ 3) (w ^ 2)
    linarith
  rw [hfac, norm_mul]
  calc ‖w - 1‖ * ‖w ^ 3 + w ^ 2 + w + 1‖ ≤ (A * e) * 85 :=
        mul_le_mul h1 hb (norm_nonneg _) (mul_nonneg hA he)
    _ = 85 * A * e := by ring

/-! ## The theta quartics `U`, `W`, `V` -/

/-- `W = θ₀₁⁴ = θ₃(· + 1)⁴`. -/
lemma WFun_eq_shift (z : ℍ) : WFun z = (jacobiTheta ((z : ℂ) + 1)) ^ 4 := by
  have h : ((ModularGroup.T • z : ℍ) : ℂ) = (z : ℂ) + 1 := by
    rw [UpperHalfPlane.modular_T_smul, UpperHalfPlane.coe_vadd]; push_cast; ring
  calc WFun z = (Work.Modular.theta4 z) ^ 4 := rfl
    _ = (Work.Modular.theta3 (ModularGroup.T • z)) ^ 4 := by rw [Work.Modular.theta3_T_smul]
    _ = (jacobiTheta ((ModularGroup.T • z : ℍ) : ℂ)) ^ 4 := rfl
    _ = (jacobiTheta ((z : ℂ) + 1)) ^ 4 := by rw [h]

/-- `U - 1 = O (e^{-π Im z})` on `{Im z ≥ 1/3}`. -/
lemma UFun_sub_one_le_third : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 / 3 ≤ z.im →
    ‖UFun z - 1‖ ≤ C * Real.exp (-(Real.pi * z.im)) := by
  refine ⟨340, by norm_num, fun z hz => ?_⟩
  have h1 := jacobiTheta_coe_sub_one_le_third z hz
  have h2 := jacobiTheta_coe_norm_le_four z hz
  have h3 := norm_pow_four_sub_one_le_four (w := jacobiTheta (z : ℂ)) (A := 4)
    (e := Real.exp (-(Real.pi * z.im))) (by norm_num) (Real.exp_pos _).le h1 h2
  have hU : UFun z = (jacobiTheta (z : ℂ)) ^ 4 := rfl
  rw [hU]
  linarith [h3]

/-- `W - 1 = O (e^{-π Im z})` on `{Im z ≥ 1/3}`. -/
lemma WFun_sub_one_le_third : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 / 3 ≤ z.im →
    ‖WFun z - 1‖ ≤ C * Real.exp (-(Real.pi * z.im)) := by
  refine ⟨340, by norm_num, fun z hz => ?_⟩
  have h1 := jacobiTheta_shift_sub_one_le_third z hz
  have him : ((z : ℂ) + 1).im = z.im := by simp
  have h2 : ‖jacobiTheta ((z : ℂ) + 1)‖ ≤ 4 := by
    refine jacobiTheta_norm_le_of_im ((z : ℂ) + 1) ?_
    rw [him]; exact hz
  have h3 := norm_pow_four_sub_one_le_four (w := jacobiTheta ((z : ℂ) + 1)) (A := 4)
    (e := Real.exp (-(Real.pi * z.im))) (by norm_num) (Real.exp_pos _).le h1 h2
  have hW : WFun z = (jacobiTheta ((z : ℂ) + 1)) ^ 4 := WFun_eq_shift z
  rw [hW]
  linarith [h3]

/-- `V = O (e^{-π Im z})` on `{Im z ≥ 1/3}`, from Jacobi's identity `U = W + V`. -/
lemma VFun_bound_third : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 / 3 ≤ z.im →
    ‖VFun z‖ ≤ C * Real.exp (-(Real.pi * z.im)) := by
  obtain ⟨CU, hCU, hU⟩ := UFun_sub_one_le_third
  obtain ⟨CW, hCW, hW⟩ := WFun_sub_one_le_third
  refine ⟨CU + CW, by positivity, fun z hz => ?_⟩
  have h1 := hU z hz
  have h2 := hW z hz
  have hV : VFun z = UFun z - WFun z := by
    have h := Work.Kernels.TildeFacts.theta_quartic z
    rw [h]; ring
  have hsplit : UFun z - WFun z = (UFun z - 1) - (WFun z - 1) := by ring
  rw [hV, hsplit]
  calc ‖(UFun z - 1) - (WFun z - 1)‖ ≤ ‖UFun z - 1‖ + ‖WFun z - 1‖ := norm_sub_le _ _
    _ ≤ CU * Real.exp (-(Real.pi * z.im)) + CW * Real.exp (-(Real.pi * z.im)) := add_le_add h1 h2
    _ = (CU + CW) * Real.exp (-(Real.pi * z.im)) := by ring

/-- `U² - W² = O (e^{-π Im z})` on `{Im z ≥ 1/3}`. -/
lemma UFun_sq_sub_WFun_sq_bound_third : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 / 3 ≤ z.im →
    ‖UFun z ^ 2 - WFun z ^ 2‖ ≤ C * Real.exp (-(Real.pi * z.im)) := by
  obtain ⟨CU, hCU, hU⟩ := UFun_sub_one_le_third
  obtain ⟨CW, hCW, hW⟩ := WFun_sub_one_le_third
  refine ⟨(CU + CW) * (2 + CU + CW) + 1, by positivity, fun z hz => ?_⟩
  have h1 := hU z hz
  have h2 := hW z hz
  have he0 : (0 : ℝ) ≤ Real.exp (-(Real.pi * z.im)) := (Real.exp_pos _).le
  have he1 : Real.exp (-(Real.pi * z.im)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, hz])
  have hV : VFun z = UFun z - WFun z := by
    have h := Work.Kernels.TildeFacts.theta_quartic z
    rw [h]; ring
  have hVb : ‖UFun z - WFun z‖ ≤ (CU + CW) * Real.exp (-(Real.pi * z.im)) := by
    have hsplit : UFun z - WFun z = (UFun z - 1) - (WFun z - 1) := by ring
    rw [hsplit]
    calc ‖(UFun z - 1) - (WFun z - 1)‖ ≤ ‖UFun z - 1‖ + ‖WFun z - 1‖ := norm_sub_le _ _
      _ ≤ CU * Real.exp (-(Real.pi * z.im)) + CW * Real.exp (-(Real.pi * z.im)) := add_le_add h1 h2
      _ = (CU + CW) * Real.exp (-(Real.pi * z.im)) := by ring
  have hUb : ‖UFun z‖ ≤ 1 + CU * Real.exp (-(Real.pi * z.im)) := by
    have h := norm_add_le (UFun z - 1) (1 : ℂ)
    rw [sub_add_cancel, norm_one] at h
    linarith
  have hWb : ‖WFun z‖ ≤ 1 + CW * Real.exp (-(Real.pi * z.im)) := by
    have h := norm_add_le (WFun z - 1) (1 : ℂ)
    rw [sub_add_cancel, norm_one] at h
    linarith
  have hUW : ‖UFun z + WFun z‖ ≤ 2 + CU + CW := by
    have h := norm_add_le (UFun z) (WFun z)
    have hCUe : CU * Real.exp (-(Real.pi * z.im)) ≤ CU := mul_le_of_le_one_right hCU.le he1
    have hCWe : CW * Real.exp (-(Real.pi * z.im)) ≤ CW := mul_le_of_le_one_right hCW.le he1
    linarith
  have hfac : UFun z ^ 2 - WFun z ^ 2 = (UFun z - WFun z) * (UFun z + WFun z) := by ring
  rw [hfac, norm_mul]
  have hstep : ‖UFun z - WFun z‖ * ‖UFun z + WFun z‖
      ≤ ((CU + CW) * Real.exp (-(Real.pi * z.im))) * (2 + CU + CW) :=
    mul_le_mul hVb hUW (norm_nonneg _) (by positivity)
  have hCU0 : (0 : ℝ) ≤ CU + CW := by positivity
  have hK0 : (0 : ℝ) ≤ (CU + CW) * (2 + CU + CW) := by positivity
  calc ‖UFun z - WFun z‖ * ‖UFun z + WFun z‖
      ≤ ((CU + CW) * (2 + CU + CW)) * Real.exp (-(Real.pi * z.im)) := by
        rw [mul_assoc] at hstep
        linarith [hstep]
    _ ≤ ((CU + CW) * (2 + CU + CW) + 1) * Real.exp (-(Real.pi * z.im)) :=
        mul_le_mul_of_nonneg_right (by linarith) he0

/-! ## The bounded Eisenstein factors -/

/-- `E₄` is bounded on `{Im z ≥ 1/3}`. -/
lemma E4Fun_bound_third : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 / 3 ≤ z.im → ‖E4Fun z‖ ≤ C := by
  obtain ⟨C, hC, _, h4, _, _⟩ := ZAtomsThird.first_order
  refine ⟨1 + C, by positivity, fun z hz => ?_⟩
  have hq := norm_qParam_le_third (z := z) hz
  have h1 := h4 z hz
  have hsplit : E4Fun z = (E4Fun z - 1) + 1 := by ring
  rw [hsplit]
  calc ‖(E4Fun z - 1) + 1‖ ≤ ‖E4Fun z - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
    _ ≤ C * ‖qParamFun z‖ + 1 := by rw [norm_one]; linarith
    _ ≤ 1 + C := by nlinarith [hC.le, hq, norm_nonneg (qParamFun z)]

/-- `E₆` is bounded on `{Im z ≥ 1/3}`. -/
lemma E6Fun_bound_third : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 / 3 ≤ z.im → ‖E6Fun z‖ ≤ C := by
  obtain ⟨C, hC, _, _, h6, _⟩ := ZAtomsThird.first_order
  refine ⟨1 + C, by positivity, fun z hz => ?_⟩
  have hq := norm_qParam_le_third (z := z) hz
  have h1 := h6 z hz
  have hsplit : E6Fun z = (E6Fun z - 1) + 1 := by ring
  rw [hsplit]
  calc ‖(E6Fun z - 1) + 1‖ ≤ ‖E6Fun z - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
    _ ≤ C * ‖qParamFun z‖ + 1 := by rw [norm_one]; linarith
    _ ≤ 1 + C := by nlinarith [hC.le, hq, norm_nonneg (qParamFun z)]

/-- `1 / Δ = O (e^{2π Im z})` on `{Im z ≥ 1/3}`. -/
lemma DeltaFun_inv_le_third : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 / 3 ≤ z.im →
    ‖DeltaFun z‖⁻¹ ≤ C * Real.exp (2 * Real.pi * z.im) := by
  obtain ⟨cD, hcD, hD⟩ := delta_lower_third
  refine ⟨cD⁻¹, inv_pos.mpr hcD, fun z hz => ?_⟩
  have hqz : 0 < ‖qParamFun z‖ := by rw [norm_qParamFun]; exact Real.exp_pos _
  have h1 : cD * ‖qParamFun z‖ ≤ ‖DeltaFun z‖ := hD z hz
  have hpos : 0 < ‖DeltaFun z‖ := lt_of_lt_of_le (mul_pos hcD hqz) h1
  have h2 : ‖DeltaFun z‖⁻¹ ≤ (cD * ‖qParamFun z‖)⁻¹ := inv_anti₀ (mul_pos hcD hqz) h1
  calc ‖DeltaFun z‖⁻¹ ≤ (cD * ‖qParamFun z‖)⁻¹ := h2
    _ = cD⁻¹ * Real.exp (2 * Real.pi * z.im) := by
        rw [mul_inv, norm_qParamFun, Real.exp_neg, inv_inv]

/-- `j = E₄³/Δ = O (e^{2π Im z})` on `{Im z ≥ 1/3}`. -/
lemma jInvariantFun_bound_third : ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 1 / 3 ≤ z.im →
    ‖jInvariantFun z‖ ≤ C * Real.exp (2 * Real.pi * z.im) := by
  obtain ⟨cE4, hcE4, hE4⟩ := E4Fun_bound_third
  obtain ⟨cDi, hcDi, hDi⟩ := DeltaFun_inv_le_third
  refine ⟨cE4 ^ 3 * cDi, by positivity, fun z hz => ?_⟩
  have h1 := hE4 z hz
  have h2 := hDi z hz
  have hcoe : jInvariantFun z = E4Fun z ^ 3 / DeltaFun z := rfl
  rw [hcoe, norm_div, norm_pow]
  calc ‖E4Fun z‖ ^ 3 / ‖DeltaFun z‖ = ‖E4Fun z‖ ^ 3 * ‖DeltaFun z‖⁻¹ := by rw [div_eq_mul_inv]
    _ ≤ cE4 ^ 3 * (cDi * Real.exp (2 * Real.pi * z.im)) :=
        mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) h1 3) h2 (inv_nonneg.mpr (norm_nonneg _))
          (by positivity)
    _ = cE4 ^ 3 * cDi * Real.exp (2 * Real.pi * z.im) := by ring

/-! ## The target -/

theorem KMinusFunnelZBounds :
    ∃ C : ℝ, 0 < C ∧ ∀ z : UpperHalfPlane, 1 / 3 ≤ z.im →
      ‖Work.Kernels.E8Fun z * Work.Kernels.VFun z + Work.Kernels.E6Fun z * (Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2)‖ ≤ C ∧
      ‖Work.Kernels.E8Fun z * Work.Kernels.VFun z‖ ≤ C ∧
      ‖Work.Kernels.VFun z‖ ≤ C ∧
      ‖Work.Kernels.jInvariantFun z * Work.Kernels.VFun z‖ ≤ C * Real.exp (Real.pi * z.im) ∧
      ‖Work.Kernels.E10Fun z / Work.Kernels.DeltaFun z * (Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2)‖ ≤ C * Real.exp (Real.pi * z.im) := by
  obtain ⟨cV, hcV, hV⟩ := VFun_bound_third
  obtain ⟨c2, hc2, h2⟩ := UFun_sq_sub_WFun_sq_bound_third
  obtain ⟨cE4, hcE4, hE4⟩ := E4Fun_bound_third
  obtain ⟨cE6, hcE6, hE6⟩ := E6Fun_bound_third
  obtain ⟨cDi, hcDi, hDi⟩ := DeltaFun_inv_le_third
  obtain ⟨cj, hcj, hj⟩ := jInvariantFun_bound_third
  refine ⟨cE4 ^ 2 * cV + cE6 * c2 + cE4 * cE6 * c2 * cDi + cj * cV + cV + 1,
    by positivity, fun z hz => ?_⟩
  have hVz := hV z hz
  have h2z := h2 z hz
  have hE4z := hE4 z hz
  have hE6z := hE6 z hz
  have hDiz := hDi z hz
  have hjz := hj z hz
  set e : ℝ := Real.exp (-(Real.pi * z.im)) with he
  have he0 : 0 ≤ e := by rw [he]; exact (Real.exp_pos _).le
  have he1 : e ≤ 1 := by
    rw [he]; exact Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, hz])
  have hE8z : ‖E8Fun z‖ ≤ cE4 ^ 2 := by
    rw [show E8Fun z = E4Fun z ^ 2 from rfl, norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hE4z 2
  have hE10z : ‖E10Fun z‖ ≤ cE4 * cE6 := by
    rw [show E10Fun z = E4Fun z * E6Fun z from rfl, norm_mul]
    exact mul_le_mul hE4z hE6z (norm_nonneg _) hcE4.le
  have hn_a : (0 : ℝ) ≤ cE4 ^ 2 * cV := by positivity
  have hn_b : (0 : ℝ) ≤ cE6 * c2 := by positivity
  have hn_c : (0 : ℝ) ≤ cE4 * cE6 * c2 * cDi := by positivity
  have hn_d : (0 : ℝ) ≤ cj * cV := by positivity
  have hb1 : ‖E8Fun z * VFun z‖ ≤ cE4 ^ 2 * cV := by
    rw [norm_mul]
    calc ‖E8Fun z‖ * ‖VFun z‖ ≤ cE4 ^ 2 * (cV * e) :=
          mul_le_mul hE8z hVz (norm_nonneg _) (by positivity)
      _ = cE4 ^ 2 * cV * e := by ring
      _ ≤ cE4 ^ 2 * cV * 1 := mul_le_mul_of_nonneg_left he1 (by positivity)
      _ = cE4 ^ 2 * cV := by ring
  have hb2 : ‖E6Fun z * (UFun z ^ 2 - WFun z ^ 2)‖ ≤ cE6 * c2 := by
    rw [norm_mul]
    calc ‖E6Fun z‖ * ‖UFun z ^ 2 - WFun z ^ 2‖ ≤ cE6 * (c2 * e) :=
          mul_le_mul hE6z h2z (norm_nonneg _) hcE6.le
      _ = cE6 * c2 * e := by ring
      _ ≤ cE6 * c2 * 1 := mul_le_mul_of_nonneg_left he1 (by positivity)
      _ = cE6 * c2 := by ring
  have hb3 : ‖VFun z‖ ≤ cV := by
    calc ‖VFun z‖ ≤ cV * e := hVz
      _ ≤ cV * 1 := mul_le_mul_of_nonneg_left he1 hcV.le
      _ = cV := by ring
  have hb4 : ‖jInvariantFun z * VFun z‖ ≤ cj * cV * Real.exp (Real.pi * z.im) := by
    rw [norm_mul]
    calc ‖jInvariantFun z‖ * ‖VFun z‖
        ≤ (cj * Real.exp (2 * Real.pi * z.im)) * (cV * e) :=
          mul_le_mul hjz hVz (norm_nonneg _) (by positivity)
      _ = cj * cV * (Real.exp (2 * Real.pi * z.im) * e) := by ring
      _ = cj * cV * Real.exp (Real.pi * z.im) := by
          rw [he, ← Real.exp_add,
            show 2 * Real.pi * z.im + -(Real.pi * z.im) = Real.pi * z.im by ring]
  have hb5 : ‖E10Fun z / DeltaFun z * (UFun z ^ 2 - WFun z ^ 2)‖
      ≤ cE4 * cE6 * c2 * cDi * Real.exp (Real.pi * z.im) := by
    rw [norm_mul, norm_div]
    calc ‖E10Fun z‖ / ‖DeltaFun z‖ * ‖UFun z ^ 2 - WFun z ^ 2‖
        = ‖E10Fun z‖ * (‖DeltaFun z‖⁻¹ * ‖UFun z ^ 2 - WFun z ^ 2‖) := by ring
      _ ≤ (cE4 * cE6) * ((cDi * Real.exp (2 * Real.pi * z.im)) * (c2 * e)) :=
          mul_le_mul hE10z (mul_le_mul hDiz h2z (norm_nonneg _) (by positivity))
            (by positivity) (by positivity)
      _ = cE4 * cE6 * c2 * cDi * (Real.exp (2 * Real.pi * z.im) * e) := by ring
      _ = cE4 * cE6 * c2 * cDi * Real.exp (Real.pi * z.im) := by
          rw [he, ← Real.exp_add,
            show 2 * Real.pi * z.im + -(Real.pi * z.im) = Real.pi * z.im by ring]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · calc ‖E8Fun z * VFun z + E6Fun z * (UFun z ^ 2 - WFun z ^ 2)‖
        ≤ ‖E8Fun z * VFun z‖ + ‖E6Fun z * (UFun z ^ 2 - WFun z ^ 2)‖ := norm_add_le _ _
      _ ≤ cE4 ^ 2 * cV + cE6 * c2 := add_le_add hb1 hb2
      _ ≤ cE4 ^ 2 * cV + cE6 * c2 + cE4 * cE6 * c2 * cDi + cj * cV + cV + 1 := by linarith
  · exact le_trans hb1 (by linarith)
  · exact le_trans hb3 (by linarith)
  · exact le_trans hb4 (mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le)
  · exact le_trans hb5 (mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le)

end

end Work.Asymptotics
