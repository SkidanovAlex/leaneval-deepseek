import Mathlib
import Submission.Work.Asymptotics.KMinusCuspBallDefs
import Submission.Work.Residues.KMinusCuspDefs
import Submission.Work.Kernels.ModerateGrowth

/-!
# The cusp-`0` tile `E` of the CKMRV `K_-` estimate

This file defines the region

  `E = {τ : ℍ | 3 / 2 ≤ (S • τ).im}`

(the cusp-`0` neighbourhood `{τ : ‖τ - i/3‖ ≤ 1/3} \ {0}` of the upper half plane) on which the
CKMRV `E`-order bound `Work.Asymptotics.KMinus_slash_bound_E` is stated, and records the
elementary geometry of `S • τ` on it: `‖τ‖ ≤ 2 / 3`, `‖S • τ‖ ≥ 3 / 2`,
`1 / (S • τ).im ≤ 2 / 3`, and the scale comparison `scale (S • τ) ≤ 3 * scale τ`.

## Main definitions

* `Work.Asymptotics.EReg` : the cusp-`0` tile `E = {τ | 3 / 2 ≤ (S • τ).im}`.
-/

noncomputable section

open UpperHalfPlane ModularGroup

namespace Work.Asymptotics

open Work.Kernels (scale)

/-- The cusp-`0` tile `E = {τ : ℍ | 3 / 2 ≤ (S • τ).im}` on which the `K_-` `E`-estimate is
stated.  It is the disk of radius `1/3` about `i/3` (with the origin removed). -/
def EReg : Set ℍ := {τ : ℍ | (3 / 2 : ℝ) ≤ (ModularGroup.S • τ).im}

lemma mem_EReg {τ : ℍ} : τ ∈ EReg ↔ (3 / 2 : ℝ) ≤ (ModularGroup.S • τ).im := Iff.rfl

/-- `(S • τ).im = τ.im / ‖τ‖²`. -/
lemma EReg_S_im (τ : ℍ) : (ModularGroup.S • τ).im = τ.im / ‖(τ : ℂ)‖ ^ 2 := by
  rw [Work.Kernels.im_smul_eq, Work.Kernels.jFun_apply]
  simp

lemma EReg_normSq_eq (τ : ℍ) : ‖(τ : ℂ)‖ ^ 2 = τ.re ^ 2 + τ.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  ring

lemma EReg_norm_pos (τ : ℍ) : 0 < ‖(τ : ℂ)‖ := norm_pos_iff.mpr τ.ne_zero

lemma EReg_im_le_norm (τ : ℍ) : τ.im ≤ ‖(τ : ℂ)‖ := by
  have h1 := Complex.abs_im_le_norm (τ : ℂ)
  rw [UpperHalfPlane.coe_im, abs_of_pos τ.im_pos] at h1
  exact h1

/-- On `E`, `‖τ‖² ≤ (2/3) τ.im`. -/
lemma EReg_normSq_le (τ : ℍ) (hτ : τ ∈ EReg) : ‖(τ : ℂ)‖ ^ 2 ≤ (2 / 3 : ℝ) * τ.im := by
  have hS : (3 / 2 : ℝ) ≤ τ.im / ‖(τ : ℂ)‖ ^ 2 := by rw [← EReg_S_im]; exact hτ
  have hn : 0 < ‖(τ : ℂ)‖ ^ 2 := pow_pos (EReg_norm_pos τ) 2
  rw [le_div_iff₀ hn] at hS
  linarith

/-- On `E`, `‖τ‖ ≤ 2/3`. -/
lemma EReg_norm_le (τ : ℍ) (hτ : τ ∈ EReg) : ‖(τ : ℂ)‖ ≤ 2 / 3 := by
  have h1 := EReg_normSq_le τ hτ
  have h2 := EReg_im_le_norm τ
  have h3 : ‖(τ : ℂ)‖ ^ 2 ≤ (2 / 3 : ℝ) * ‖(τ : ℂ)‖ := le_trans h1 (by linarith)
  have h4 : 0 < ‖(τ : ℂ)‖ := EReg_norm_pos τ
  nlinarith [h3, h4]

/-- On `E`, `1 / ‖τ‖ ≤ scale τ`. -/
lemma EReg_inv_norm_le_scale (τ : ℍ) : (‖(τ : ℂ)‖)⁻¹ ≤ scale τ := by
  have h1 : (‖(τ : ℂ)‖)⁻¹ ≤ (τ.im)⁻¹ :=
    inv_anti₀ τ.im_pos (EReg_im_le_norm τ)
  exact le_trans h1 (Work.Kernels.inv_im_le_scale τ)

/-- On `E`, `‖S • τ‖ = 1 / ‖τ‖`. -/
lemma EReg_norm_S (τ : ℍ) : ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖ = (‖(τ : ℂ)‖)⁻¹ := by
  rw [Work.Kernels.S_smul_coe, norm_neg, norm_inv]

/-- On `E`, `3/2 ≤ ‖S • τ‖`. -/
lemma EReg_norm_S_ge (τ : ℍ) (hτ : τ ∈ EReg) : (3 / 2 : ℝ) ≤ ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖ := by
  rw [EReg_norm_S]
  have h := EReg_norm_le τ hτ
  have h2 : (0 : ℝ) < ‖(τ : ℂ)‖ := EReg_norm_pos τ
  have h3 : (‖(τ : ℂ)‖)⁻¹ = 1 / ‖(τ : ℂ)‖ := by rw [one_div]
  rw [h3]
  have h4 : (3 / 2 : ℝ) = 1 / (2 / 3 : ℝ) := by norm_num
  rw [h4]
  exact one_div_le_one_div_of_le h2 h

/-- On `E`, `1 / (S • τ).im ≤ 2/3`. -/
lemma EReg_inv_im_S_le (τ : ℍ) (hτ : τ ∈ EReg) : ((ModularGroup.S • τ).im)⁻¹ ≤ 2 / 3 := by
  rw [EReg_S_im]
  have h1 := EReg_normSq_le τ hτ
  have hpos : 0 < τ.im / ‖(τ : ℂ)‖ ^ 2 := by
    have : (0 : ℝ) < ‖(τ : ℂ)‖ ^ 2 := pow_pos (EReg_norm_pos τ) 2
    positivity
  rw [inv_div]
  have h2 : (3 / 2 : ℝ) ≤ τ.im / ‖(τ : ℂ)‖ ^ 2 := by rw [← EReg_S_im]; exact hτ
  have h3 : ‖(τ : ℂ)‖ ^ 2 ≤ (2 / 3 : ℝ) * τ.im := h1
  have him : 0 < τ.im := τ.im_pos
  have hn : 0 < ‖(τ : ℂ)‖ ^ 2 := pow_pos (EReg_norm_pos τ) 2
  rw [div_le_iff₀ him]
  rw [le_div_iff₀ hn] at h2
  linarith

/-- The scale of `S • τ` is comparable to the scale of `τ` on `E`. -/
lemma EReg_scale_S_le (τ : ℍ) (hτ : τ ∈ EReg) : scale (ModularGroup.S • τ) ≤ 3 * scale τ := by
  have h1 : (scale (ModularGroup.S • τ)) = 1 + ((ModularGroup.S • τ).im)⁻¹
      + ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖ := rfl
  rw [h1]
  have h2 := EReg_inv_im_S_le τ hτ
  have h3 : ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖ ≤ scale τ := by
    rw [EReg_norm_S]; exact EReg_inv_norm_le_scale τ
  have h4 : (1 : ℝ) ≤ scale τ := Work.Kernels.one_le_scale τ
  linarith

/-- `tpar (S • τ)` is positive. -/
lemma EReg_tpar_S_pos (τ : ℍ) : 0 < Work.Residues.tpar (ModularGroup.S • τ) :=
  Work.Residues.tpar_pos _

/-- `tpar (S • τ) ≤ 1` on `E`. -/
lemma EReg_tpar_S_le_one (τ : ℍ) : Work.Residues.tpar (ModularGroup.S • τ) ≤ 1 :=
  Work.Residues.tpar_le_one _

/-- `tpar z² = ‖q z‖`. -/
lemma EReg_tpar_sq (z : ℍ) : Work.Residues.tpar z ^ 2 = ‖Work.Kernels.qParamFun z‖ := by
  rw [Work.Residues.tpar_eq_norm_Ept, Work.Residues.norm_Ept, sq, ← Real.exp_add]
  congr 1
  rw [Work.Kernels.qParamFun, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, UpperHalfPlane.coe_im]
  ring

/-- On `E`, `tpar (S • τ)² = ‖q (S • τ)‖`. -/
lemma EReg_tpar_S_sq_eq (τ : ℍ) :
    Work.Residues.tpar (ModularGroup.S • τ) ^ 2 = ‖Work.Kernels.qParamFun (ModularGroup.S • τ)‖ :=
  EReg_tpar_sq _

end Work.Asymptotics
