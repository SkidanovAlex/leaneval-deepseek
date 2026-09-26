import Mathlib
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.Residues.KMinusCuspDefs
import Submission.Work.Residues.ThetaDecay

namespace Work.Asymptotics.KhatE1

/-!
# The bounds `‖U - 1‖ ≤ 40 tpar` and `‖W - 1‖ ≤ 40 tpar` on the funnel

On the funnel `Funnel = {τ ∈ 𝒟 : 2 ≤ Im τ}` the cusp parameter is
`tpar τ = e^{-π Im τ} ≤ e^{-2π}`, and both theta quartics `U = θ₀₀⁴` and `W = θ₀₁⁴`
are `1 + O(tpar)`.  Concretely, `Work.Residues.UFun_decay` and
`Work.Residues.WFun_decay` are proved with the explicit constant
`15 * thetaA + 1 = 15 * 2/(1 - e^{-π}) + 1 ≤ 40`, which is what we record here.

The cruder estimate `e^{-π} ≤ 1/8` (from `e^π ≥ e^3 ≥ 2^3 = 8`) gives
`thetaA = 2/(1 - e^{-π}) ≤ 13/5`, hence `15 thetaA + 1 ≤ 40`.
-/

/-- `8 ≤ e ^ π`, from `e ^ π ≥ e ^ 3 = (e ^ 1) ^ 3 ≥ 2 ^ 3 = 8`. -/
private lemma exp_pi_ge_eight : (8 : ℝ) ≤ Real.exp Real.pi := by
  have h3 : Real.exp 3 ≤ Real.exp Real.pi := Real.exp_le_exp.mpr Real.pi_gt_three.le
  have h2 : (8 : ℝ) ≤ Real.exp 3 := by
    have h : Real.exp 3 = (Real.exp 1) ^ 3 := by simpa using Real.exp_nat_mul 1 3
    rw [h]
    have h1 : (2 : ℝ) ≤ Real.exp 1 := Real.exp_one_gt_two.le
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ (Real.exp 1) ^ 3 := pow_le_pow_left₀ (by norm_num) h1 3
  linarith

/-- `e ^ (-π) ≤ 1 / 8`. -/
private lemma exp_neg_pi_le_eighth : Real.exp (-Real.pi) ≤ 1 / 8 := by
  rw [Real.exp_neg]
  simpa [one_div] using
    (one_div_le_one_div_of_le (a := (8 : ℝ)) (b := Real.exp Real.pi)
      (by norm_num) exp_pi_ge_eight)

/-- `thetaA = 2 / (1 - e^{-π}) ≤ 13 / 5`. -/
private lemma thetaA_le_thirteen_fifths : Work.Residues.thetaA ≤ 13 / 5 := by
  have he8 := exp_neg_pi_le_eighth
  have hden : (0 : ℝ) < 1 - Real.exp (-Real.pi) := by
    have := Real.exp_pos (-Real.pi); linarith
  rw [Work.Residues.thetaA, div_le_iff₀ hden]
  nlinarith [he8]

/-- `15 * thetaA + 1 ≤ 40`. -/
private lemma fifteen_thetaA_add_one_le : 15 * Work.Residues.thetaA + 1 ≤ 40 := by
  have h := thetaA_le_thirteen_fifths
  nlinarith

theorem E1funnel_UW_bounds :
    ∀ τ : UpperHalfPlane, Work.Asymptotics.Funnel τ →
      ‖Work.Kernels.UFun τ - 1‖ ≤ 40 * Work.Residues.tpar τ ∧
      ‖Work.Kernels.WFun τ - 1‖ ≤ 40 * Work.Residues.tpar τ := by
  intro τ hτ
  have him : 1 ≤ τ.im := le_trans (by norm_num) hτ.2
  have h40 : 15 * Work.Residues.thetaA ≤ 40 := by linarith [fifteen_thetaA_add_one_le]
  constructor
  · have hz : 1 ≤ ((τ : ℂ)).im := by rw [UpperHalfPlane.coe_im]; exact him
    have h1 := Work.Residues.norm_jacobiTheta_sub_one_bound (τ : ℂ) hz
    have h2 := Work.Residues.norm_jacobiTheta_le_two (τ : ℂ) hz
    have h3 := Work.Residues.norm_pow_four_sub_one_le (w := jacobiTheta (τ : ℂ))
      (A := Work.Residues.thetaA) (e := Real.exp (-(Real.pi * (τ : ℂ).im)))
      Work.Residues.thetaA_nonneg (Real.exp_nonneg _) h1 h2
    rw [show Work.Kernels.UFun τ = jacobiTheta (τ : ℂ) ^ 4 from rfl, Work.Residues.tpar]
    simp only [UpperHalfPlane.coe_im] at h3
    exact le_trans h3 (mul_le_mul_of_nonneg_right h40 (Real.exp_nonneg _))
  · have himz : (((ModularGroup.T • τ : UpperHalfPlane) : ℂ)).im = τ.im := by
      rw [Work.Kernels.coe_T_smul, Complex.add_im, Complex.one_im, add_zero,
        UpperHalfPlane.coe_im]
    have hz : 1 ≤ (((ModularGroup.T • τ : UpperHalfPlane) : ℂ)).im := by
      rw [himz]; exact him
    have h1 : ‖jacobiTheta (((ModularGroup.T • τ : UpperHalfPlane) : ℂ)) - 1‖
        ≤ Work.Residues.thetaA * Real.exp (-(Real.pi * τ.im)) := by
      have hh := Work.Residues.norm_jacobiTheta_sub_one_bound
        (((ModularGroup.T • τ : UpperHalfPlane) : ℂ)) hz
      rw [himz] at hh
      exact hh
    have h2 := Work.Residues.norm_jacobiTheta_le_two
      (((ModularGroup.T • τ : UpperHalfPlane) : ℂ)) hz
    have h3 := Work.Residues.norm_pow_four_sub_one_le
      (w := jacobiTheta (((ModularGroup.T • τ : UpperHalfPlane) : ℂ)))
      (A := Work.Residues.thetaA) (e := Real.exp (-(Real.pi * τ.im)))
      Work.Residues.thetaA_nonneg (Real.exp_nonneg _) h1 h2
    have hW : Work.Kernels.WFun τ
        = jacobiTheta (((ModularGroup.T • τ : UpperHalfPlane) : ℂ)) ^ 4 := by
      rw [show Work.Kernels.WFun τ = Work.Modular.theta4 τ ^ 4 from rfl,
        ← Work.Modular.theta3_T_smul τ]
      rfl
    rw [hW, Work.Residues.tpar]
    exact le_trans h3 (mul_le_mul_of_nonneg_right h40 (Real.exp_nonneg _))

end Work.Asymptotics.KhatE1
