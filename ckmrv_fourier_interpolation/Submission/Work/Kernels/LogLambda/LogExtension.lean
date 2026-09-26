/-
# The explicit branch of `log λ` on `{im z > 1/2}`, and the chosen logarithm `Lfun`

The explicit branch

  `LU(z) = πiz + 4log 2 + 4log(θ₁₀(z)/(2 e^{πiz/4})) - 4log θ₀₀(z)`

was introduced in `LogConstruct` on the half plane `{im z > 1}`.  In fact both principal
logarithm arguments, `θ₁₀(z)/(2e^{πiz/4}) = θ₂(z/2,z)/2` and `θ₀₀(z)`, already lie in the disc
of radius `1` about `1` as soon as `im z > 1/2`; hence `LU` is a legitimate branch of `log λ`
on the larger half plane `W = {z | 1/2 < im z}`.  Since `Lfun - LU` is continuous on the
connected set `W` with values in `2πiℤ` and vanishes at `2i`, it vanishes identically:

  `Lfun z = LU z` for all `z ∈ W`.

This file also fixes `Lfun` as the chosen logarithm of `λ` produced by `exists_L`.
-/
import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.LogLambda.LogConstruct
import Submission.Work.Analysis.DiscreteValues.eq_const_of_isPreconnected

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Complex Set Filter Topology
open scoped Modular

namespace Work.Kernels.LogLambda

/-! ## The larger half plane `W = {im z > 1/2}` -/

/-- The half plane `{z : ℂ | 1/2 < im z}`. -/
def W : Set ℂ := {z : ℂ | 1 / 2 < z.im}

lemma W_subset_U : W ⊆ U := fun z hz => by
  simp only [U, W, Set.mem_setOf_eq] at hz ⊢
  linarith

lemma isPreconnected_W : IsPreconnected W :=
  (convex_halfSpace_im_gt (1 / 2 : ℝ)).isPreconnected

lemma two_I_mem_W : (2 * Complex.I : ℂ) ∈ W := by
  simp only [W, Set.mem_setOf_eq]
  norm_num

/-! ## Elementary exponential estimates -/

lemma exp_lt_third_of_lt {u : ℝ} (hu : u < -(Real.pi / 2)) : Real.exp u < 1 / 3 := by
  have h3 : (3 : ℝ) < Real.exp (Real.pi / 2) := by
    have h := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ Real.pi / 2 by positivity)
    nlinarith [Real.pi_gt_three]
  have h4 : Real.exp (-(Real.pi / 2)) < 1 / 3 := by
    rw [Real.exp_neg, show (1 : ℝ) / 3 = (3 : ℝ)⁻¹ by norm_num,
      inv_lt_comm₀ (Real.exp_pos _) (by norm_num), inv_inv]
    exact h3
  exact lt_trans (Real.exp_lt_exp.mpr hu) h4

lemma exp_lt_half_of_lt {u : ℝ} (hu : u < -Real.pi) : Real.exp u < 1 / 2 := by
  have h3 : (2 : ℝ) < Real.exp Real.pi := by
    have h := Real.add_one_le_exp Real.pi
    linarith [Real.pi_gt_three]
  have h4 : Real.exp (-Real.pi) < 1 / 2 := by
    rw [Real.exp_neg, show (1 : ℝ) / 2 = (2 : ℝ)⁻¹ by norm_num,
      inv_lt_comm₀ (Real.exp_pos _) (by norm_num), inv_inv]
    exact h3
  exact lt_trans (Real.exp_lt_exp.mpr hu) h4

/-! ## The branch conditions on `W` -/

lemma norm_thetaC00_sub_one_lt_W {z : ℂ} (hz : 1 / 2 < z.im) : ‖thetaC00 z - 1‖ < 1 := by
  have hy : 0 < z.im := by linarith
  have h := norm_jacobiTheta_sub_one_le (τ := z) (by simpa using hy)
  have he := exp_lt_third_of_lt (u := (-Real.pi) * z.im) (by nlinarith [Real.pi_pos, hz])
  have hden : 0 < 1 - Real.exp (-Real.pi * z.im) := by linarith
  have h' : 2 / (1 - Real.exp (-Real.pi * z.im)) * Real.exp (-Real.pi * z.im) < 1 := by
    rw [show 2 / (1 - Real.exp (-Real.pi * z.im)) * Real.exp (-Real.pi * z.im)
      = 2 * Real.exp (-Real.pi * z.im) / (1 - Real.exp (-Real.pi * z.im)) by ring,
      div_lt_one hden]
    linarith
  rw [show thetaC00 z - 1 = jacobiTheta z - 1 from rfl]
  exact lt_of_le_of_lt h h'

lemma thetaC00_ne_zero_W {z : ℂ} (hz : 1 / 2 < z.im) : thetaC00 z ≠ 0 := by
  intro h0
  have h := norm_thetaC00_sub_one_lt_W hz
  rw [h0, zero_sub, norm_neg, norm_one] at h
  linarith

lemma ratio_small_W {z : ℂ} (hz : 1 / 2 < z.im) :
    ‖jacobiTheta₂ (z/2) z / 2 - 1‖ < 1 := by
  have h := ThetaLower.ratio_estimate z (by linarith)
  have he := exp_lt_half_of_lt (u := -(2 * Real.pi * z.im)) (by nlinarith [Real.pi_pos, hz])
  have hden : 0 < 1 - Real.exp (-(2 * Real.pi * z.im)) := by linarith
  have h' : Real.exp (-(2 * Real.pi * z.im)) / (1 - Real.exp (-(2 * Real.pi * z.im))) < 1 := by
    rw [div_lt_one hden]
    linarith
  exact lt_of_le_of_lt h h'

lemma ratio_ne_zero_W {z : ℂ} (hz : 1 / 2 < z.im) :
    jacobiTheta₂ (z/2) z / 2 ≠ 0 := by
  intro h0
  have h := ratio_small_W hz
  rw [h0, zero_sub, norm_neg, norm_one] at h
  linarith

lemma thetaC00_mem_slitPlane_W {z : ℂ} (hz : 1 / 2 < z.im) : thetaC00 z ∈ Complex.slitPlane :=
  Work.Analysis.BranchLog.mem_slitPlane_of_norm_sub_one_lt (norm_thetaC00_sub_one_lt_W hz)

lemma ratio_mem_slitPlane_W {z : ℂ} (hz : 1 / 2 < z.im) :
    jacobiTheta₂ (z/2) z / 2 ∈ Complex.slitPlane :=
  Work.Analysis.BranchLog.mem_slitPlane_of_norm_sub_one_lt (ratio_small_W hz)

/-! ## `LU` is a logarithm of `λ` on `W` -/

lemma exp_LU_W (z : ℂ) (hz : 1 / 2 < z.im) : Complex.exp (LU z) = lamC z := by
  have ht0 : thetaC00 z ≠ 0 := thetaC00_ne_zero_W hz
  have hrmid : ‖jacobiTheta₂ (z/2) z / 2 - 1‖ < 1 := ratio_small_W hz
  have hr0 : jacobiTheta₂ (z/2) z / 2 ≠ 0 := ratio_ne_zero_W hz
  have hexpand : Complex.exp (LU z)
      = Complex.exp (Real.pi * Complex.I * z) * 16
        * (jacobiTheta₂ (z/2) z / 2)^4 * (thetaC00 z ^ 4)⁻¹ := by
    rw [LU, thetaC10_div_exp]
    rw [show Real.pi * Complex.I * z + 4 * ↑(Real.log 2) + 4 * Complex.log (jacobiTheta₂ (z / 2) z / 2) - 4 * Complex.log (thetaC00 z)
        = Real.pi * Complex.I * z + (4 * ↑(Real.log 2) + (4 * Complex.log (jacobiTheta₂ (z/2) z / 2) + (-4) * Complex.log (thetaC00 z))) by ring]
    rw [Complex.exp_add, Complex.exp_add, Complex.exp_add, exp_four_log hr0, exp_neg_four_log ht0, exp_four_log_two]
    ring
  have hratio : Complex.exp (Real.pi * Complex.I * z) * 16 * (jacobiTheta₂ (z/2) z / 2)^4
      = thetaC10 z ^ 4 := by
    rw [← thetaC10_div_exp]
    have hexp4 : (Complex.exp (Real.pi * Complex.I * z / 4))^4
        = Complex.exp (Real.pi * Complex.I * z) := by
      rw [← Complex.exp_nat_mul]
      congr 1
      ring
    rw [div_pow, mul_pow, hexp4]
    have h16 : (2:ℂ)^4 = 16 := by norm_num
    rw [h16]
    field_simp
  rw [hexpand, hratio]
  show thetaC10 z ^ 4 * (thetaC00 z ^ 4)⁻¹ = lamC z
  rw [lamC, div_eq_mul_inv]

lemma continuousOn_ratio_W : ContinuousOn (fun z : ℂ => jacobiTheta₂ (z/2) z / 2) W := by
  have h1 : ContinuousOn (fun z : ℂ => thetaC10 z / (2*Complex.exp (Real.pi*Complex.I*z/4))) W :=
    (differentiableOn_thetaC10.mono W_subset_U).continuousOn.div (by fun_prop)
      (fun z _ => mul_ne_zero two_ne_zero (Complex.exp_ne_zero _))
  refine h1.congr (fun z _ => ?_)
  exact (thetaC10_div_exp z).symm

lemma continuousOn_LU_W : ContinuousOn LU W := by
  have h1 : ContinuousOn (fun z : ℂ => Real.pi * Complex.I * z + 4 * (Real.log 2 : ℂ)) W := by
    fun_prop
  have h2 : ContinuousOn (fun z : ℂ => 4 * Complex.log (jacobiTheta₂ (z/2) z / 2)) W :=
    (continuousOn_ratio_W.clog (fun z hz => ratio_mem_slitPlane_W hz)).const_mul 4
  have h3 : ContinuousOn (fun z : ℂ => 4 * Complex.log (thetaC00 z)) W :=
    ((differentiableOn_thetaC00.mono W_subset_U).continuousOn.clog
      (fun z hz => thetaC00_mem_slitPlane_W hz)).const_mul 4
  have h4 : ContinuousOn (fun z : ℂ => Real.pi * Complex.I * z + 4 * (Real.log 2 : ℂ)
      + 4 * Complex.log (jacobiTheta₂ (z/2) z / 2) - 4 * Complex.log (thetaC00 z)) W :=
    (h1.add h2).sub h3
  refine h4.congr (fun z _ => ?_)
  show LU z = Real.pi * Complex.I * z + 4 * (Real.log 2 : ℂ)
      + 4 * Complex.log (jacobiTheta₂ (z/2) z / 2) - 4 * Complex.log (thetaC00 z)
  rw [LU, thetaC10_div_exp]

/-! ## The chosen logarithm `Lfun` and its normalisation -/

/-- The chosen logarithm of `λ`, produced by `exists_L`. -/
noncomputable def Lfun : ℂ → ℂ := Classical.choose exists_L

lemma Lfun_spec : DifferentiableOn ℂ Lfun U ∧ (∀ z ∈ U, Complex.exp (Lfun z) = lamC z)
    ∧ (∀ z ∈ V, Lfun z = LU z) := Classical.choose_spec exists_L

/-- `Lfun` is given by the explicit branch `LU` on the whole half plane `{im z > 1/2}`. -/
lemma Lfun_eq_LU_on_W : ∀ z ∈ W, Lfun z = LU z := by
  obtain ⟨hfd, hexp, hV⟩ := Lfun_spec
  have hval : ∀ z ∈ W, ∃ n : ℤ, (Lfun - LU) z = n * (2 * Real.pi * Complex.I) := by
    intro z hz
    have hzU : z ∈ U := W_subset_U hz
    have h1 : Complex.exp ((Lfun - LU) z) = 1 := by
      rw [Pi.sub_apply, Complex.exp_sub, hexp z hzU, exp_LU_W z hz]
      exact div_self (lamC_ne_zero hzU)
    exact Complex.exp_eq_one_iff.mp h1
  have hcont : ContinuousOn (Lfun - LU) W :=
    (hfd.mono W_subset_U).continuousOn.sub continuousOn_LU_W
  have hconst := Work.Analysis.DiscreteValues.eq_const_of_isPreconnected isPreconnected_W hcont
    hval two_I_mem_W
  intro z hz
  have hzc := hconst z hz
  rw [Pi.sub_apply, Pi.sub_apply] at hzc
  have h0 : Lfun (2 * Complex.I) = LU (2 * Complex.I) :=
    hV _ (by simp only [V, Set.mem_ofPred_eq]; norm_num)
  rw [h0, sub_self] at hzc
  exact sub_eq_zero.mp hzc

end Work.Kernels.LogLambda
