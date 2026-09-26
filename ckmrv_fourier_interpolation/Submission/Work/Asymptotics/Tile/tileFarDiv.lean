import Mathlib
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.DeltaFun_imagAxis_lower_sharp
import Submission.Work.Asymptotics.E_jdiff_large

namespace Work.Asymptotics.Tile

open UpperHalfPlane ModularGroup
open scoped MatrixGroups UpperHalfPlane

noncomputable section

/-! ## Elementary constants -/

lemma expNegTwoPiLeHalfFar : Real.exp (-(2 * Real.pi)) ≤ 1 / 2 := by
  have h1 : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h2 : (2 : ℝ) ≤ (Real.exp 1) ^ 6 := by
    have h3 : (2.7 : ℝ) ^ 6 ≤ (Real.exp 1) ^ 6 :=
      pow_le_pow_left₀ (by norm_num) (le_of_lt h1) 6
    have h4 : (2 : ℝ) ≤ (2.7 : ℝ) ^ 6 := by norm_num
    linarith
  have h5 : (Real.exp 1) ^ 6 = Real.exp 6 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h6 : (6 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have h7 : (2 : ℝ) ≤ Real.exp (2 * Real.pi) := by
    have h8 := Real.exp_le_exp.mpr h6
    rw [h5] at h2
    linarith
  rw [Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le (by norm_num) h7

/-- `‖1 - e^{2πi((S • w) - i t)}‖ ≥ 1/2` for `w ∈ E`, `t ≥ 1`, `t ≤ Im (S • w) - 1`. -/
lemma oneSubExpGeHalfFar {w : UpperHalfPlane} {t : ℝ} (hw : w ∈ Work.Asymptotics.KEpsilon)
    (htle : t ≤ (ModularGroup.S • w).im - 1) :
    (1 : ℝ) / 2 ≤ ‖1 - Complex.exp (2 * Real.pi * Complex.I *
        ((((ModularGroup.S • w : UpperHalfPlane)) : ℂ) - ((t : ℂ) * Complex.I)))‖ := by
  set Z : ℂ := Complex.exp (2 * Real.pi * Complex.I *
    ((((ModularGroup.S • w : UpperHalfPlane)) : ℂ) - ((t : ℂ) * Complex.I))) with hZdef
  have hnorm : ‖Z‖ = Real.exp (-(2 * Real.pi * ((ModularGroup.S • w).im - t))) := by
    rw [hZdef, Complex.norm_exp]
    congr 1
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.sub_re, Complex.sub_im, UpperHalfPlane.coe_im,
      UpperHalfPlane.coe_re]
    norm_num
    try ring
  have hle : ‖Z‖ ≤ Real.exp (-(2 * Real.pi)) := by
    rw [hnorm]
    exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, htle])
  have hsub := norm_sub_norm_le (1 : ℂ) Z
  rw [norm_one, hnorm] at hsub
  linarith [expNegTwoPiLeHalfFar]

/-! ## The sharp divisor bound at the contour point `z = i t` -/

lemma divisorLowerSharpFar :
    ∃ c : ℝ, 0 < c ∧ ∀ (w : UpperHalfPlane) (t : ℝ) (ht : 0 < t),
      w ∈ Work.Asymptotics.KEpsilon → 1 ≤ t → t ≤ (ModularGroup.S • w).im - 1 →
      c * Real.exp (2 * Real.pi * ((ModularGroup.S • w).im - t))
        ≤ ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht) *
            (Work.Kernels.jInvariantFun w -
              Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht))‖ := by
  obtain ⟨c₀, hc₀, hJ⟩ := Work.Asymptotics.E_jdiff_large
  refine ⟨c₀ / 4, by positivity, fun w t ht hw ht1 htle => ?_⟩
  have hΔ : (1 : ℝ) / 2 * Real.exp (-(2 * Real.pi * t)) ≤
      ‖Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht)‖ :=
    Work.Asymptotics.DeltaFun_imagAxis_lower_sharp t ht ht1
  have hZ := oneSubExpGeHalfFar hw htle
  have hJ' : c₀ * Real.exp (2 * Real.pi * (ModularGroup.S • w).im) * (1 / 2) ≤
      ‖Work.Kernels.jInvariantFun w -
        Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)‖ := by
    have h := hJ w t ht hw ht1
    have hc : (0 : ℝ) ≤ c₀ * Real.exp (2 * Real.pi * (ModularGroup.S • w).im) := by positivity
    calc c₀ * Real.exp (2 * Real.pi * (ModularGroup.S • w).im) * (1 / 2)
        ≤ c₀ * Real.exp (2 * Real.pi * (ModularGroup.S • w).im) *
            ‖1 - Complex.exp (2 * Real.pi * Complex.I *
              ((((ModularGroup.S • w : UpperHalfPlane)) : ℂ) - ((t : ℂ) * Complex.I)))‖ :=
          mul_le_mul_of_nonneg_left hZ hc
      _ ≤ ‖Work.Kernels.jInvariantFun w -
            Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)‖ := h
  have hprod := mul_le_mul hΔ hJ' (by positivity) (by positivity)
  rw [norm_mul]
  have hexp : (1 / 2 * Real.exp (-(2 * Real.pi * t))) *
        (c₀ * Real.exp (2 * Real.pi * (ModularGroup.S • w).im) * (1 / 2))
      = c₀ / 4 * Real.exp (2 * Real.pi * ((ModularGroup.S • w).im - t)) := by
    have h : Real.exp (-(2 * Real.pi * t)) * Real.exp (2 * Real.pi * (ModularGroup.S • w).im)
        = Real.exp (2 * Real.pi * ((ModularGroup.S • w).im - t)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [← h]; ring
  rw [← hexp]
  exact hprod

end

end Work.Asymptotics.Tile
