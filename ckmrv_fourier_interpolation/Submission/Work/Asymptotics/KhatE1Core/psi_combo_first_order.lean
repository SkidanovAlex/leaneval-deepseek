import Mathlib
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.Asymptotics.Compact.tailDefs
import Submission.Work.Asymptotics.ThetaQExp
import Submission.Work.Asymptotics.CuspL_eq
import Submission.Work.Asymptotics.LogLambdaData_L_eq_Lfun
import Submission.Work.Asymptotics.KhatE1.ratio_third_order
import Submission.Work.Asymptotics.thetaC00_second_order
import Submission.Work.Asymptotics.KhatE1.E1LS_eq_log
import Submission.Work.Asymptotics.KhatE1.E1funnel_UW_bounds
import Submission.Work.Residues.LamSExpansion
import Submission.Work.Residues.ThetaAux

set_option maxHeartbeats 800000

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

namespace Work.Asymptotics.KhatE1Core

noncomputable section

/-! ## Elementary funnel facts -/

/-- `e^{-2π} ≤ 1/350`. -/
private lemma exp_neg_two_pi_le_inv350 : Real.exp (-(2 * Real.pi)) ≤ 1 / 350 := by
  have h6 : (6 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have h1 : Real.exp 6 ≤ Real.exp (2 * Real.pi) := Real.exp_le_exp.mpr h6
  have h3 : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h4 : (2.7 : ℝ) ^ 6 ≤ (Real.exp 1) ^ 6 := pow_le_pow_left₀ (by norm_num) h3.le 6
  have h2 : Real.exp 6 = (Real.exp 1) ^ 6 := by
    rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) * 1 by norm_num, Real.exp_nat_mul]
  have h5 : (350 : ℝ) ≤ Real.exp (2 * Real.pi) := by
    rw [h2] at h1
    nlinarith [h1, h4, (by norm_num : (350 : ℝ) ≤ 2.7 ^ 6)]
  rw [Real.exp_neg, inv_eq_one_div]
  exact one_div_le_one_div_of_le (by norm_num) h5

/-- `e^{-π} ≤ 1/8`. -/
private lemma exp_neg_pi_le_eighth' : Real.exp (-Real.pi) ≤ 1 / 8 := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := le_of_lt Real.exp_one_gt_two
  have h3e : (8 : ℝ) ≤ Real.exp 3 := by
    rw [show (3 : ℝ) = 1 + 1 + 1 by norm_num, Real.exp_add, Real.exp_add]
    nlinarith [h2, Real.exp_pos 1]
  have h3 : (3 : ℝ) ≤ Real.pi := le_of_lt Real.pi_gt_three
  have hπ : (8 : ℝ) ≤ Real.exp Real.pi := h3e.trans (Real.exp_le_exp.mpr h3)
  calc Real.exp (-Real.pi) = (Real.exp Real.pi)⁻¹ := Real.exp_neg _
    _ ≤ (8 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hπ
    _ = 1 / 8 := by norm_num

/-- `‖nomeE τ‖ = e^{-π Im τ}`. -/
private lemma norm_nomeE_eq (τ : UpperHalfPlane) :
    ‖Work.Asymptotics.nomeE τ‖ = Real.exp (-(Real.pi * τ.im)) := by
  rw [Work.Asymptotics.nomeE_def, Complex.norm_exp]
  congr 1
  rw [show (Real.pi : ℂ) * Complex.I * (τ : ℂ)
      = ((Real.pi : ℝ) : ℂ) * (Complex.I * (τ : ℂ)) by ring,
    Complex.re_ofReal_mul, Complex.I_mul_re, UpperHalfPlane.coe_im]
  ring

/-- On the funnel, `‖nomeE τ‖ ≤ 1/350`. -/
private lemma nomeE_norm_le_funnel {τ : UpperHalfPlane} (hτ : Work.Asymptotics.Funnel τ) :
    ‖Work.Asymptotics.nomeE τ‖ ≤ 1 / 350 := by
  rw [norm_nomeE_eq]
  exact le_trans (Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, hτ.2]))
    exp_neg_two_pi_le_inv350

/-- On the funnel, `tpar τ = ‖nomeE τ‖`. -/
private lemma tpar_eq_norm_nomeE (τ : UpperHalfPlane) :
    Work.Residues.tpar τ = ‖Work.Asymptotics.nomeE τ‖ := by
  rw [Work.Residues.tpar]
  exact (norm_nomeE_eq τ).symm

/-! ## The `τ`-atom combination `2ξ₂ + ξ₄` -/

/-- The combination `2ξ₂ + ξ₄ = 2(U+W) + (U²+W²-2V²)` equals `6 - 192 e²` up to `O(‖e‖³)`. -/
private lemma psiW_expansion :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : UpperHalfPlane, Work.Asymptotics.Funnel τ →
      ‖2 * (Work.Kernels.UFun τ + Work.Kernels.WFun τ)
          + (Work.Kernels.UFun τ ^ 2 + Work.Kernels.WFun τ ^ 2
              - 2 * Work.Kernels.VFun τ ^ 2)
          - (6 - 192 * Work.Asymptotics.nomeE τ ^ 2)‖
        ≤ C * ‖Work.Asymptotics.nomeE τ‖ ^ 4 := by
  refine ⟨300000, by norm_num, fun τ hτ => ?_⟩
  set e : ℂ := Work.Asymptotics.nomeE τ with he
  have hen : ‖e‖ ≤ 1 / 350 := by rw [he]; exact nomeE_norm_le_funnel hτ
  have he1 : ‖e‖ ≤ 1 := le_trans hen (by norm_num)
  have hx5 : ‖e‖ ^ 5 ≤ (1 / 350 : ℝ) ^ 5 := pow_le_pow_left₀ (norm_nonneg e) hen 5
  -- the three `q`-expansions
  have hτ2 : 2 ≤ τ.im := hτ.2
  have hU := Work.Asymptotics.UFun_qexp τ hτ2
  have hW := Work.Asymptotics.WFun_qexp τ hτ2
  have hV := Work.Asymptotics.VFun_qexp τ hτ2
  rw [← he] at hU hW hV
  -- bounding `U`, `W`, `V`
  obtain ⟨hUb, hWb⟩ := Work.Asymptotics.KhatE1.E1funnel_UW_bounds τ hτ
  have ht : Work.Residues.tpar τ = ‖e‖ := by rw [tpar_eq_norm_nomeE, he]
  have hUb' : ‖Work.Kernels.UFun τ - 1‖ ≤ 40 * ‖e‖ := by rw [ht] at hUb; exact hUb
  have hWb' : ‖Work.Kernels.WFun τ - 1‖ ≤ 40 * ‖e‖ := by rw [ht] at hWb; exact hWb
  have hUnorm : ‖Work.Kernels.UFun τ‖ ≤ 1 + 40 * ‖e‖ := by
    have h1 : ‖Work.Kernels.UFun τ‖ ≤ ‖Work.Kernels.UFun τ - 1‖ + ‖(1 : ℂ)‖ := by
      simpa using norm_add_le (Work.Kernels.UFun τ - 1) (1 : ℂ)
    rw [norm_one] at h1
    linarith [h1, hUb']
  have hWnorm : ‖Work.Kernels.WFun τ‖ ≤ 1 + 40 * ‖e‖ := by
    have h1 : ‖Work.Kernels.WFun τ‖ ≤ ‖Work.Kernels.WFun τ - 1‖ + ‖(1 : ℂ)‖ := by
      simpa using norm_add_le (Work.Kernels.WFun τ - 1) (1 : ℂ)
    rw [norm_one] at h1
    linarith [h1, hWb']
  have hVnorm : ‖Work.Kernels.VFun τ‖ ≤ 2 + 80 * ‖e‖ := by
    have hq : Work.Kernels.VFun τ = Work.Kernels.UFun τ - Work.Kernels.WFun τ := by
      have h := Work.Kernels.TildeFacts.theta_quartic τ
      rw [h]; ring
    rw [hq]
    have := norm_sub_le (Work.Kernels.UFun τ) (Work.Kernels.WFun τ)
    linarith
  -- the truncated polynomials
  set PUn : ℂ := 1 + 8 * e + 24 * e ^ 2 + 32 * e ^ 3 + 24 * e ^ 4 with hPUn
  set PWn : ℂ := 1 - 8 * e + 24 * e ^ 2 - 32 * e ^ 3 + 24 * e ^ 4 with hPWn
  set PVn : ℂ := 16 * e + 64 * e ^ 3 with hPVn
  have hα : ‖Work.Kernels.UFun τ - PUn‖ ≤ 10000 * ‖e‖ ^ 5 := by rw [hPUn]; exact hU
  have hβ : ‖Work.Kernels.WFun τ - PWn‖ ≤ 10000 * ‖e‖ ^ 5 := by rw [hPWn]; exact hW
  have hγ : ‖Work.Kernels.VFun τ - PVn‖ ≤ 10000 * ‖e‖ ^ 5 := by rw [hPVn]; exact hV
  -- the two auxiliary norms
  have hUplus : ‖Work.Kernels.UFun τ + PUn‖ ≤ 4 := by
    have hsplit : Work.Kernels.UFun τ + PUn
        = 2 * Work.Kernels.UFun τ - (Work.Kernels.UFun τ - PUn) := by ring
    rw [hsplit]
    have h1 := norm_sub_le (2 * Work.Kernels.UFun τ) (Work.Kernels.UFun τ - PUn)
    rw [norm_mul, Complex.norm_ofNat] at h1
    have hval : (2 : ℝ) * (1 + 40 * (1 / 350)) + 10000 * ((1 / 350 : ℝ) ^ 5) < 4 := by
      norm_num
    linarith [h1, hα, hUnorm, hen, hx5, hval]
  have hWplus : ‖Work.Kernels.WFun τ + PWn‖ ≤ 4 := by
    have hsplit : Work.Kernels.WFun τ + PWn
        = 2 * Work.Kernels.WFun τ - (Work.Kernels.WFun τ - PWn) := by ring
    rw [hsplit]
    have h1 := norm_sub_le (2 * Work.Kernels.WFun τ) (Work.Kernels.WFun τ - PWn)
    rw [norm_mul, Complex.norm_ofNat] at h1
    have hval : (2 : ℝ) * (1 + 40 * (1 / 350)) + 10000 * ((1 / 350 : ℝ) ^ 5) < 4 := by
      norm_num
    linarith [h1, hβ, hWnorm, hen, hx5, hval]
  have hVplus : ‖Work.Kernels.VFun τ + PVn‖ ≤ 8 := by
    have hsplit : Work.Kernels.VFun τ + PVn
        = 2 * Work.Kernels.VFun τ - (Work.Kernels.VFun τ - PVn) := by ring
    rw [hsplit]
    have h1 := norm_sub_le (2 * Work.Kernels.VFun τ) (Work.Kernels.VFun τ - PVn)
    rw [norm_mul, Complex.norm_ofNat] at h1
    have hval : (2 : ℝ) * (2 + 80 * (1 / 350)) + 10000 * ((1 / 350 : ℝ) ^ 5) < 8 := by
      norm_num
    linarith [h1, hγ, hVnorm, hen, hx5, hval]
  -- the exact algebraic split
  have hkey : 2 * (Work.Kernels.UFun τ + Work.Kernels.WFun τ)
        + (Work.Kernels.UFun τ ^ 2 + Work.Kernels.WFun τ ^ 2
            - 2 * Work.Kernels.VFun τ ^ 2) - (6 - 192 * e ^ 2)
      = (2 * (PUn + PWn) + (PUn ^ 2 + PWn ^ 2 - 2 * PVn ^ 2) - (6 - 192 * e ^ 2))
        + (2 * (Work.Kernels.UFun τ - PUn) + 2 * (Work.Kernels.WFun τ - PWn)
            + (Work.Kernels.UFun τ - PUn) * (Work.Kernels.UFun τ + PUn)
            + (Work.Kernels.WFun τ - PWn) * (Work.Kernels.WFun τ + PWn)
            - 2 * ((Work.Kernels.VFun τ - PVn) * (Work.Kernels.VFun τ + PVn))) := by
    ring
  have hpoly : 2 * (PUn + PWn) + (PUn ^ 2 + PWn ^ 2 - 2 * PVn ^ 2) - (6 - 192 * e ^ 2)
      = -1728 * e ^ 4 - 3840 * e ^ 6 + 1152 * e ^ 8 := by
    rw [hPUn, hPWn, hPVn]; ring
  have hpolybound : ‖-1728 * e ^ 4 - 3840 * e ^ 6 + 1152 * e ^ 8‖ ≤ 6720 * ‖e‖ ^ 4 := by
    have h2 : ‖(-1728 : ℂ) * e ^ 4‖ = 1728 * ‖e‖ ^ 4 := by
      rw [norm_mul, norm_pow]; norm_num
    have h3 : ‖(3840 : ℂ) * e ^ 6‖ = 3840 * ‖e‖ ^ 6 := by
      rw [norm_mul, norm_pow]; norm_num
    have h4 : ‖(1152 : ℂ) * e ^ 8‖ = 1152 * ‖e‖ ^ 8 := by
      rw [norm_mul, norm_pow]; norm_num
    have h1 : ‖-1728 * e ^ 4 - 3840 * e ^ 6 + 1152 * e ^ 8‖
        ≤ 1728 * ‖e‖ ^ 4 + 3840 * ‖e‖ ^ 6 + 1152 * ‖e‖ ^ 8 := by
      calc ‖-1728 * e ^ 4 - 3840 * e ^ 6 + 1152 * e ^ 8‖
          ≤ ‖-1728 * e ^ 4 - 3840 * e ^ 6‖ + ‖1152 * e ^ 8‖ := norm_add_le _ _
        _ ≤ (‖-1728 * e ^ 4‖ + ‖3840 * e ^ 6‖) + ‖1152 * e ^ 8‖ := by
              have hh := norm_sub_le ((-1728 : ℂ) * e ^ 4) ((3840 : ℂ) * e ^ 6)
              linarith
        _ = 1728 * ‖e‖ ^ 4 + 3840 * ‖e‖ ^ 6 + 1152 * ‖e‖ ^ 8 := by
              rw [h2, h3, h4]
              try ring
    have h6 : ‖e‖ ^ 6 ≤ ‖e‖ ^ 4 := pow_le_pow_of_le_one (norm_nonneg e) he1 (by norm_num)
    have h8 : ‖e‖ ^ 8 ≤ ‖e‖ ^ 4 := pow_le_pow_of_le_one (norm_nonneg e) he1 (by norm_num)
    nlinarith [h1, h6, h8]
  have herr : ‖(2 * (Work.Kernels.UFun τ - PUn) + 2 * (Work.Kernels.WFun τ - PWn)
            + (Work.Kernels.UFun τ - PUn) * (Work.Kernels.UFun τ + PUn)
            + (Work.Kernels.WFun τ - PWn) * (Work.Kernels.WFun τ + PWn)
            - 2 * ((Work.Kernels.VFun τ - PVn) * (Work.Kernels.VFun τ + PVn)))‖
      ≤ 280000 * ‖e‖ ^ 5 := by
    have h2α : ‖2 * (Work.Kernels.UFun τ - PUn)‖ ≤ 20000 * ‖e‖ ^ 5 := by
      rw [norm_mul, Complex.norm_ofNat]; linarith [hα]
    have h2β : ‖2 * (Work.Kernels.WFun τ - PWn)‖ ≤ 20000 * ‖e‖ ^ 5 := by
      rw [norm_mul, Complex.norm_ofNat]; linarith [hβ]
    have hαU : ‖(Work.Kernels.UFun τ - PUn) * (Work.Kernels.UFun τ + PUn)‖
        ≤ 40000 * ‖e‖ ^ 5 := by
      rw [norm_mul]
      have hh := mul_le_mul hα hUplus (norm_nonneg _) (by positivity)
      linarith [hh]
    have hβW : ‖(Work.Kernels.WFun τ - PWn) * (Work.Kernels.WFun τ + PWn)‖
        ≤ 40000 * ‖e‖ ^ 5 := by
      rw [norm_mul]
      have hh := mul_le_mul hβ hWplus (norm_nonneg _) (by positivity)
      linarith [hh]
    have h2γV : ‖2 * ((Work.Kernels.VFun τ - PVn) * (Work.Kernels.VFun τ + PVn))‖
        ≤ 160000 * ‖e‖ ^ 5 := by
      rw [norm_mul, Complex.norm_ofNat, norm_mul]
      have hh := mul_le_mul hγ hVplus (norm_nonneg _) (by positivity)
      linarith [hh]
    have hA := norm_sub_le (2 * (Work.Kernels.UFun τ - PUn) + 2 * (Work.Kernels.WFun τ - PWn)
        + (Work.Kernels.UFun τ - PUn) * (Work.Kernels.UFun τ + PUn)
        + (Work.Kernels.WFun τ - PWn) * (Work.Kernels.WFun τ + PWn))
        (2 * ((Work.Kernels.VFun τ - PVn) * (Work.Kernels.VFun τ + PVn)))
    have hB := norm_add_le (2 * (Work.Kernels.UFun τ - PUn) + 2 * (Work.Kernels.WFun τ - PWn)
        + (Work.Kernels.UFun τ - PUn) * (Work.Kernels.UFun τ + PUn))
        ((Work.Kernels.WFun τ - PWn) * (Work.Kernels.WFun τ + PWn))
    have hC := norm_add_le (2 * (Work.Kernels.UFun τ - PUn) + 2 * (Work.Kernels.WFun τ - PWn))
        ((Work.Kernels.UFun τ - PUn) * (Work.Kernels.UFun τ + PUn))
    have hD := norm_add_le (2 * (Work.Kernels.UFun τ - PUn)) (2 * (Work.Kernels.WFun τ - PWn))
    linarith
  have hmain : ‖(2 * (PUn + PWn) + (PUn ^ 2 + PWn ^ 2 - 2 * PVn ^ 2) - (6 - 192 * e ^ 2))
        + (2 * (Work.Kernels.UFun τ - PUn) + 2 * (Work.Kernels.WFun τ - PWn)
            + (Work.Kernels.UFun τ - PUn) * (Work.Kernels.UFun τ + PUn)
            + (Work.Kernels.WFun τ - PWn) * (Work.Kernels.WFun τ + PWn)
            - 2 * ((Work.Kernels.VFun τ - PVn) * (Work.Kernels.VFun τ + PVn)))‖
      ≤ 6720 * ‖e‖ ^ 4 + 280000 * ‖e‖ ^ 5 := by
    rw [hpoly]
    exact le_trans (norm_add_le _ _) (add_le_add hpolybound herr)
  calc ‖2 * (Work.Kernels.UFun τ + Work.Kernels.WFun τ)
        + (Work.Kernels.UFun τ ^ 2 + Work.Kernels.WFun τ ^ 2
            - 2 * Work.Kernels.VFun τ ^ 2) - (6 - 192 * e ^ 2)‖
      = ‖(2 * (PUn + PWn) + (PUn ^ 2 + PWn ^ 2 - 2 * PVn ^ 2) - (6 - 192 * e ^ 2))
        + (2 * (Work.Kernels.UFun τ - PUn) + 2 * (Work.Kernels.WFun τ - PWn)
            + (Work.Kernels.UFun τ - PUn) * (Work.Kernels.UFun τ + PUn)
            + (Work.Kernels.WFun τ - PWn) * (Work.Kernels.WFun τ + PWn)
            - 2 * ((Work.Kernels.VFun τ - PVn) * (Work.Kernels.VFun τ + PVn)))‖ := by
          rw [hkey]
    _ ≤ 6720 * ‖e‖ ^ 4 + 280000 * ‖e‖ ^ 5 := hmain
    _ ≤ 300000 * ‖e‖ ^ 4 := by
          have h5 : ‖e‖ ^ 5 ≤ ‖e‖ ^ 4 := pow_le_pow_of_le_one (norm_nonneg e) he1 (by norm_num)
          have h4 : (0 : ℝ) ≤ ‖e‖ ^ 4 := by positivity
          linarith

/-! ## The `τ`-atom combination `2(ξ₂|₂S) + (ξ₄|₄S)` -/

/-- The combination `-2(U+V) + (U²+V²-2W²)` equals `-3 + 96 e² + 1152 e³` up to `O(‖e‖⁴)`. -/
private lemma psiZ_expansion :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : UpperHalfPlane, Work.Asymptotics.Funnel τ →
      ‖-2 * (Work.Kernels.UFun τ + Work.Kernels.VFun τ)
          + (Work.Kernels.UFun τ ^ 2 + Work.Kernels.VFun τ ^ 2
              - 2 * Work.Kernels.WFun τ ^ 2)
          - (-3 + 96 * Work.Asymptotics.nomeE τ ^ 2
              + 1152 * Work.Asymptotics.nomeE τ ^ 3)‖
        ≤ C * ‖Work.Asymptotics.nomeE τ‖ ^ 4 := by
  refine ⟨300000, by norm_num, fun τ hτ => ?_⟩
  set e : ℂ := Work.Asymptotics.nomeE τ with he
  have hen : ‖e‖ ≤ 1 / 350 := by rw [he]; exact nomeE_norm_le_funnel hτ
  have he1 : ‖e‖ ≤ 1 := le_trans hen (by norm_num)
  have hx5 : ‖e‖ ^ 5 ≤ (1 / 350 : ℝ) ^ 5 := pow_le_pow_left₀ (norm_nonneg e) hen 5
  have hτ2 : 2 ≤ τ.im := hτ.2
  have hU := Work.Asymptotics.UFun_qexp τ hτ2
  have hW := Work.Asymptotics.WFun_qexp τ hτ2
  have hV := Work.Asymptotics.VFun_qexp τ hτ2
  rw [← he] at hU hW hV
  obtain ⟨hUb, hWb⟩ := Work.Asymptotics.KhatE1.E1funnel_UW_bounds τ hτ
  have ht : Work.Residues.tpar τ = ‖e‖ := by rw [tpar_eq_norm_nomeE, he]
  have hUb' : ‖Work.Kernels.UFun τ - 1‖ ≤ 40 * ‖e‖ := by rw [ht] at hUb; exact hUb
  have hWb' : ‖Work.Kernels.WFun τ - 1‖ ≤ 40 * ‖e‖ := by rw [ht] at hWb; exact hWb
  have hUnorm : ‖Work.Kernels.UFun τ‖ ≤ 1 + 40 * ‖e‖ := by
    have h1 : ‖Work.Kernels.UFun τ‖ ≤ ‖Work.Kernels.UFun τ - 1‖ + ‖(1 : ℂ)‖ := by
      simpa using norm_add_le (Work.Kernels.UFun τ - 1) (1 : ℂ)
    rw [norm_one] at h1
    linarith [h1, hUb']
  have hWnorm : ‖Work.Kernels.WFun τ‖ ≤ 1 + 40 * ‖e‖ := by
    have h1 : ‖Work.Kernels.WFun τ‖ ≤ ‖Work.Kernels.WFun τ - 1‖ + ‖(1 : ℂ)‖ := by
      simpa using norm_add_le (Work.Kernels.WFun τ - 1) (1 : ℂ)
    rw [norm_one] at h1
    linarith [h1, hWb']
  have hVnorm : ‖Work.Kernels.VFun τ‖ ≤ 2 + 80 * ‖e‖ := by
    have hq : Work.Kernels.VFun τ = Work.Kernels.UFun τ - Work.Kernels.WFun τ := by
      have h := Work.Kernels.TildeFacts.theta_quartic τ
      rw [h]; ring
    rw [hq]
    have := norm_sub_le (Work.Kernels.UFun τ) (Work.Kernels.WFun τ)
    linarith
  set PUn : ℂ := 1 + 8 * e + 24 * e ^ 2 + 32 * e ^ 3 + 24 * e ^ 4 with hPUn
  set PWn : ℂ := 1 - 8 * e + 24 * e ^ 2 - 32 * e ^ 3 + 24 * e ^ 4 with hPWn
  set PVn : ℂ := 16 * e + 64 * e ^ 3 with hPVn
  have hα : ‖Work.Kernels.UFun τ - PUn‖ ≤ 10000 * ‖e‖ ^ 5 := by rw [hPUn]; exact hU
  have hβ : ‖Work.Kernels.WFun τ - PWn‖ ≤ 10000 * ‖e‖ ^ 5 := by rw [hPWn]; exact hW
  have hγ : ‖Work.Kernels.VFun τ - PVn‖ ≤ 10000 * ‖e‖ ^ 5 := by rw [hPVn]; exact hV
  have hUplus : ‖Work.Kernels.UFun τ + PUn‖ ≤ 4 := by
    have hsplit : Work.Kernels.UFun τ + PUn
        = 2 * Work.Kernels.UFun τ - (Work.Kernels.UFun τ - PUn) := by ring
    rw [hsplit]
    have h1 := norm_sub_le (2 * Work.Kernels.UFun τ) (Work.Kernels.UFun τ - PUn)
    rw [norm_mul, Complex.norm_ofNat] at h1
    have hval : (2 : ℝ) * (1 + 40 * (1 / 350)) + 10000 * ((1 / 350 : ℝ) ^ 5) < 4 := by
      norm_num
    linarith [h1, hα, hUnorm, hen, hx5, hval]
  have hWplus : ‖Work.Kernels.WFun τ + PWn‖ ≤ 4 := by
    have hsplit : Work.Kernels.WFun τ + PWn
        = 2 * Work.Kernels.WFun τ - (Work.Kernels.WFun τ - PWn) := by ring
    rw [hsplit]
    have h1 := norm_sub_le (2 * Work.Kernels.WFun τ) (Work.Kernels.WFun τ - PWn)
    rw [norm_mul, Complex.norm_ofNat] at h1
    have hval : (2 : ℝ) * (1 + 40 * (1 / 350)) + 10000 * ((1 / 350 : ℝ) ^ 5) < 4 := by
      norm_num
    linarith [h1, hβ, hWnorm, hen, hx5, hval]
  have hVplus : ‖Work.Kernels.VFun τ + PVn‖ ≤ 8 := by
    have hsplit : Work.Kernels.VFun τ + PVn
        = 2 * Work.Kernels.VFun τ - (Work.Kernels.VFun τ - PVn) := by ring
    rw [hsplit]
    have h1 := norm_sub_le (2 * Work.Kernels.VFun τ) (Work.Kernels.VFun τ - PVn)
    rw [norm_mul, Complex.norm_ofNat] at h1
    have hval : (2 : ℝ) * (2 + 80 * (1 / 350)) + 10000 * ((1 / 350 : ℝ) ^ 5) < 8 := by
      norm_num
    linarith [h1, hγ, hVnorm, hen, hx5, hval]
  have hkey : -2 * (Work.Kernels.UFun τ + Work.Kernels.VFun τ)
        + (Work.Kernels.UFun τ ^ 2 + Work.Kernels.VFun τ ^ 2
            - 2 * Work.Kernels.WFun τ ^ 2)
        - (-3 + 96 * e ^ 2 + 1152 * e ^ 3)
      = (-2 * (PUn + PVn) + (PUn ^ 2 + PVn ^ 2 - 2 * PWn ^ 2)
            - (-3 + 96 * e ^ 2 + 1152 * e ^ 3))
        + ((-2) * (Work.Kernels.UFun τ - PUn) + (-2) * (Work.Kernels.VFun τ - PVn)
            + (Work.Kernels.UFun τ - PUn) * (Work.Kernels.UFun τ + PUn)
            + (Work.Kernels.VFun τ - PVn) * (Work.Kernels.VFun τ + PVn)
            - 2 * ((Work.Kernels.WFun τ - PWn) * (Work.Kernels.WFun τ + PWn))) := by
    ring
  have hpoly : -2 * (PUn + PVn) + (PUn ^ 2 + PVn ^ 2 - 2 * PWn ^ 2)
        - (-3 + 96 * e ^ 2 + 1152 * e ^ 3)
      = 864 * e ^ 4 + 5760 * e ^ 5 + 1920 * e ^ 6 + 4608 * e ^ 7 - 576 * e ^ 8 := by
    rw [hPUn, hPWn, hPVn]; ring
  have hpolybound : ‖864 * e ^ 4 + 5760 * e ^ 5 + 1920 * e ^ 6 + 4608 * e ^ 7 - 576 * e ^ 8‖
      ≤ 14000 * ‖e‖ ^ 4 := by
    have h1 : ‖864 * e ^ 4 + 5760 * e ^ 5 + 1920 * e ^ 6 + 4608 * e ^ 7 - 576 * e ^ 8‖
        ≤ 864 * ‖e‖ ^ 4 + 5760 * ‖e‖ ^ 5 + 1920 * ‖e‖ ^ 6 + 4608 * ‖e‖ ^ 7 + 576 * ‖e‖ ^ 8 := by
      have a := norm_sub_le (864 * e ^ 4 + 5760 * e ^ 5 + 1920 * e ^ 6 + 4608 * e ^ 7)
        (576 * e ^ 8)
      have b := norm_add_le (864 * e ^ 4 + 5760 * e ^ 5 + 1920 * e ^ 6) (4608 * e ^ 7)
      have c := norm_add_le (864 * e ^ 4 + 5760 * e ^ 5) (1920 * e ^ 6)
      have d := norm_add_le (864 * e ^ 4) (5760 * e ^ 5)
      have e4 : ‖864 * e ^ 4‖ = 864 * ‖e‖ ^ 4 := by rw [norm_mul, norm_pow]; norm_num
      have e5 : ‖5760 * e ^ 5‖ = 5760 * ‖e‖ ^ 5 := by rw [norm_mul, norm_pow]; norm_num
      have e6 : ‖1920 * e ^ 6‖ = 1920 * ‖e‖ ^ 6 := by rw [norm_mul, norm_pow]; norm_num
      have e7 : ‖4608 * e ^ 7‖ = 4608 * ‖e‖ ^ 7 := by rw [norm_mul, norm_pow]; norm_num
      have e8 : ‖576 * e ^ 8‖ = 576 * ‖e‖ ^ 8 := by rw [norm_mul, norm_pow]; norm_num
      linarith
    have h6 : ‖e‖ ^ 6 ≤ ‖e‖ ^ 4 := pow_le_pow_of_le_one (norm_nonneg e) he1 (by norm_num)
    have h5 : ‖e‖ ^ 5 ≤ ‖e‖ ^ 4 := pow_le_pow_of_le_one (norm_nonneg e) he1 (by norm_num)
    have h7 : ‖e‖ ^ 7 ≤ ‖e‖ ^ 4 := pow_le_pow_of_le_one (norm_nonneg e) he1 (by norm_num)
    have h8 : ‖e‖ ^ 8 ≤ ‖e‖ ^ 4 := pow_le_pow_of_le_one (norm_nonneg e) he1 (by norm_num)
    nlinarith [h1, h5, h6, h7, h8]
  have herr : ‖(-2) * (Work.Kernels.UFun τ - PUn) + (-2) * (Work.Kernels.VFun τ - PVn)
            + (Work.Kernels.UFun τ - PUn) * (Work.Kernels.UFun τ + PUn)
            + (Work.Kernels.VFun τ - PVn) * (Work.Kernels.VFun τ + PVn)
            - 2 * ((Work.Kernels.WFun τ - PWn) * (Work.Kernels.WFun τ + PWn))‖
      ≤ 240000 * ‖e‖ ^ 5 := by
    have hα' : ‖(-2) * (Work.Kernels.UFun τ - PUn)‖ ≤ 20000 * ‖e‖ ^ 5 := by
      rw [norm_mul]
      have h2 : ‖(-2 : ℂ)‖ = 2 := by norm_num
      rw [h2]
      linarith [hα]
    have hγ' : ‖(-2) * (Work.Kernels.VFun τ - PVn)‖ ≤ 20000 * ‖e‖ ^ 5 := by
      rw [norm_mul]
      have h2 : ‖(-2 : ℂ)‖ = 2 := by norm_num
      rw [h2]
      linarith [hγ]
    have hαU : ‖(Work.Kernels.UFun τ - PUn) * (Work.Kernels.UFun τ + PUn)‖
        ≤ 40000 * ‖e‖ ^ 5 := by
      rw [norm_mul]
      have hh := mul_le_mul hα hUplus (norm_nonneg _) (by positivity)
      linarith [hh]
    have hγV : ‖(Work.Kernels.VFun τ - PVn) * (Work.Kernels.VFun τ + PVn)‖
        ≤ 80000 * ‖e‖ ^ 5 := by
      rw [norm_mul]
      have hh := mul_le_mul hγ hVplus (norm_nonneg _) (by positivity)
      linarith [hh]
    have h2βW : ‖2 * ((Work.Kernels.WFun τ - PWn) * (Work.Kernels.WFun τ + PWn))‖
        ≤ 80000 * ‖e‖ ^ 5 := by
      rw [norm_mul, Complex.norm_ofNat, norm_mul]
      have hh := mul_le_mul hβ hWplus (norm_nonneg _) (by positivity)
      linarith [hh]
    have hA := norm_sub_le ((-2) * (Work.Kernels.UFun τ - PUn) + (-2) * (Work.Kernels.VFun τ - PVn)
        + (Work.Kernels.UFun τ - PUn) * (Work.Kernels.UFun τ + PUn)
        + (Work.Kernels.VFun τ - PVn) * (Work.Kernels.VFun τ + PVn))
        (2 * ((Work.Kernels.WFun τ - PWn) * (Work.Kernels.WFun τ + PWn)))
    have hB := norm_add_le ((-2) * (Work.Kernels.UFun τ - PUn) + (-2) * (Work.Kernels.VFun τ - PVn)
        + (Work.Kernels.UFun τ - PUn) * (Work.Kernels.UFun τ + PUn))
        ((Work.Kernels.VFun τ - PVn) * (Work.Kernels.VFun τ + PVn))
    have hC := norm_add_le ((-2) * (Work.Kernels.UFun τ - PUn) + (-2) * (Work.Kernels.VFun τ - PVn))
        ((Work.Kernels.UFun τ - PUn) * (Work.Kernels.UFun τ + PUn))
    have hD := norm_add_le ((-2) * (Work.Kernels.UFun τ - PUn)) ((-2) * (Work.Kernels.VFun τ - PVn))
    linarith
  have hmain : ‖(-2 * (PUn + PVn) + (PUn ^ 2 + PVn ^ 2 - 2 * PWn ^ 2)
            - (-3 + 96 * e ^ 2 + 1152 * e ^ 3))
        + ((-2) * (Work.Kernels.UFun τ - PUn) + (-2) * (Work.Kernels.VFun τ - PVn)
            + (Work.Kernels.UFun τ - PUn) * (Work.Kernels.UFun τ + PUn)
            + (Work.Kernels.VFun τ - PVn) * (Work.Kernels.VFun τ + PVn)
            - 2 * ((Work.Kernels.WFun τ - PWn) * (Work.Kernels.WFun τ + PWn)))‖
      ≤ 14000 * ‖e‖ ^ 4 + 240000 * ‖e‖ ^ 5 := by
    rw [hpoly]
    exact le_trans (norm_add_le _ _) (add_le_add hpolybound herr)
  calc ‖-2 * (Work.Kernels.UFun τ + Work.Kernels.VFun τ)
        + (Work.Kernels.UFun τ ^ 2 + Work.Kernels.VFun τ ^ 2
            - 2 * Work.Kernels.WFun τ ^ 2)
        - (-3 + 96 * e ^ 2 + 1152 * e ^ 3)‖
      = ‖(-2 * (PUn + PVn) + (PUn ^ 2 + PVn ^ 2 - 2 * PWn ^ 2)
            - (-3 + 96 * e ^ 2 + 1152 * e ^ 3))
        + ((-2) * (Work.Kernels.UFun τ - PUn) + (-2) * (Work.Kernels.VFun τ - PVn)
            + (Work.Kernels.UFun τ - PUn) * (Work.Kernels.UFun τ + PUn)
            + (Work.Kernels.VFun τ - PVn) * (Work.Kernels.VFun τ + PVn)
            - 2 * ((Work.Kernels.WFun τ - PWn) * (Work.Kernels.WFun τ + PWn)))‖ := by
          rw [hkey]
    _ ≤ 14000 * ‖e‖ ^ 4 + 240000 * ‖e‖ ^ 5 := hmain
    _ ≤ 300000 * ‖e‖ ^ 4 := by
          have h5 : ‖e‖ ^ 5 ≤ ‖e‖ ^ 4 := pow_le_pow_of_le_one (norm_nonneg e) he1 (by norm_num)
          have h4 : (0 : ℝ) ≤ ‖e‖ ^ 4 := by positivity
          linarith

/-! ## The third-order cusp expansion of `𝓛_S` -/

/-- `log(1+z) = z - z²/2 + z³/3 + O(‖z‖⁴)` for `‖z‖ ≤ 1/2`, with constant `1/2`. -/
private lemma log_taylor_remainder3 (z : ℂ) (hz : ‖z‖ ≤ 1 / 2) :
    ‖Complex.log (1 + z) - (z - z ^ 2 / 2 + z ^ 3 / 3)‖ ≤ (1 / 2) * ‖z‖ ^ 4 := by
  have hz1 : ‖z‖ < 1 := by linarith
  have h := Complex.norm_log_sub_logTaylor_le 3 hz1
  have hlt : Complex.logTaylor 4 z = z - z ^ 2 / 2 + z ^ 3 / 3 := by
    simp only [Complex.logTaylor, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    norm_num
    ring
  rw [hlt] at h
  have h2 : (1 - ‖z‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have hpos : 0 ≤ ‖z‖ ^ 4 := by positivity
  have hstep : ‖z‖ ^ 4 * (1 - ‖z‖)⁻¹ / ((↑(3 : ℕ) : ℝ) + 1) ≤ (1 / 2) * ‖z‖ ^ 4 := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < (↑(3 : ℕ) : ℝ) + 1)]
    nlinarith [h2, hpos]
  calc ‖Complex.log (1 + z) - (z - z ^ 2 / 2 + z ^ 3 / 3)‖
      ≤ ‖z‖ ^ (3 + 1) * (1 - ‖z‖)⁻¹ / ((↑(3 : ℕ) : ℝ) + 1) := h
    _ = ‖z‖ ^ 4 * (1 - ‖z‖)⁻¹ / ((↑(3 : ℕ) : ℝ) + 1) := by norm_num
    _ ≤ (1 / 2) * ‖z‖ ^ 4 := hstep

/-- **Third-order abstract expansion step.**  If `a + 2q` and `b - 2q` are both `O(‖q‖⁴)`
(with `‖q‖ = r ≤ 1/8`, constant `M ≤ 4`), then
`log(1+a) - log(1+b) + 4q + (16/3)q³ = O(r⁴)` with the explicit constant `1000`. -/
private lemma log_expansion_step3 {a b q : ℂ} {M r : ℝ}
    (hM : 0 < M) (hM4 : M ≤ 4) (hr0 : 0 ≤ r) (hr : ‖q‖ ≤ r) (hr8 : r ≤ 1 / 8)
    (ha : ‖a + 2 * q‖ ≤ M * r ^ 4) (hb : ‖b - 2 * q‖ ≤ M * r ^ 4) :
    ‖Complex.log (1 + a) - Complex.log (1 + b) + 4 * q + (16 / 3 : ℂ) * q ^ 3‖
      ≤ 1000 * r ^ 4 := by
  have hr1 : r ≤ 1 := by linarith
  have hr4 : (0 : ℝ) ≤ r ^ 4 := by positivity
  have hMle : M * r ^ 4 ≤ 4 * r ^ 4 := mul_le_mul_of_nonneg_right hM4 hr4
  have h4r : 4 * r ^ 4 ≤ r := by nlinarith [pow_le_pow_left₀ hr0 hr8 3, hr0, sq_nonneg r]
  have h8r : 8 * r ^ 4 ≤ r := by nlinarith [pow_le_pow_left₀ hr0 hr8 3, hr0, sq_nonneg r]
  have hMr : M * r ^ 4 ≤ r := by linarith [hMle, h4r]
  have h2Mr : 2 * M * r ^ 4 ≤ r := by nlinarith [hMle, h8r]
  have hna : ‖a‖ ≤ 3 * r := by
    have h1 : ‖a‖ ≤ ‖a + 2 * q‖ + ‖2 * q‖ := by
      have h : ‖a‖ = ‖(a + 2 * q) - 2 * q‖ := by congr 1; ring
      rw [h]; exact norm_sub_le _ _
    have h2 : ‖(2 : ℂ) * q‖ = 2 * ‖q‖ := by rw [norm_mul]; norm_num
    rw [h2] at h1
    linarith [h1, ha, hMr, hr]
  have hnb : ‖b‖ ≤ 3 * r := by
    have h1 : ‖b‖ ≤ ‖b - 2 * q‖ + ‖2 * q‖ := by
      have h : ‖b‖ = ‖(b - 2 * q) + 2 * q‖ := by congr 1; ring
      rw [h]; exact norm_add_le _ _
    have h2 : ‖(2 : ℂ) * q‖ = 2 * ‖q‖ := by rw [norm_mul]; norm_num
    rw [h2] at h1
    linarith [h1, hb, hMr, hr]
  have hra := log_taylor_remainder3 a (by linarith : ‖a‖ ≤ 1 / 2)
  have hrb := log_taylor_remainder3 b (by linarith : ‖b‖ ≤ 1 / 2)
  have hra' : ‖Complex.log (1 + a) - (a - a ^ 2 / 2 + a ^ 3 / 3)‖ ≤ (81 / 2) * r ^ 4 := by
    refine le_trans hra ?_
    have h2 : (1 / 2) * ‖a‖ ^ 4 ≤ (1 / 2) * (3 * r) ^ 4 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg a) hna 4) (by norm_num)
    calc (1 / 2) * ‖a‖ ^ 4 ≤ (1 / 2) * (3 * r) ^ 4 := h2
      _ = (81 / 2) * r ^ 4 := by ring
  have hrb' : ‖Complex.log (1 + b) - (b - b ^ 2 / 2 + b ^ 3 / 3)‖ ≤ (81 / 2) * r ^ 4 := by
    refine le_trans hrb ?_
    have h2 : (1 / 2) * ‖b‖ ^ 4 ≤ (1 / 2) * (3 * r) ^ 4 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg b) hnb 4) (by norm_num)
    calc (1 / 2) * ‖b‖ ^ 4 ≤ (1 / 2) * (3 * r) ^ 4 := h2
      _ = (81 / 2) * r ^ 4 := by ring
  -- the difference of the truncated logarithms
  have hd1 : ‖a + 2 * q‖ ≤ 4 * r ^ 4 := le_trans ha hMle
  have hd2 : ‖b - 2 * q‖ ≤ 4 * r ^ 4 := le_trans hb hMle
  have hε : ‖(a + 2 * q) - (b - 2 * q)‖ ≤ 8 * r ^ 4 := by
    calc ‖(a + 2 * q) - (b - 2 * q)‖ ≤ ‖a + 2 * q‖ + ‖b - 2 * q‖ := norm_sub_le _ _
      _ ≤ 4 * r ^ 4 + 4 * r ^ 4 := add_le_add hd1 hd2
      _ = 8 * r ^ 4 := by ring
  have hζ : ‖(a + 2 * q) ^ 2 + (a + 2 * q) * (b - 2 * q) + (b - 2 * q) ^ 2‖ ≤ 48 * r ^ 8 := by
    have h1 : ‖(a + 2 * q) ^ 2‖ ≤ (4 * r ^ 4) ^ 2 := by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) hd1 2
    have h2 : ‖(a + 2 * q) * (b - 2 * q)‖ ≤ (4 * r ^ 4) * (4 * r ^ 4) := by
      rw [norm_mul]
      exact mul_le_mul hd1 hd2 (norm_nonneg _) (by positivity)
    have h3 : ‖(b - 2 * q) ^ 2‖ ≤ (4 * r ^ 4) ^ 2 := by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) hd2 2
    have htr : ‖(a + 2 * q) ^ 2 + (a + 2 * q) * (b - 2 * q) + (b - 2 * q) ^ 2‖
        ≤ ‖(a + 2 * q) ^ 2‖ + ‖(a + 2 * q) * (b - 2 * q)‖ + ‖(b - 2 * q) ^ 2‖ := by
      have hx := norm_add_le ((a + 2 * q) ^ 2 + (a + 2 * q) * (b - 2 * q)) ((b - 2 * q) ^ 2)
      have hy := norm_add_le ((a + 2 * q) ^ 2) ((a + 2 * q) * (b - 2 * q))
      linarith
    have h4 : (4 * r ^ 4) ^ 2 + (4 * r ^ 4) * (4 * r ^ 4) + (4 * r ^ 4) ^ 2 = 48 * r ^ 8 := by ring
    linarith [htr, h1, h2, h3, h4]
  have hr6 : r ^ 6 ≤ r ^ 4 := pow_le_pow_of_le_one hr0 hr1 (by norm_num)
  have hr9 : r ^ 9 ≤ r ^ 4 := pow_le_pow_of_le_one hr0 hr1 (by norm_num)
  have hr12 : r ^ 12 ≤ r ^ 4 := pow_le_pow_of_le_one hr0 hr1 (by norm_num)
  have hcube : ‖a ^ 3 - b ^ 3 + 16 * q ^ 3‖ ≤ 800 * r ^ 4 := by
    have hid : a ^ 3 - b ^ 3 + 16 * q ^ 3
        = 12 * q ^ 2 * ((a + 2 * q) - (b - 2 * q))
          - 4 * q * ((a + 2 * q) ^ 2 + (a + 2 * q) * (b - 2 * q) + (b - 2 * q) ^ 2)
          - 2 * q * ((a + 2 * q) - (b - 2 * q)) ^ 2
          + ((a + 2 * q) - (b - 2 * q))
              * ((a + 2 * q) ^ 2 + (a + 2 * q) * (b - 2 * q) + (b - 2 * q) ^ 2) := by
      ring
    rw [hid]
    have hT1 : ‖12 * q ^ 2 * ((a + 2 * q) - (b - 2 * q))‖ ≤ 12 * r ^ 2 * (8 * r ^ 4) := by
      have h12 : ‖(12 : ℂ)‖ = 12 := by norm_num
      rw [norm_mul, norm_mul, h12, norm_pow]
      have hq2 : ‖q‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg q) hr 2
      have h1 : 12 * ‖q‖ ^ 2 ≤ 12 * r ^ 2 := by linarith
      exact mul_le_mul h1 hε (norm_nonneg _) (by positivity)
    have hT2 : ‖4 * q * ((a + 2 * q) ^ 2 + (a + 2 * q) * (b - 2 * q) + (b - 2 * q) ^ 2)‖
        ≤ 4 * r * (48 * r ^ 8) := by
      rw [norm_mul, norm_mul, Complex.norm_ofNat]
      have h1 : 4 * ‖q‖ ≤ 4 * r := by linarith [norm_nonneg q]
      exact mul_le_mul h1 hζ (norm_nonneg _) (by positivity)
    have hT3 : ‖2 * q * ((a + 2 * q) - (b - 2 * q)) ^ 2‖ ≤ 2 * r * (8 * r ^ 4) ^ 2 := by
      rw [norm_mul, norm_mul, Complex.norm_ofNat, norm_pow]
      have h1 : 2 * ‖q‖ ≤ 2 * r := by linarith [norm_nonneg q]
      have h2 : ‖(a + 2 * q) - (b - 2 * q)‖ ^ 2 ≤ (8 * r ^ 4) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hε 2
      exact mul_le_mul h1 h2 (by positivity) (by positivity)
    have hT4 : ‖((a + 2 * q) - (b - 2 * q))
        * ((a + 2 * q) ^ 2 + (a + 2 * q) * (b - 2 * q) + (b - 2 * q) ^ 2)‖
        ≤ (8 * r ^ 4) * (48 * r ^ 8) := by
      rw [norm_mul]
      exact mul_le_mul hε hζ (norm_nonneg _) (by positivity)
    have hA := norm_add_le (12 * q ^ 2 * ((a + 2 * q) - (b - 2 * q))
        - 4 * q * ((a + 2 * q) ^ 2 + (a + 2 * q) * (b - 2 * q) + (b - 2 * q) ^ 2)
        - 2 * q * ((a + 2 * q) - (b - 2 * q)) ^ 2)
        (((a + 2 * q) - (b - 2 * q))
          * ((a + 2 * q) ^ 2 + (a + 2 * q) * (b - 2 * q) + (b - 2 * q) ^ 2))
    have hB := norm_sub_le (12 * q ^ 2 * ((a + 2 * q) - (b - 2 * q))
        - 4 * q * ((a + 2 * q) ^ 2 + (a + 2 * q) * (b - 2 * q) + (b - 2 * q) ^ 2))
        (2 * q * ((a + 2 * q) - (b - 2 * q)) ^ 2)
    have hC := norm_sub_le (12 * q ^ 2 * ((a + 2 * q) - (b - 2 * q)))
        (4 * q * ((a + 2 * q) ^ 2 + (a + 2 * q) * (b - 2 * q) + (b - 2 * q) ^ 2))
    have hpos4 : (0 : ℝ) ≤ r ^ 4 := hr4
    nlinarith [hA, hB, hC, hT1, hT2, hT3, hT4, hpos4, hr1, hr0, hr6, hr9, hr12]
  have hs : ‖(a - a ^ 2 / 2 + a ^ 3 / 3) - (b - b ^ 2 / 2 + b ^ 3 / 3)
        + 4 * q + (16 / 3 : ℂ) * q ^ 3‖ ≤ 400 * r ^ 4 := by
    have heq : (a - a ^ 2 / 2 + a ^ 3 / 3) - (b - b ^ 2 / 2 + b ^ 3 / 3) + 4 * q
          + (16 / 3 : ℂ) * q ^ 3
        = (a - b + 4 * q) - (a ^ 2 - b ^ 2) / 2 + (a ^ 3 - b ^ 3 + 16 * q ^ 3) / 3 := by
      ring
    rw [heq]
    have hab4q : ‖a - b + 4 * q‖ ≤ 8 * r ^ 4 := by
      have h1 : a - b + 4 * q = (a + 2 * q) - (b - 2 * q) := by ring
      rw [h1]; exact hε
    have hab : ‖a + b‖ ≤ 8 * r ^ 4 := by
      have h1 : a + b = (a + 2 * q) + (b - 2 * q) := by ring
      rw [h1]
      calc ‖(a + 2 * q) + (b - 2 * q)‖ ≤ ‖a + 2 * q‖ + ‖b - 2 * q‖ := norm_add_le _ _
        _ ≤ 4 * r ^ 4 + 4 * r ^ 4 := add_le_add hd1 hd2
        _ = 8 * r ^ 4 := by ring
    have habsq : ‖a - b‖ ≤ 5 * r := by
      have h1 : ‖a - b‖ ≤ ‖a - b + 4 * q‖ + ‖4 * q‖ := by
        have h : ‖a - b‖ = ‖(a - b + 4 * q) - 4 * q‖ := by congr 1; ring
        rw [h]; exact norm_sub_le _ _
      have h2 : ‖(4 : ℂ) * q‖ = 4 * ‖q‖ := by rw [norm_mul]; norm_num
      rw [h2] at h1
      linarith [h1, hab4q, hr, hr0]
    have hsq : ‖(a ^ 2 - b ^ 2) / 2‖ ≤ 20 * r ^ 4 := by
      rw [norm_div]
      have h1 : ‖a ^ 2 - b ^ 2‖ = ‖(a - b) * (a + b)‖ := by congr 1; ring
      rw [h1, norm_mul]
      have h2 : ‖a - b‖ * ‖a + b‖ ≤ (5 * r) * (8 * r ^ 4) :=
        mul_le_mul habsq hab (norm_nonneg _) (by positivity)
      norm_num
      nlinarith [h2, hr4]
    have hcube3 : ‖(a ^ 3 - b ^ 3 + 16 * q ^ 3) / 3‖ ≤ 300 * r ^ 4 := by
      rw [norm_div]
      have h3 : ‖(3 : ℂ)‖ = 3 := by norm_num
      rw [h3]
      have h2 : ‖a ^ 3 - b ^ 3 + 16 * q ^ 3‖ / 3 ≤ 800 * r ^ 4 / 3 := by
        rw [div_le_div_iff_of_pos_right (by norm_num : (0:ℝ) < 3)]
        exact hcube
      have h4 : 800 * r ^ 4 / 3 ≤ 300 * r ^ 4 := by
        rw [div_le_iff₀ (by norm_num : (0:ℝ) < 3)]
        nlinarith [hr4]
      linarith
    have h1 := norm_add_le ((a - b + 4 * q) - (a ^ 2 - b ^ 2) / 2) ((a ^ 3 - b ^ 3 + 16 * q ^ 3) / 3)
    have h1' := norm_sub_le (a - b + 4 * q) ((a ^ 2 - b ^ 2) / 2)
    linarith [h1, h1', hab4q, hsq, hcube3, hr4]
  have key : Complex.log (1 + a) - Complex.log (1 + b) + 4 * q + (16 / 3 : ℂ) * q ^ 3
      = (Complex.log (1 + a) - (a - a ^ 2 / 2 + a ^ 3 / 3))
        - (Complex.log (1 + b) - (b - b ^ 2 / 2 + b ^ 3 / 3))
        + ((a - a ^ 2 / 2 + a ^ 3 / 3) - (b - b ^ 2 / 2 + b ^ 3 / 3) + 4 * q
            + (16 / 3 : ℂ) * q ^ 3) := by ring
  rw [key]
  have h1 := norm_add_le ((Complex.log (1 + a) - (a - a ^ 2 / 2 + a ^ 3 / 3))
      - (Complex.log (1 + b) - (b - b ^ 2 / 2 + b ^ 3 / 3)))
      ((a - a ^ 2 / 2 + a ^ 3 / 3) - (b - b ^ 2 / 2 + b ^ 3 / 3) + 4 * q
        + (16 / 3 : ℂ) * q ^ 3)
  have h1' := norm_sub_le (Complex.log (1 + a) - (a - a ^ 2 / 2 + a ^ 3 / 3))
      (Complex.log (1 + b) - (b - b ^ 2 / 2 + b ^ 3 / 3))
  nlinarith [h1, h1', hra', hrb', hs, pow_nonneg hr0 4]

/-- `θ₀₁(τ) = 1 - 2E + O(‖E‖⁴)`. -/
private lemma theta01_second_order (τ : UpperHalfPlane) (hτ : 1 ≤ τ.im) :
    ‖Work.Kernels.theta01Fun τ - 1 + 2 * Work.Residues.Ept τ‖
      ≤ 4 * ‖Work.Residues.Ept τ‖ ^ 4 := by
  have hτ' : (1 : ℝ) ≤ ((τ : ℂ) + 1).im := by
    rw [Complex.add_im, Complex.one_im, UpperHalfPlane.coe_im]; linarith
  have h := Work.Asymptotics.thetaC00_second_order ((τ : ℂ) + 1) hτ'
  have he : Complex.exp (Real.pi * Complex.I * ((τ : ℂ) + 1)) = - Work.Residues.Ept τ := by
    rw [Work.Residues.Ept_apply,
      show Real.pi * Complex.I * ((τ : ℂ) + 1)
        = Real.pi * Complex.I * (τ : ℂ) + Real.pi * Complex.I by ring,
      Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  have ht : Work.Kernels.theta01Fun τ = jacobiTheta ((τ : ℂ) + 1) := by
    show jacobiTheta₂ (1 / 2) (τ : ℂ) = jacobiTheta ((τ : ℂ) + 1)
    rw [Work.Kernels.ClassicalFacts.jacobiTheta₂_half_eq_jacobiTheta_add_one]
  rw [show Work.Kernels.LogLambda.thetaC00 ((τ : ℂ) + 1) = jacobiTheta ((τ : ℂ) + 1) from rfl,
    he, norm_neg] at h
  have h' : ‖jacobiTheta ((τ : ℂ) + 1) - 1 + 2 * Work.Residues.Ept τ‖
      ≤ 4 * ‖Work.Residues.Ept τ‖ ^ 4 := by
    refine le_trans (le_of_eq ?_) h
    congr 1
    ring
  rw [ht]
  exact h' 

/-- **Third-order cusp expansion of `𝓛_S`.** -/
private lemma LS_cusp_third_order (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : UpperHalfPlane, Work.Asymptotics.Funnel τ →
      ‖ℓ.L_S τ + 16 * Work.Asymptotics.nomeE τ
          + (64 / 3 : ℂ) * Work.Asymptotics.nomeE τ ^ 3‖
        ≤ C * ‖Work.Asymptotics.nomeE τ‖ ^ 4 := by
  refine ⟨4000, by norm_num, fun τ hτ => ?_⟩
  have hhalf : (1 / 2 : ℝ) < τ.im :=
    lt_of_lt_of_le (by norm_num) (Work.Asymptotics.Funnel.im_one hτ)
  rw [show Work.Asymptotics.nomeE τ = Work.Residues.Ept τ from rfl]
  rw [Work.Residues.LogLambdaData_LS_eq_LamS ℓ τ hhalf]
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = ‖Work.Residues.Ept τ‖ := ⟨_, rfl⟩
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hr8 : r ≤ 1 / 8 := by
    rw [hr]
    exact (Work.Residues.norm_Ept_le_exp_neg_pi τ (Work.Asymptotics.Funnel.im_one hτ)).trans
      exp_neg_pi_le_eighth'
  have ha : ‖(Work.Kernels.theta01Fun τ - 1) + 2 * Work.Residues.Ept τ‖ ≤ 4 * r ^ 4 := by
    rw [hr]; exact theta01_second_order τ (Work.Asymptotics.Funnel.im_one hτ)
  have hb : ‖(Work.Kernels.theta00Fun τ - 1) - 2 * Work.Residues.Ept τ‖ ≤ 4 * r ^ 4 := by
    rw [hr]
    exact Work.Asymptotics.thetaC00_second_order (τ : ℂ)
      (by rw [UpperHalfPlane.coe_im]; exact Work.Asymptotics.Funnel.im_one hτ)
  have hkey := log_expansion_step3 (a := Work.Kernels.theta01Fun τ - 1)
    (b := Work.Kernels.theta00Fun τ - 1) (q := Work.Residues.Ept τ) (M := 4) (r := r)
    (by norm_num) (le_refl 4) hr0 (by rw [hr]) hr8 ha hb
  have hlog1 : Complex.log (1 + (Work.Kernels.theta01Fun τ - 1))
      = Complex.log (Work.Kernels.theta01Fun τ) := by congr 1; ring
  have hlog0 : Complex.log (1 + (Work.Kernels.theta00Fun τ - 1))
      = Complex.log (Work.Kernels.theta00Fun τ) := by congr 1; ring
  rw [hlog1, hlog0] at hkey
  have hLam : Work.Kernels.LogLambda.LamS (τ : ℂ) + 16 * Work.Residues.Ept τ
        + (64 / 3 : ℂ) * Work.Residues.Ept τ ^ 3
      = 4 * (Complex.log (Work.Kernels.theta01Fun τ)
              - Complex.log (Work.Kernels.theta00Fun τ) + 4 * Work.Residues.Ept τ
              + (16 / 3 : ℂ) * Work.Residues.Ept τ ^ 3) := by
    simp only [Work.Kernels.LogLambda.LamS, Work.Kernels.LogLambda.thetaC01,
      Work.Kernels.LogLambda.thetaC00, Work.Kernels.theta01Fun, Work.Kernels.theta00Fun]
    ring
  rw [hLam]
  have hnorm : ‖(4 : ℂ) * (Complex.log (Work.Kernels.theta01Fun τ)
        - Complex.log (Work.Kernels.theta00Fun τ) + 4 * Work.Residues.Ept τ
        + (16 / 3 : ℂ) * Work.Residues.Ept τ ^ 3)‖
      = 4 * ‖Complex.log (Work.Kernels.theta01Fun τ)
        - Complex.log (Work.Kernels.theta00Fun τ) + 4 * Work.Residues.Ept τ
        + (16 / 3 : ℂ) * Work.Residues.Ept τ ^ 3‖ := by
    rw [norm_mul]; norm_num
  rw [hnorm]
  calc 4 * ‖Complex.log (Work.Kernels.theta01Fun τ)
          - Complex.log (Work.Kernels.theta00Fun τ) + 4 * Work.Residues.Ept τ
          + (16 / 3 : ℂ) * Work.Residues.Ept τ ^ 3‖
      ≤ 4 * (1000 * r ^ 4) := by linarith [hkey]
    _ = 4000 * ‖Work.Residues.Ept τ‖ ^ 4 := by rw [hr]; ring

/-! ## The third-order cusp expansion of `𝓛` -/

/-- `log(1 + (E²+a)) = E² + O(‖E‖⁴)` when `a = O(‖E‖⁴)`. -/
private lemma log_one_add_sq_bound {E a : ℂ}
    (hE1 : ‖E‖ ≤ 1 / 8) (ha : ‖a‖ ≤ 2 * ‖E‖ ^ 4) :
    ‖Complex.log (1 + (E ^ 2 + a)) - E ^ 2‖ ≤ 100 * ‖E‖ ^ 4 := by
  have hk : (0 : ℝ) ≤ ‖E‖ := norm_nonneg E
  have hE1' : ‖E‖ ≤ 1 := by linarith
  set u : ℂ := E ^ 2 + a with hu
  have ha' : ‖u - E ^ 2‖ ≤ 2 * ‖E‖ ^ 4 := by
    have h : u - E ^ 2 = a := by rw [hu]; ring
    rw [h]; exact ha
  have hEk2 : ‖E‖ ^ 2 ≤ (1 / 8 : ℝ) ^ 2 := pow_le_pow_left₀ hk hE1 2
  have hu_norm : ‖u‖ ≤ 3 * ‖E‖ ^ 2 := by
    have h1 : ‖u‖ ≤ ‖E ^ 2‖ + ‖a‖ := by rw [hu]; exact norm_add_le _ _
    rw [norm_pow] at h1
    have h2 : ‖E‖ ^ 4 ≤ ‖E‖ ^ 2 := pow_le_pow_of_le_one hk hE1' (by norm_num)
    nlinarith [h1, ha, h2]
  have hu1 : ‖u‖ ≤ 1 / 2 := by nlinarith [hu_norm, hEk2]
  have hrem := log_taylor_remainder3 u hu1
  have hpoly : u - u ^ 2 / 2 + u ^ 3 / 3 - E ^ 2
      = (u - E ^ 2) * (1 - (u + E ^ 2) / 2 + (u ^ 2 + u * E ^ 2 + E ^ 4) / 3)
        - E ^ 4 / 2 + E ^ 6 / 3 := by ring
  have hEb : ‖E ^ 2‖ ≤ 1 := by rw [norm_pow]; nlinarith [hk, hE1']
  have hbr : ‖1 - (u + E ^ 2) / 2 + (u ^ 2 + u * E ^ 2 + E ^ 4) / 3‖ ≤ 20 := by
    have hA := norm_add_le (1 - (u + E ^ 2) / 2) ((u ^ 2 + u * E ^ 2 + E ^ 4) / 3)
    have hB := norm_sub_le (1 : ℂ) ((u + E ^ 2) / 2)
    rw [norm_one] at hB
    have h1 : ‖(u + E ^ 2) / 2‖ ≤ 3 := by
      rw [norm_div, Complex.norm_ofNat]
      have h2 : ‖u + E ^ 2‖ ≤ 5 := by
        have h3 := norm_add_le u (E ^ 2)
        linarith [h3, hu_norm, hEb, hk, hE1']
      linarith [h2]
    have h2 : ‖(u ^ 2 + u * E ^ 2 + E ^ 4) / 3‖ ≤ 15 := by
      rw [norm_div, Complex.norm_ofNat]
      have h4 : ‖u ^ 2 + u * E ^ 2 + E ^ 4‖ ≤ 45 := by
        have h5 := norm_add_le (u ^ 2 + u * E ^ 2) (E ^ 4)
        have h6 := norm_add_le (u ^ 2) (u * E ^ 2)
        have h7 : ‖u ^ 2‖ ≤ 20 := by
          rw [norm_pow]
          have h : ‖u‖ ^ 2 ≤ (3 * ‖E‖ ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg u) hu_norm 2
          nlinarith [h, hk, hE1']
        have h8 : ‖u * E ^ 2‖ ≤ 20 := by
          rw [norm_mul, norm_pow]
          have h : ‖u‖ * ‖E‖ ^ 2 ≤ (3 * ‖E‖ ^ 2) * ‖E‖ ^ 2 :=
            mul_le_mul_of_nonneg_right hu_norm (by positivity)
          nlinarith [h, hk, hE1']
        have h9 : ‖E ^ 4‖ ≤ 1 := by
          rw [norm_pow]
          exact pow_le_one₀ hk hE1'
        linarith
      linarith [h4]
    linarith [hA, hB, h1, h2]
  have hterm : ‖(u - E ^ 2) * (1 - (u + E ^ 2) / 2 + (u ^ 2 + u * E ^ 2 + E ^ 4) / 3)
        - E ^ 4 / 2 + E ^ 6 / 3‖ ≤ 45 * ‖E‖ ^ 4 := by
    have h1 : ‖(u - E ^ 2) * (1 - (u + E ^ 2) / 2 + (u ^ 2 + u * E ^ 2 + E ^ 4) / 3)‖
        ≤ 2 * ‖E‖ ^ 4 * 20 := by
      rw [norm_mul]
      exact mul_le_mul ha' hbr (norm_nonneg _) (by positivity)
    have h2 : ‖E ^ 4 / 2‖ = ‖E‖ ^ 4 / 2 := by rw [norm_div, norm_pow]; norm_num
    have h3 : ‖E ^ 6 / 3‖ = ‖E‖ ^ 6 / 3 := by rw [norm_div, norm_pow]; norm_num
    have h4 : ‖E‖ ^ 6 ≤ ‖E‖ ^ 4 := pow_le_pow_of_le_one hk hE1' (by norm_num)
    have hA := norm_add_le ((u - E ^ 2) * (1 - (u + E ^ 2) / 2
        + (u ^ 2 + u * E ^ 2 + E ^ 4) / 3) - E ^ 4 / 2) (E ^ 6 / 3)
    have hB := norm_sub_le ((u - E ^ 2) * (1 - (u + E ^ 2) / 2
        + (u ^ 2 + u * E ^ 2 + E ^ 4) / 3)) (E ^ 4 / 2)
    rw [h3] at hA
    rw [h2] at hB
    have hpos : (0 : ℝ) ≤ ‖E‖ ^ 4 := by positivity
    nlinarith [hA, hB, h1, h4, hpos]
  have hlog : Complex.log (1 + (E ^ 2 + a)) = Complex.log (1 + u) := by rw [hu]
  have hsplit : Complex.log (1 + u) - E ^ 2
      = (Complex.log (1 + u) - (u - u ^ 2 / 2 + u ^ 3 / 3))
        + ((u - u ^ 2 / 2 + u ^ 3 / 3) - E ^ 2) := by ring
  rw [hlog, hsplit]
  refine le_trans (norm_add_le _ _) ?_
  rw [hpoly]
  have h3 : ‖u‖ ^ 4 ≤ (3 * ‖E‖ ^ 2) ^ 4 := pow_le_pow_left₀ (norm_nonneg u) hu_norm 4
  have h4 : ‖E‖ ^ 8 ≤ ‖E‖ ^ 4 := pow_le_pow_of_le_one hk hE1' (by norm_num)
  have hpos : (0 : ℝ) ≤ ‖E‖ ^ 4 := by positivity
  nlinarith [hrem, hterm, h3, h4, hpos, hk, hE1]

/-- `log(1 + (2E+b)) = 2E - 2E² + (8/3)E³ + O(‖E‖⁴)` when `b = O(‖E‖⁴)`. -/
private lemma log_one_add_two_mul_bound {E b : ℂ}
    (hE1 : ‖E‖ ≤ 1 / 8) (hb : ‖b‖ ≤ 4 * ‖E‖ ^ 4) :
    ‖Complex.log (1 + (2 * E + b)) - 2 * E + 2 * E ^ 2 - (8 / 3 : ℂ) * E ^ 3‖
      ≤ 150 * ‖E‖ ^ 4 := by
  have hk : (0 : ℝ) ≤ ‖E‖ := norm_nonneg E
  have hE1' : ‖E‖ ≤ 1 := by linarith
  set c : ℂ := 2 * E with hc
  set w : ℂ := c + b with hw
  have hcE : ‖c‖ ≤ 2 * ‖E‖ := by rw [hc, norm_mul, Complex.norm_ofNat]
  have hb1 : ‖b‖ ≤ ‖E‖ := by
    have h3 : 4 * ‖E‖ ^ 3 ≤ 1 := by
      have h4 : ‖E‖ ^ 3 ≤ (1 / 8 : ℝ) ^ 3 := pow_le_pow_left₀ hk hE1 3
      nlinarith
    calc ‖b‖ ≤ 4 * ‖E‖ ^ 4 := hb
      _ = (4 * ‖E‖ ^ 3) * ‖E‖ := by ring
      _ ≤ 1 * ‖E‖ := mul_le_mul_of_nonneg_right h3 hk
      _ = ‖E‖ := by ring
  have hw_norm : ‖w‖ ≤ 3 * ‖E‖ := by
    have h1 : ‖w‖ ≤ ‖c‖ + ‖b‖ := by rw [hw]; exact norm_add_le _ _
    linarith [h1, hcE, hb1]
  have hwb : ‖w - c‖ ≤ 4 * ‖E‖ ^ 4 := by
    have h : w - c = b := by rw [hw]; ring
    rw [h]; exact hb
  have hw1 : ‖w‖ ≤ 1 / 2 := by nlinarith [hw_norm, hE1]
  have hrem := log_taylor_remainder3 w hw1
  have hpoly : w - w ^ 2 / 2 + w ^ 3 / 3 - (c - c ^ 2 / 2 + c ^ 3 / 3)
      = (w - c) * (1 - (w + c) / 2 + (w ^ 2 + w * c + c ^ 2) / 3) := by ring
  have hc1 : ‖c‖ ≤ 1 := by nlinarith [hcE, hk, hE1']
  have hbr : ‖1 - (w + c) / 2 + (w ^ 2 + w * c + c ^ 2) / 3‖ ≤ 20 := by
    have hA := norm_add_le (1 - (w + c) / 2) ((w ^ 2 + w * c + c ^ 2) / 3)
    have hB := norm_sub_le (1 : ℂ) ((w + c) / 2)
    rw [norm_one] at hB
    have h1 : ‖(w + c) / 2‖ ≤ 3 := by
      rw [norm_div, Complex.norm_ofNat]
      have h2 : ‖w + c‖ ≤ 5 := by
        have h3 := norm_add_le w c
        linarith [h3, hw_norm, hc1]
      linarith [h2]
    have h2 : ‖(w ^ 2 + w * c + c ^ 2) / 3‖ ≤ 15 := by
      rw [norm_div, Complex.norm_ofNat]
      have h4 : ‖w ^ 2 + w * c + c ^ 2‖ ≤ 45 := by
        have h5 := norm_add_le (w ^ 2 + w * c) (c ^ 2)
        have h6 := norm_add_le (w ^ 2) (w * c)
        have h7 : ‖w ^ 2‖ ≤ 20 := by
          rw [norm_pow]
          have h : ‖w‖ ^ 2 ≤ (3 * ‖E‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg w) hw_norm 2
          nlinarith [h, hk, hE1']
        have h8 : ‖w * c‖ ≤ 20 := by
          rw [norm_mul]
          have h : ‖w‖ * ‖c‖ ≤ (3 * ‖E‖) * (2 * ‖E‖) :=
            mul_le_mul hw_norm hcE (norm_nonneg c) (by positivity)
          nlinarith [h, hk, hE1']
        have h9 : ‖c ^ 2‖ ≤ 4 := by
          rw [norm_pow]
          have h : ‖c‖ ^ 2 ≤ (2 * ‖E‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg c) hcE 2
          nlinarith [h, hk, hE1']
        linarith
      linarith [h4]
    linarith [hA, hB, h1, h2]
  have hterm : ‖(w - c) * (1 - (w + c) / 2 + (w ^ 2 + w * c + c ^ 2) / 3)‖
      ≤ 4 * ‖E‖ ^ 4 * 20 := by
    rw [norm_mul]
    exact mul_le_mul hwb hbr (norm_nonneg _) (by positivity)
  have hlog : Complex.log (1 + (2 * E + b)) = Complex.log (1 + w) := by rw [hw, hc]
  have hT : c - c ^ 2 / 2 + c ^ 3 / 3 = 2 * E - 2 * E ^ 2 + (8 / 3 : ℂ) * E ^ 3 := by
    rw [hc]; ring
  have hsplit : Complex.log (1 + w) - 2 * E + 2 * E ^ 2 - (8 / 3 : ℂ) * E ^ 3
      = (Complex.log (1 + w) - (w - w ^ 2 / 2 + w ^ 3 / 3))
        + ((w - w ^ 2 / 2 + w ^ 3 / 3) - (c - c ^ 2 / 2 + c ^ 3 / 3)) := by
    rw [hT]; ring
  rw [hlog, hsplit]
  refine le_trans (norm_add_le _ _) ?_
  rw [hpoly]
  have h3 : ‖w‖ ^ 4 ≤ (3 * ‖E‖) ^ 4 := pow_le_pow_left₀ (norm_nonneg w) hw_norm 4
  have hpos : (0 : ℝ) ≤ ‖E‖ ^ 4 := by positivity
  nlinarith [hrem, hterm, h3, hpos, hk, hE1]

/-- **Third-order cusp expansion of `𝓛`.** -/
private lemma L_cusp_third_order (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : UpperHalfPlane, Work.Asymptotics.Funnel τ →
      ‖ℓ.L τ - ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ
          - 8 * Work.Residues.Ept τ + 12 * Work.Residues.Ept τ ^ 2
          - (32 / 3 : ℂ) * Work.Residues.Ept τ ^ 3)‖
        ≤ C * ‖Work.Residues.Ept τ‖ ^ 4 := by
  refine ⟨1000, by norm_num, fun τ hτ => ?_⟩
  have h1 : 1 ≤ τ.im := Work.Asymptotics.Funnel.im_one hτ
  rw [show Work.Asymptotics.Compact.cuspC ℓ = 4 * (Real.log 2 : ℂ) from
    Work.Asymptotics.CuspL_eq ℓ]
  rw [Work.Asymptotics.LogLambdaData_L_eq_Lfun ℓ τ]
  rw [Work.Residues.Ept_apply]
  set z : ℂ := (τ : ℂ) with hz
  have hz1 : (1 : ℝ) ≤ z.im := by rw [hz, UpperHalfPlane.coe_im]; exact h1
  have hzW : z ∈ Work.Kernels.LogLambda.W := by
    show (1 / 2 : ℝ) < z.im
    linarith
  set E : ℂ := Complex.exp (Real.pi * Complex.I * z) with hE
  set r : ℂ := jacobiTheta₂ (z / 2) z / 2 with hrdef
  set θ : ℂ := Work.Kernels.LogLambda.thetaC00 z with hθdef
  have hEnorm : ‖E‖ = Real.exp (-(Real.pi * z.im)) := by
    rw [hE]; exact Work.Asymptotics.norm_exp_pi_I_mul z
  have hE1 : ‖E‖ ≤ 1 := by
    rw [hEnorm, Real.exp_le_one_iff]; nlinarith [Real.pi_pos, hz1]
  have hE8 : ‖E‖ ≤ 1 / 8 := by
    rw [hEnorm]
    exact (Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, hz1])).trans exp_neg_pi_le_eighth'
  have hA : ‖r - 1 - E ^ 2‖ ≤ 2 * ‖E‖ ^ 4 := by
    rw [hrdef, hE]
    exact Work.Asymptotics.ratio_third_order z hz1
  have hB : ‖θ - 1 - 2 * E‖ ≤ 4 * ‖E‖ ^ 4 := by
    rw [hθdef, hE]
    exact Work.Asymptotics.thetaC00_second_order z hz1
  have hlogr := log_one_add_sq_bound (E := E) (a := r - 1 - E ^ 2) hE8 hA
  rw [show E ^ 2 + (r - 1 - E ^ 2) = r - 1 by ring,
    show (1 : ℂ) + (r - 1) = r by ring] at hlogr
  have hlogθ := log_one_add_two_mul_bound (E := E) (b := θ - 1 - 2 * E) hE8 hB
  rw [show 2 * E + (θ - 1 - 2 * E) = θ - 1 by ring,
    show (1 : ℂ) + (θ - 1) = θ by ring] at hlogθ
  have hLU : Work.Kernels.LogLambda.LU z - (Real.pi : ℂ) * Complex.I * z
      = 4 * (Real.log 2 : ℂ) + 4 * Complex.log r - 4 * Complex.log θ := by
    rw [Work.Kernels.LogLambda.LU, Work.Kernels.LogLambda.thetaC10_div_exp]
    simp only [hrdef, hθdef, Work.Kernels.LogLambda.thetaC00]
    ring
  have hkey : Work.Kernels.LogLambda.Lfun z - (Real.pi : ℂ) * Complex.I * z
        - 4 * (Real.log 2 : ℂ) + 8 * E - 12 * E ^ 2 + (32 / 3 : ℂ) * E ^ 3
      = 4 * (Complex.log r - E ^ 2)
        - 4 * (Complex.log θ - 2 * E + 2 * E ^ 2 - (8 / 3 : ℂ) * E ^ 3) := by
    rw [Work.Kernels.LogLambda.Lfun_eq_LU_on_W z hzW, hLU]
    ring
  have hgoal : Work.Kernels.LogLambda.Lfun z
        - ((Real.pi : ℂ) * Complex.I * z + 4 * (Real.log 2 : ℂ) - 8 * E + 12 * E ^ 2
            - (32 / 3 : ℂ) * E ^ 3)
      = Work.Kernels.LogLambda.Lfun z - (Real.pi : ℂ) * Complex.I * z
        - 4 * (Real.log 2 : ℂ) + 8 * E - 12 * E ^ 2 + (32 / 3 : ℂ) * E ^ 3 := by ring
  rw [hgoal, hkey]
  have hnorm4 : ‖(4 : ℂ)‖ = 4 := by norm_num
  calc ‖4 * (Complex.log r - E ^ 2) - 4 * (Complex.log θ - 2 * E + 2 * E ^ 2
        - (8 / 3 : ℂ) * E ^ 3)‖
      ≤ ‖4 * (Complex.log r - E ^ 2)‖
          + ‖4 * (Complex.log θ - 2 * E + 2 * E ^ 2 - (8 / 3 : ℂ) * E ^ 3)‖ := norm_sub_le _ _
    _ = 4 * ‖Complex.log r - E ^ 2‖
          + 4 * ‖Complex.log θ - 2 * E + 2 * E ^ 2 - (8 / 3 : ℂ) * E ^ 3‖ := by
        rw [norm_mul, norm_mul, hnorm4]
    _ ≤ 4 * (100 * ‖E‖ ^ 4) + 4 * (150 * ‖E‖ ^ 4) := by
        have := hlogr
        have := hlogθ
        linarith
    _ = 1000 * ‖E‖ ^ 4 := by ring

/-! ## Bounds for the truncation polynomials -/

private lemma norm_W3_le {e : ℂ} (h : ‖e‖ ≤ 1) : ‖(6 : ℂ) - 192 * e ^ 2‖ ≤ 200 := by
  have h1 : ‖(192 : ℂ) * e ^ 2‖ ≤ 192 * ‖e‖ ^ 2 := by
    rw [norm_mul, norm_pow, Complex.norm_ofNat]
  have h2 : ‖e‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg e) h
  have h3 : ‖(6 : ℂ)‖ = 6 := Complex.norm_ofNat 6
  have h4 := norm_sub_le (6 : ℂ) (192 * e ^ 2)
  rw [h3] at h4
  linarith [h4, h1, h2]

private lemma norm_R3_le {e : ℂ} (h : ‖e‖ ≤ 1) :
    ‖(-8 : ℂ) * e + 12 * e ^ 2 - (32 / 3 : ℂ) * e ^ 3‖ ≤ 31 * ‖e‖ := by
  have hk : (0 : ℝ) ≤ ‖e‖ := norm_nonneg e
  have h2 : ‖e‖ ^ 2 ≤ ‖e‖ := by
    simpa using pow_le_pow_of_le_one hk h (show (1 : ℕ) ≤ 2 by norm_num)
  have h3 : ‖e‖ ^ 3 ≤ ‖e‖ := by
    simpa using pow_le_pow_of_le_one hk h (show (1 : ℕ) ≤ 3 by norm_num)
  have t1 : ‖(-8 : ℂ) * e‖ ≤ 8 * ‖e‖ := by
    rw [norm_mul]
    have h8 : ‖(-8 : ℂ)‖ = 8 := by norm_num
    rw [h8]
  have t2 : ‖12 * e ^ 2‖ ≤ 12 * ‖e‖ := by
    rw [norm_mul, norm_pow, Complex.norm_ofNat]
    nlinarith [h2, hk]
  have t3 : ‖(32 / 3 : ℂ) * e ^ 3‖ ≤ 11 * ‖e‖ := by
    rw [norm_mul, norm_pow]
    have h32 : ‖(32 / 3 : ℂ)‖ = 32 / 3 := by norm_num
    rw [h32]
    nlinarith [h3, hk]
  have t4 := norm_sub_le ((-8 : ℂ) * e + 12 * e ^ 2) ((32 / 3 : ℂ) * e ^ 3)
  have t5 := norm_add_le ((-8 : ℂ) * e) (12 * e ^ 2)
  linarith [t4, t5, t1, t2, t3]

private lemma norm_Z3_le {e : ℂ} (h : ‖e‖ ≤ 1) :
    ‖(-3 : ℂ) + 96 * e ^ 2 + 1152 * e ^ 3‖ ≤ 2000 := by
  have hk : (0 : ℝ) ≤ ‖e‖ := norm_nonneg e
  have h2 : ‖e‖ ^ 2 ≤ 1 := pow_le_one₀ hk h
  have h3 : ‖e‖ ^ 3 ≤ 1 := pow_le_one₀ hk h
  have t1 : ‖(96 : ℂ) * e ^ 2‖ ≤ 96 := by
    rw [norm_mul, norm_pow, Complex.norm_ofNat]; nlinarith [h2]
  have t2 : ‖(1152 : ℂ) * e ^ 3‖ ≤ 1152 := by
    rw [norm_mul, norm_pow, Complex.norm_ofNat]; nlinarith [h3]
  have t3 : ‖(-3 : ℂ)‖ = 3 := by norm_num
  have t4 := norm_add_le ((-3 : ℂ) + 96 * e ^ 2) (1152 * e ^ 3)
  have t5 := norm_add_le ((-3 : ℂ)) (96 * e ^ 2)
  rw [t3] at t5
  linarith [t4, t5, t1, t2]

private lemma norm_S3_le {e : ℂ} (h : ‖e‖ ≤ 1) :
    ‖(-16 : ℂ) * e - (64 / 3 : ℂ) * e ^ 3‖ ≤ 38 * ‖e‖ := by
  have hk : (0 : ℝ) ≤ ‖e‖ := norm_nonneg e
  have h3 : ‖e‖ ^ 3 ≤ ‖e‖ := by
    simpa using pow_le_pow_of_le_one hk h (show (1 : ℕ) ≤ 3 by norm_num)
  have t1 : ‖(-16 : ℂ) * e‖ ≤ 16 * ‖e‖ := by
    rw [norm_mul]
    have h16 : ‖(-16 : ℂ)‖ = 16 := by norm_num
    rw [h16]
  have t2 : ‖(64 / 3 : ℂ) * e ^ 3‖ ≤ 22 * ‖e‖ := by
    rw [norm_mul, norm_pow]
    have h64 : ‖(64 / 3 : ℂ)‖ = 64 / 3 := by norm_num
    rw [h64]
    nlinarith [h3, hk]
  have t4 := norm_sub_le ((-16 : ℂ) * e) ((64 / 3 : ℂ) * e ^ 3)
  linarith [t4, t1, t2]

/-! ## The main theorem -/

/-- **First-order cusp expansion of `2ψ₂ + ψ₄`.** -/
theorem psi_combo_first_order (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : UpperHalfPlane, Work.Asymptotics.Funnel τ →
      ‖2 * Work.Kernels.psi2 ℓ τ + Work.Kernels.psi4 ℓ τ
          - 6 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ)
          + (192 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ) - 72)
              * Work.Kernels.qParamFun τ‖
        ≤ C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖ ^ 2 := by
  obtain ⟨C1, hC1, h1⟩ := psiW_expansion
  obtain ⟨C2, hC2, h2⟩ := psiZ_expansion
  obtain ⟨C3, hC3, h3⟩ := L_cusp_third_order ℓ
  obtain ⟨C4, hC4, h4⟩ := LS_cusp_third_order ℓ
  refine ⟨C1 * (Real.pi + 4) + (45312 + 31 * C1 + 200 * C3 + C1 * C3 + 38 * C2
      + 2000 * C4 + C2 * C4) + 1, 1, by positivity, by norm_num, fun τ hτ => ?_⟩
  have hτ1 : (1 : ℝ) ≤ τ.im := Work.Asymptotics.Funnel.im_one hτ
  set e : ℂ := Work.Asymptotics.nomeE τ with he
  have hen : ‖e‖ ≤ 1 / 350 := by rw [he]; exact nomeE_norm_le_funnel hτ
  have he1 : ‖e‖ ≤ 1 := le_trans hen (by norm_num)
  have heEpt : e = Work.Residues.Ept τ := rfl
  have heEpt' : Work.Residues.Ept τ = e := heEpt.symm
  have hqe : Work.Kernels.qParamFun τ = e ^ 2 := by
    rw [he, Work.Asymptotics.nomeE_def, Work.Kernels.qParamFun, sq, ← Complex.exp_add]
    congr 1
    ring
  set Wp : ℂ := 2 * (Work.Kernels.UFun τ + Work.Kernels.WFun τ)
      + (Work.Kernels.UFun τ ^ 2 + Work.Kernels.WFun τ ^ 2 - 2 * Work.Kernels.VFun τ ^ 2)
      with hWpdef
  set Zp : ℂ := -2 * (Work.Kernels.UFun τ + Work.Kernels.VFun τ)
      + (Work.Kernels.UFun τ ^ 2 + Work.Kernels.VFun τ ^ 2 - 2 * Work.Kernels.WFun τ ^ 2)
      with hZpdef
  set W3 : ℂ := (6 : ℂ) - 192 * e ^ 2 with hW3
  set R3 : ℂ := -8 * e + 12 * e ^ 2 - (32 / 3 : ℂ) * e ^ 3 with hR3
  set Z3 : ℂ := (-3 : ℂ) + 96 * e ^ 2 + 1152 * e ^ 3 with hZ3
  set S3 : ℂ := -16 * e - (64 / 3 : ℂ) * e ^ 3 with hS3
  set w : ℂ := Wp - W3 with hw
  set z : ℂ := Zp - Z3 with hz
  set Λ : ℂ := (Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ with hΛ
  set Rl : ℂ := ℓ.L τ - Λ with hRl
  set Lsv : ℂ := ℓ.L_S τ with hLsv
  set rr : ℂ := Rl - R3 with hrr
  set ss : ℂ := Lsv - S3 with hss
  -- the psi-decomposition
  have hs1 : (Work.Kernels.xi2Fun ∣[(2 : ℤ)] ModularGroup.S) τ
      = -(Work.Kernels.UFun τ + Work.Kernels.VFun τ) :=
    Work.Kernels.KernelFacts.xi2Fun_slash_S τ
  have hs2 : (Work.Kernels.xi4Fun ∣[(4 : ℤ)] ModularGroup.S) τ
      = Work.Kernels.UFun τ ^ 2 + Work.Kernels.VFun τ ^ 2 - 2 * Work.Kernels.WFun τ ^ 2 :=
    Work.Kernels.KernelFacts.xi4S_apply τ
  have hpsi : 2 * Work.Kernels.psi2 ℓ τ + Work.Kernels.psi4 ℓ τ
      = Wp * ℓ.L τ + Zp * ℓ.L_S τ := by
    have hu : 2 * Work.Kernels.psi2 ℓ τ + Work.Kernels.psi4 ℓ τ
        = (2 * Work.Kernels.xi2Fun τ + Work.Kernels.xi4Fun τ) * ℓ.L τ
          + (2 * ((Work.Kernels.xi2Fun ∣[(2 : ℤ)] ModularGroup.S) τ)
              + (Work.Kernels.xi4Fun ∣[(4 : ℤ)] ModularGroup.S) τ) * ℓ.L_S τ := by
      simp only [Work.Kernels.psi2, Work.Kernels.psi4]
      ring
    have e1 : 2 * Work.Kernels.xi2Fun τ + Work.Kernels.xi4Fun τ = Wp := by
      rw [hWpdef]
    have e2 : 2 * ((Work.Kernels.xi2Fun ∣[(2 : ℤ)] ModularGroup.S) τ)
        + (Work.Kernels.xi4Fun ∣[(4 : ℤ)] ModularGroup.S) τ = Zp := by
      rw [hZpdef, hs1, hs2]
      ring
    rw [hu, e1, e2]
  -- bounds for the four error pieces
  have hWp := h1 τ hτ
  rw [← he] at hWp
  have hZp := h2 τ hτ
  rw [← he] at hZp
  have hRe := h3 τ hτ
  rw [heEpt'] at hRe
  have hLSe := h4 τ hτ
  rw [← he] at hLSe
  have hw_b : ‖w‖ ≤ C1 * ‖e‖ ^ 4 := by
    have h : ‖Wp - W3‖ ≤ C1 * ‖e‖ ^ 4 := by rw [hWpdef, hW3]; exact hWp
    rwa [← hw] at h
  have hz_b : ‖z‖ ≤ C2 * ‖e‖ ^ 4 := by
    have h : ‖Zp - Z3‖ ≤ C2 * ‖e‖ ^ 4 := by rw [hZpdef, hZ3]; exact hZp
    rwa [← hz] at h
  have hr_b : ‖rr‖ ≤ C3 * ‖e‖ ^ 4 := by
    have heq : rr = ℓ.L τ - ((Real.pi : ℂ) * Complex.I * (τ : ℂ)
        + Work.Asymptotics.Compact.cuspC ℓ - 8 * Work.Residues.Ept τ
        + 12 * Work.Residues.Ept τ ^ 2 - (32 / 3 : ℂ) * Work.Residues.Ept τ ^ 3) := by
      rw [hrr, hRl, hR3, hΛ, heEpt]
      ring
    rw [heq]; exact hRe
  have hs_b : ‖ss‖ ≤ C4 * ‖e‖ ^ 4 := by
    have heq : ss = ℓ.L_S τ + 16 * Work.Asymptotics.nomeE τ
        + (64 / 3 : ℂ) * Work.Asymptotics.nomeE τ ^ 3 := by
      rw [hss, hLsv, hS3]
      ring
    rw [heq, he]; exact hLSe
  -- the algebraic reduction
  have hT : 2 * Work.Kernels.psi2 ℓ τ + Work.Kernels.psi4 ℓ τ - 6 * Λ
        + (192 * Λ - 72) * Work.Kernels.qParamFun τ
      = w * Λ + ((W3 + w) * Rl + (Z3 + z) * Lsv - 72 * e ^ 2) := by
    have hL : ℓ.L τ = Λ + Rl := by rw [hRl]; ring
    have hW3w : Wp = W3 + w := by rw [hw]; ring
    have hZ3z : Zp = Z3 + z := by rw [hz]; ring
    rw [hpsi, hL, hqe, ← hLsv, hW3w, hZ3z, hW3]
    ring
  -- the polynomial identity and the error decomposition
  have hpoly : W3 * R3 + Z3 * S3 - 72 * e ^ 2 = -20736 * e ^ 4 - 24576 * e ^ 6 := by
    rw [hW3, hR3, hZ3]; ring
  have hRl_eq : Rl = R3 + rr := by rw [hrr]; ring
  have hLsv_eq : Lsv = S3 + ss := by rw [hss]; ring
  have hsplit : (W3 + w) * Rl + (Z3 + z) * Lsv - 72 * e ^ 2
      = (W3 * R3 + Z3 * S3 - 72 * e ^ 2) + (W3 * rr + Z3 * ss)
        + ((w * R3 + w * rr) + (z * S3 + z * ss)) := by
    rw [hRl_eq, hLsv_eq]; ring
  -- bounds for the pieces
  have hpolyb : ‖-20736 * e ^ 4 - 24576 * e ^ 6‖ ≤ 45312 * ‖e‖ ^ 4 := by
    have e1 : ‖(-20736 : ℂ) * e ^ 4‖ = 20736 * ‖e‖ ^ 4 := by
      rw [norm_mul, norm_pow]; norm_num
    have e2 : ‖(24576 : ℂ) * e ^ 6‖ = 24576 * ‖e‖ ^ 6 := by
      rw [norm_mul, norm_pow]; norm_num
    have h6 : ‖e‖ ^ 6 ≤ ‖e‖ ^ 4 := pow_le_pow_of_le_one (norm_nonneg e) he1
      (show (4 : ℕ) ≤ 6 by norm_num)
    have h4 : (0 : ℝ) ≤ ‖e‖ ^ 4 := by positivity
    have hA := norm_sub_le ((-20736 : ℂ) * e ^ 4) ((24576 : ℂ) * e ^ 6)
    rw [e1, e2] at hA
    nlinarith [hA, h6, h4]
  have hwR3 : ‖w * R3‖ ≤ 31 * C1 * ‖e‖ ^ 4 := by
    rw [norm_mul]
    have hR3b : ‖R3‖ ≤ 31 * ‖e‖ := by rw [hR3]; exact norm_R3_le he1
    calc ‖w‖ * ‖R3‖ ≤ (C1 * ‖e‖ ^ 4) * (31 * ‖e‖) :=
          mul_le_mul hw_b hR3b (norm_nonneg _) (by positivity)
      _ = 31 * C1 * ‖e‖ ^ 5 := by ring
      _ ≤ 31 * C1 * ‖e‖ ^ 4 := mul_le_mul_of_nonneg_left
          (pow_le_pow_of_le_one (norm_nonneg e) he1 (show (4 : ℕ) ≤ 5 by norm_num))
          (mul_nonneg (by positivity) hC1.le)
  have hW3r : ‖W3 * rr‖ ≤ 200 * C3 * ‖e‖ ^ 4 := by
    rw [norm_mul]
    have hW3b : ‖W3‖ ≤ 200 := by rw [hW3]; exact norm_W3_le he1
    calc ‖W3‖ * ‖rr‖ ≤ 200 * (C3 * ‖e‖ ^ 4) :=
          mul_le_mul hW3b hr_b (norm_nonneg _) (by positivity)
      _ = 200 * C3 * ‖e‖ ^ 4 := by ring
  have hwr : ‖w * rr‖ ≤ C1 * C3 * ‖e‖ ^ 4 := by
    rw [norm_mul]
    calc ‖w‖ * ‖rr‖ ≤ (C1 * ‖e‖ ^ 4) * (C3 * ‖e‖ ^ 4) :=
          mul_le_mul hw_b hr_b (norm_nonneg _) (by positivity)
      _ = C1 * C3 * ‖e‖ ^ 8 := by ring
      _ ≤ C1 * C3 * ‖e‖ ^ 4 := mul_le_mul_of_nonneg_left
          (pow_le_pow_of_le_one (norm_nonneg e) he1 (show (4 : ℕ) ≤ 8 by norm_num))
          (mul_nonneg hC1.le hC3.le)
  have hzS3 : ‖z * S3‖ ≤ 38 * C2 * ‖e‖ ^ 4 := by
    rw [norm_mul]
    have hS3b : ‖S3‖ ≤ 38 * ‖e‖ := by rw [hS3]; exact norm_S3_le he1
    calc ‖z‖ * ‖S3‖ ≤ (C2 * ‖e‖ ^ 4) * (38 * ‖e‖) :=
          mul_le_mul hz_b hS3b (norm_nonneg _) (by positivity)
      _ = 38 * C2 * ‖e‖ ^ 5 := by ring
      _ ≤ 38 * C2 * ‖e‖ ^ 4 := mul_le_mul_of_nonneg_left
          (pow_le_pow_of_le_one (norm_nonneg e) he1 (show (4 : ℕ) ≤ 5 by norm_num))
          (mul_nonneg (by positivity) hC2.le)
  have hZ3s : ‖Z3 * ss‖ ≤ 2000 * C4 * ‖e‖ ^ 4 := by
    rw [norm_mul]
    have hZ3b : ‖Z3‖ ≤ 2000 := by rw [hZ3]; exact norm_Z3_le he1
    calc ‖Z3‖ * ‖ss‖ ≤ 2000 * (C4 * ‖e‖ ^ 4) :=
          mul_le_mul hZ3b hs_b (norm_nonneg _) (by positivity)
      _ = 2000 * C4 * ‖e‖ ^ 4 := by ring
  have hzs : ‖z * ss‖ ≤ C2 * C4 * ‖e‖ ^ 4 := by
    rw [norm_mul]
    calc ‖z‖ * ‖ss‖ ≤ (C2 * ‖e‖ ^ 4) * (C4 * ‖e‖ ^ 4) :=
          mul_le_mul hz_b hs_b (norm_nonneg _) (by positivity)
      _ = C2 * C4 * ‖e‖ ^ 8 := by ring
      _ ≤ C2 * C4 * ‖e‖ ^ 4 := mul_le_mul_of_nonneg_left
          (pow_le_pow_of_le_one (norm_nonneg e) he1 (show (4 : ℕ) ≤ 8 by norm_num))
          (mul_nonneg hC2.le hC4.le)
  -- the bound for the bracket
  have hCB : ‖(W3 + w) * Rl + (Z3 + z) * Lsv - 72 * e ^ 2‖
      ≤ (45312 + 31 * C1 + 200 * C3 + C1 * C3 + 38 * C2 + 2000 * C4 + C2 * C4) * ‖e‖ ^ 4 := by
    rw [hsplit]
    have hA := norm_add_le ((W3 * R3 + Z3 * S3 - 72 * e ^ 2) + (W3 * rr + Z3 * ss))
      ((w * R3 + w * rr) + (z * S3 + z * ss))
    have hB := norm_add_le (W3 * R3 + Z3 * S3 - 72 * e ^ 2) (W3 * rr + Z3 * ss)
    have hC := norm_add_le (W3 * rr) (Z3 * ss)
    have hD := norm_add_le (w * R3 + w * rr) (z * S3 + z * ss)
    have hE := norm_add_le (w * R3) (w * rr)
    have hF := norm_add_le (z * S3) (z * ss)
    have h1 : ‖W3 * rr + Z3 * ss‖ ≤ 200 * C3 * ‖e‖ ^ 4 + 2000 * C4 * ‖e‖ ^ 4 := by
      linarith [hC, hW3r, hZ3s]
    have h2 : ‖w * R3 + w * rr‖ ≤ 31 * C1 * ‖e‖ ^ 4 + C1 * C3 * ‖e‖ ^ 4 := by
      linarith [hE, hwR3, hwr]
    have h3 : ‖z * S3 + z * ss‖ ≤ 38 * C2 * ‖e‖ ^ 4 + C2 * C4 * ‖e‖ ^ 4 := by
      linarith [hF, hzS3, hzs]
    have h4 : ‖(w * R3 + w * rr) + (z * S3 + z * ss)‖
        ≤ 31 * C1 * ‖e‖ ^ 4 + C1 * C3 * ‖e‖ ^ 4 + 38 * C2 * ‖e‖ ^ 4 + C2 * C4 * ‖e‖ ^ 4 := by
      linarith [hD, h2, h3]
    have hA' : ‖W3 * R3 + Z3 * S3 - 72 * e ^ 2‖ ≤ 45312 * ‖e‖ ^ 4 := by
      rw [hpoly]; exact hpolyb
    have h5 : ‖(W3 * R3 + Z3 * S3 - 72 * e ^ 2) + (W3 * rr + Z3 * ss)‖
        ≤ 45312 * ‖e‖ ^ 4 + (200 * C3 * ‖e‖ ^ 4 + 2000 * C4 * ‖e‖ ^ 4) := by
      linarith [hB, hA', h1]
    linarith [hA, h4, h5]
  -- the bound for `Λ`
  have hscale1 : (1 : ℝ) ≤ Work.Kernels.scale τ := by
    rw [Work.Kernels.scale]
    have h : 0 < (τ.im)⁻¹ := by positivity
    have h2 : (0 : ℝ) ≤ ‖(τ : ℂ)‖ := norm_nonneg _
    linarith
  have hΛb : ‖Λ‖ ≤ (Real.pi + 4) * Work.Kernels.scale τ := by
    rw [hΛ]
    have hc : Work.Asymptotics.Compact.cuspC ℓ = 4 * (Real.log 2 : ℂ) :=
      Work.Asymptotics.CuspL_eq ℓ
    have h3 : ‖(4 : ℂ) * (Real.log 2 : ℂ)‖ ≤ 4 := by
      rw [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.log_nonneg (by norm_num))]
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    have h4 : ‖(τ : ℂ)‖ ≤ Work.Kernels.scale τ := by
      rw [Work.Kernels.scale]
      have h : 0 < (τ.im)⁻¹ := by positivity
      linarith
    have h6 : ‖(Real.pi : ℂ) * Complex.I * (τ : ℂ)‖ ≤ Real.pi * Work.Kernels.scale τ := by
      have hπ : ‖(Real.pi : ℂ) * Complex.I * (τ : ℂ)‖ = Real.pi * ‖(τ : ℂ)‖ := by
        rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos Real.pi_pos]
      rw [hπ]
      nlinarith [h4, Real.pi_pos]
    rw [hc]
    have h1 := norm_add_le ((Real.pi : ℂ) * Complex.I * (τ : ℂ)) ((4 : ℂ) * (Real.log 2 : ℂ))
    have h5 : Real.pi * Work.Kernels.scale τ + 4 ≤ (Real.pi + 4) * Work.Kernels.scale τ := by
      nlinarith [hscale1]
    linarith [h1, h6, h3, h5]
  -- assembly
  have hqn : ‖Work.Kernels.qParamFun τ‖ ^ 2 = ‖e‖ ^ 4 := by
    rw [hqe, norm_pow]
    ring
  have hwΛ : ‖w‖ * ‖Λ‖ ≤ (C1 * (Real.pi + 4)) * Work.Kernels.scale τ * ‖e‖ ^ 4 := by
    calc ‖w‖ * ‖Λ‖ ≤ (C1 * ‖e‖ ^ 4) * ((Real.pi + 4) * Work.Kernels.scale τ) :=
          mul_le_mul hw_b hΛb (norm_nonneg _) (by positivity)
      _ = (C1 * (Real.pi + 4)) * Work.Kernels.scale τ * ‖e‖ ^ 4 := by ring
  rw [hT]
  have hCB0 : (0 : ℝ) ≤ 45312 + 31 * C1 + 200 * C3 + C1 * C3 + 38 * C2 + 2000 * C4 + C2 * C4 := by
    positivity
  have h4 : (0 : ℝ) ≤ ‖e‖ ^ 4 := by positivity
  calc ‖w * Λ + ((W3 + w) * Rl + (Z3 + z) * Lsv - 72 * e ^ 2)‖
      ≤ ‖w * Λ‖ + ‖(W3 + w) * Rl + (Z3 + z) * Lsv - 72 * e ^ 2‖ := norm_add_le _ _
    _ ≤ (C1 * (Real.pi + 4)) * Work.Kernels.scale τ * ‖e‖ ^ 4
          + (45312 + 31 * C1 + 200 * C3 + C1 * C3 + 38 * C2 + 2000 * C4 + C2 * C4)
              * ‖e‖ ^ 4 := by
        rw [norm_mul]
        exact add_le_add hwΛ hCB
    _ ≤ (C1 * (Real.pi + 4)) * Work.Kernels.scale τ * ‖e‖ ^ 4
          + (45312 + 31 * C1 + 200 * C3 + C1 * C3 + 38 * C2 + 2000 * C4 + C2 * C4)
              * Work.Kernels.scale τ * ‖e‖ ^ 4 := by
        have h8 : (45312 + 31 * C1 + 200 * C3 + C1 * C3 + 38 * C2 + 2000 * C4 + C2 * C4)
              * ‖e‖ ^ 4
            ≤ (45312 + 31 * C1 + 200 * C3 + C1 * C3 + 38 * C2 + 2000 * C4 + C2 * C4)
              * Work.Kernels.scale τ * ‖e‖ ^ 4 := by
          have h9 := mul_le_mul_of_nonneg_right hscale1 h4
          nlinarith [h9, hCB0, h4]
        linarith [h8]
    _ = (C1 * (Real.pi + 4) + (45312 + 31 * C1 + 200 * C3 + C1 * C3 + 38 * C2
          + 2000 * C4 + C2 * C4)) * Work.Kernels.scale τ * ‖e‖ ^ 4 := by ring
    _ ≤ (C1 * (Real.pi + 4) + (45312 + 31 * C1 + 200 * C3 + C1 * C3 + 38 * C2
          + 2000 * C4 + C2 * C4) + 1) * Work.Kernels.scale τ * ‖e‖ ^ 4 := by
        have h7 : (0 : ℝ) ≤ Work.Kernels.scale τ * ‖e‖ ^ 4 :=
          mul_nonneg (le_of_lt (Work.Kernels.scale_pos τ)) h4
        nlinarith [h7]
    _ = (C1 * (Real.pi + 4) + (45312 + 31 * C1 + 200 * C3 + C1 * C3 + 38 * C2
          + 2000 * C4 + C2 * C4) + 1) * (Work.Kernels.scale τ) ^ (1 : ℝ)
            * ‖Work.Kernels.qParamFun τ‖ ^ 2 := by
        rw [Real.rpow_one, hqn]
