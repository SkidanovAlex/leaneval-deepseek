import Mathlib
import Submission.Work.Asymptotics.KhatE1Core.xi_expansions
import Submission.Work.Asymptotics.KhatE1.KdevE2Expansions
import Submission.Work.Asymptotics.KhatE1.EptPsiExp
import Submission.Work.Asymptotics.KhatE1.cusp_L_fourth
import Submission.Work.Residues.LamSExpansion
import Submission.Work.Asymptotics.ThetaQExpAux
import Submission.Work.Asymptotics.PGFar.Defs
import Submission.Work.Kernels.LogLambda.LogExtension
import Submission.Work.Kernels.LogLambda.LogConstruct
import Submission.Work.Kernels.KernelFacts.psi4_T2
import Submission.Work.Kernels.TildeFacts.theta_quartic

set_option maxHeartbeats 1600000

namespace Work.Asymptotics.KhatE1Core

open UpperHalfPlane
open Work.Asymptotics.KhatE1

noncomputable section

/-! ## Elementary funnel facts -/

private lemma exp_neg_pi_le_half : Real.exp (-Real.pi) ≤ 1 / 2 := by
  have h : (2 : ℝ) ≤ Real.exp Real.pi := by
    have h1 : (2 : ℝ) ≤ Real.exp 1 := le_of_lt Real.exp_one_gt_two
    have h2 : Real.exp 1 ≤ Real.exp Real.pi :=
      Real.exp_le_exp.mpr (by linarith [Real.pi_gt_three])
    linarith
  rw [Real.exp_neg, inv_eq_one_div]
  exact one_div_le_one_div_of_le (by norm_num) h

private lemma ept_norm_le_half {τ : ℍ} (hτ : Work.Asymptotics.Funnel τ) :
    ‖Work.Residues.Ept τ‖ ≤ 1 / 2 :=
  (Work.Residues.norm_Ept_le_exp_neg_pi τ (Work.Asymptotics.Funnel.im_one hτ)).trans
    exp_neg_pi_le_half

private lemma ept_norm_le_one {τ : ℍ} (hτ : Work.Asymptotics.Funnel τ) :
    ‖Work.Residues.Ept τ‖ ≤ 1 :=
  le_trans (ept_norm_le_half hτ) (by norm_num)

/-! ## The `θ₂`-ratio to fourth order in `e` -/

theorem psi_ratio_fourth (z : ℂ) (hz : 1 ≤ z.im) :
    ‖jacobiTheta₂ (z / 2) z / 2 - 1 - Complex.exp (Real.pi * Complex.I * z) ^ 2‖
      ≤ 2 * ‖Complex.exp (Real.pi * Complex.I * z)‖ ^ 6 := by
  have hy : 0 < z.im := by linarith
  set e : ℂ := Complex.exp (Real.pi * Complex.I * z) with he
  have hee : ‖e‖ = Real.exp (-(Real.pi * z.im)) := by
    rw [he, Complex.norm_exp]
    congr 1
    rw [show (Real.pi : ℂ) * Complex.I * z = ((Real.pi : ℝ) : ℂ) * (Complex.I * z) by ring,
      Complex.re_ofReal_mul, Complex.I_mul_re]
    ring
  have he1 : ‖e‖ ≤ 1 / 2 := by
    rw [hee]
    refine (Real.exp_le_exp.mpr ?_).trans exp_neg_pi_le_half
    nlinarith [Real.pi_pos, hz]
  have hseries := Work.Asymptotics.thetaPair_pow_series z hy
  rw [show Complex.exp (Real.pi * Complex.I * z) = e from he.symm] at hseries
  have hsm : Summable (fun k : ℕ => e ^ (k ^ 2 + k)) :=
    Work.Asymptotics.summable_pow_of_le (e := e) (f := fun k => k ^ 2 + k) (m := 0) he1
      (fun n => by nlinarith)
  have hsplit : (∑' k : ℕ, e ^ (k ^ 2 + k)) = 1 + ∑' k : ℕ, e ^ ((k + 1) ^ 2 + (k + 1)) := by
    rw [hsm.tsum_eq_zero_add]
    norm_num
  have hsm1 : Summable (fun k : ℕ => e ^ ((k + 1) ^ 2 + (k + 1))) :=
    hsm.comp_injective (fun a b h => Nat.succ_injective h)
  have hsplit2 : (∑' k : ℕ, e ^ ((k + 1) ^ 2 + (k + 1)))
      = e ^ 2 + ∑' k : ℕ, e ^ ((k + 2) ^ 2 + (k + 2)) := by
    rw [hsm1.tsum_eq_zero_add]
    norm_num
  have hkey : jacobiTheta₂ (z / 2) z / 2 - 1 - e ^ 2
      = ∑' k : ℕ, e ^ ((k + 2) ^ 2 + (k + 2)) := by
    rw [hseries, hsplit, hsplit2]
    ring
  have hb := Work.Asymptotics.norm_tsum_pow_le (e := e)
    (f := fun k : ℕ => (k + 2) ^ 2 + (k + 2)) (m := 6) he1 (fun n => by nlinarith)
  calc ‖jacobiTheta₂ (z / 2) z / 2 - 1 - e ^ 2‖
      = ‖∑' k : ℕ, e ^ ((k + 2) ^ 2 + (k + 2))‖ := by rw [hkey]
    _ ≤ 2 * ‖e‖ ^ 6 := hb
    _ = 2 * ‖Complex.exp (Real.pi * Complex.I * z)‖ ^ 6 := by rw [he]

/-! ## Taylor bounds for the complex logarithm -/

private lemma norm_log_sub_poly6 {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) :
    ‖Complex.log (1 + w) - (w - w ^ 2 / 2 + w ^ 3 / 3 - w ^ 4 / 4 + w ^ 5 / 5)‖
      ≤ ‖w‖ ^ 6 := by
  have hw1 : ‖w‖ < 1 := by linarith
  have h := Complex.norm_log_sub_logTaylor_le 5 (z := w) hw1
  have hlt : Complex.logTaylor 6 w = w - w ^ 2 / 2 + w ^ 3 / 3 - w ^ 4 / 4 + w ^ 5 / 5 := by
    simp only [Complex.logTaylor, Finset.sum_range_succ, Finset.sum_range_zero]
    ring
  rw [hlt] at h
  have h2 : (1 - ‖w‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have hw0 : (0 : ℝ) ≤ ‖w‖ ^ 6 := by positivity
  calc ‖Complex.log (1 + w) - (w - w ^ 2 / 2 + w ^ 3 / 3 - w ^ 4 / 4 + w ^ 5 / 5)‖
      ≤ ‖w‖ ^ 6 * (1 - ‖w‖)⁻¹ / (5 + 1) := h
    _ = ‖w‖ ^ 6 * (1 - ‖w‖)⁻¹ / 6 := by norm_num
    _ ≤ ‖w‖ ^ 6 * 2 / 6 := by gcongr
    _ ≤ ‖w‖ ^ 6 := by nlinarith [hw0]

private lemma norm_log_sub_poly3 {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) :
    ‖Complex.log (1 + w) - (w - w ^ 2 / 2)‖ ≤ ‖w‖ ^ 3 := by
  have hw1 : ‖w‖ < 1 := by linarith
  have h := Complex.norm_log_sub_logTaylor_le 2 (z := w) hw1
  have hlt : Complex.logTaylor 3 w = w - w ^ 2 / 2 := by
    simp only [Complex.logTaylor, Finset.sum_range_succ, Finset.sum_range_zero]
    ring
  rw [hlt] at h
  have h2 : (1 - ‖w‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have hw0 : (0 : ℝ) ≤ ‖w‖ ^ 3 := by positivity
  calc ‖Complex.log (1 + w) - (w - w ^ 2 / 2)‖
      ≤ ‖w‖ ^ 3 * (1 - ‖w‖)⁻¹ / (2 + 1) := h
    _ = ‖w‖ ^ 3 * (1 - ‖w‖)⁻¹ / 3 := by norm_num
    _ ≤ ‖w‖ ^ 3 * 2 / 3 := by gcongr
    _ ≤ ‖w‖ ^ 3 := by nlinarith [hw0]

/-! ## `O(‖e‖⁶)` monomials -/

private lemma isSm6_pow (c : ℂ) (k : ℕ) (hk : 6 ≤ k) :
    IsSm 6 (fun τ : ℍ => c * (Work.Residues.Ept τ) ^ k) :=
  IsSm.mono (isSm_Epow c k) hk

private lemma IsSm_add6 {f g : ℍ → ℂ} (hf : IsSm 6 f) (hg : IsSm 6 g) :
    IsSm 6 (fun τ => f τ + g τ) := by
  have h := hf.add hg
  rw [min_self] at h
  exact h

/-! ## The fourth powers of `θ₀₀` and `θ₀₁` through order `e⁵` -/

private lemma isSm_A0 : IsSm 0 (fun τ : ℍ => 1 + 2 * Work.Residues.Ept τ
    + 2 * (Work.Residues.Ept τ) ^ 4) := by
  refine IsSm.bdd (B := 5) (by norm_num) (fun τ hτ => ?_)
  have he := ept_norm_le_one hτ
  have h4 : ‖Work.Residues.Ept τ‖ ^ 4 ≤ 1 := pow_le_one₀ (norm_nonneg _) he
  have h2 : ‖(2 : ℂ) * Work.Residues.Ept τ‖ ≤ 2 := by
    rw [norm_mul, Complex.norm_ofNat]; linarith
  have h5 : ‖(2 : ℂ) * (Work.Residues.Ept τ) ^ 4‖ ≤ 2 := by
    rw [norm_mul, Complex.norm_ofNat, norm_pow]; linarith
  have hsum := norm_add_le ((1 : ℂ) + 2 * Work.Residues.Ept τ)
    (2 * (Work.Residues.Ept τ) ^ 4)
  have hsum2 := norm_add_le (1 : ℂ) (2 * Work.Residues.Ept τ)
  rw [norm_one] at hsum2
  linarith

private lemma isSm_B0 : IsSm 0 (fun τ : ℍ => 1 - 2 * Work.Residues.Ept τ
    + 2 * (Work.Residues.Ept τ) ^ 4) := by
  refine IsSm.bdd (B := 5) (by norm_num) (fun τ hτ => ?_)
  have he := ept_norm_le_one hτ
  have h4 : ‖Work.Residues.Ept τ‖ ^ 4 ≤ 1 := pow_le_one₀ (norm_nonneg _) he
  have h2 : ‖(2 : ℂ) * Work.Residues.Ept τ‖ ≤ 2 := by
    rw [norm_mul, Complex.norm_ofNat]; linarith
  have h5 : ‖(2 : ℂ) * (Work.Residues.Ept τ) ^ 4‖ ≤ 2 := by
    rw [norm_mul, Complex.norm_ofNat, norm_pow]; linarith
  have hsum := norm_add_le ((1 : ℂ) - 2 * Work.Residues.Ept τ)
    (2 * (Work.Residues.Ept τ) ^ 4)
  have hsum2 := norm_sub_le (1 : ℂ) (2 * Work.Residues.Ept τ)
  rw [norm_one] at hsum2
  linarith

/-- `θ₀₀⁴ = (1 + 2e + 2e⁴)⁴ + O(‖e‖⁶)`. -/
private lemma U_sub_poly : IsSm 6 (fun τ : ℍ => Work.Kernels.UFun τ
    - (1 + 2 * Work.Residues.Ept τ + 2 * (Work.Residues.Ept τ) ^ 4) ^ 4) := by
  have hx6 : IsSm 6 (fun τ : ℍ => Work.Asymptotics.KhatE1.theta00Rem τ) :=
    Work.Asymptotics.KhatE1.isSm_theta00Rem
  have hx0 : IsSm 0 (fun τ : ℍ => Work.Asymptotics.KhatE1.theta00Rem τ) :=
    hx6.mono (by norm_num)
  have hbr : IsSm 0 (fun τ : ℍ => 4 * (1 + 2 * Work.Residues.Ept τ
        + 2 * (Work.Residues.Ept τ) ^ 4) ^ 3
      + 6 * (1 + 2 * Work.Residues.Ept τ + 2 * (Work.Residues.Ept τ) ^ 4) ^ 2
          * Work.Asymptotics.KhatE1.theta00Rem τ
      + 4 * (1 + 2 * Work.Residues.Ept τ + 2 * (Work.Residues.Ept τ) ^ 4)
          * Work.Asymptotics.KhatE1.theta00Rem τ ^ 2
      + Work.Asymptotics.KhatE1.theta00Rem τ ^ 3) :=
    (((IsSm.const_mul 4 (isSm_A0.pow 3)).add
      ((IsSm.const_mul 6 (isSm_A0.pow 2)).mul hx0)).add
      ((IsSm.const_mul 4 isSm_A0).mul (hx0.pow 2))).add (hx0.pow 3)
  refine IsSm.congr (hx6.mul hbr) (fun τ => ?_)
  have hU : Work.Kernels.UFun τ = (1 + 2 * Work.Residues.Ept τ
      + 2 * (Work.Residues.Ept τ) ^ 4 + Work.Asymptotics.KhatE1.theta00Rem τ) ^ 4 := by
    show Work.Kernels.theta00Fun τ ^ 4 = _
    congr 1
    simp only [Work.Asymptotics.KhatE1.theta00Rem]
    ring
  rw [hU]; ring

/-- `θ₀₁⁴ = (1 - 2e + 2e⁴)⁴ + O(‖e‖⁶)`. -/
private lemma W_sub_poly : IsSm 6 (fun τ : ℍ => Work.Kernels.WFun τ
    - (1 - 2 * Work.Residues.Ept τ + 2 * (Work.Residues.Ept τ) ^ 4) ^ 4) := by
  have hy6 : IsSm 6 (fun τ : ℍ => Work.Asymptotics.KhatE1.theta01Rem τ) :=
    Work.Asymptotics.KhatE1.isSm_theta01Rem
  have hy0 : IsSm 0 (fun τ : ℍ => Work.Asymptotics.KhatE1.theta01Rem τ) :=
    hy6.mono (by norm_num)
  have hbr : IsSm 0 (fun τ : ℍ => 4 * (1 - 2 * Work.Residues.Ept τ
        + 2 * (Work.Residues.Ept τ) ^ 4) ^ 3
      + 6 * (1 - 2 * Work.Residues.Ept τ + 2 * (Work.Residues.Ept τ) ^ 4) ^ 2
          * Work.Asymptotics.KhatE1.theta01Rem τ
      + 4 * (1 - 2 * Work.Residues.Ept τ + 2 * (Work.Residues.Ept τ) ^ 4)
          * Work.Asymptotics.KhatE1.theta01Rem τ ^ 2
      + Work.Asymptotics.KhatE1.theta01Rem τ ^ 3) :=
    (((IsSm.const_mul 4 (isSm_B0.pow 3)).add
      ((IsSm.const_mul 6 (isSm_B0.pow 2)).mul hy0)).add
      ((IsSm.const_mul 4 isSm_B0).mul (hy0.pow 2))).add (hy0.pow 3)
  refine IsSm.congr (hy6.mul hbr) (fun τ => ?_)
  have hW : Work.Kernels.WFun τ = (1 - 2 * Work.Residues.Ept τ
      + 2 * (Work.Residues.Ept τ) ^ 4 + Work.Asymptotics.KhatE1.theta01Rem τ) ^ 4 := by
    show Work.Kernels.theta01Fun τ ^ 4 = _
    congr 1
    simp only [Work.Asymptotics.KhatE1.theta01Rem]
    ring
  rw [hW]; ring

private lemma isSm_U0 : IsSm 0 (fun τ : ℍ => Work.Kernels.UFun τ) :=
  IsSm.congr ((U_sub_poly.mono (l := 0) (by norm_num)).add (isSm_A0.pow 4))
    (fun τ => by ring)

private lemma isSm_W0 : IsSm 0 (fun τ : ℍ => Work.Kernels.WFun τ) :=
  IsSm.congr ((W_sub_poly.mono (l := 0) (by norm_num)).add (isSm_B0.pow 4))
    (fun τ => by ring)

private lemma isSm_V0 : IsSm 0 (fun τ : ℍ => Work.Kernels.VFun τ) := by
  refine IsSm.congr (isSm_U0.sub isSm_W0) (fun τ => ?_)
  have h := Work.Kernels.TildeFacts.theta_quartic τ
  show Work.Kernels.UFun τ - Work.Kernels.WFun τ = Work.Kernels.VFun τ
  rw [h]; ring

/-! ## The expansions of `ξ₂`, `ξ₄` and `V` through order `e⁴` -/

/-- `ξ₂ = U + W = 2 + 48q + 48q² + O(‖e‖⁶)`, `q = e²`. -/
private lemma xi2_exp6 : IsSm 6 (fun τ : ℍ => Work.Kernels.xi2Fun τ
    - (2 + 48 * (Work.Residues.Ept τ) ^ 2 + 48 * ((Work.Residues.Ept τ) ^ 2) ^ 2)) := by
  have hres : IsSm 6 (fun τ : ℍ => 192 * (Work.Residues.Ept τ) ^ 6
      + 48 * (Work.Residues.Ept τ) ^ 8 + 192 * (Work.Residues.Ept τ) ^ 10
      + 64 * (Work.Residues.Ept τ) ^ 12 + 32 * (Work.Residues.Ept τ) ^ 16) :=
    IsSm.congr (IsSm_add6 (IsSm_add6 (IsSm_add6 (IsSm_add6 ((isSm6_pow (192) 6 le_rfl)) ((isSm6_pow (48) 8 (by norm_num)))) ((isSm6_pow (192) 10 (by norm_num)))) ((isSm6_pow (64) 12 (by norm_num)))) ((isSm6_pow (32) 16 (by norm_num)))) (fun τ => by ring)
  have hmain : IsSm 6 (fun τ : ℍ =>
      (Work.Kernels.UFun τ - (1 + 2 * Work.Residues.Ept τ + 2 * (Work.Residues.Ept τ) ^ 4) ^ 4)
      + (Work.Kernels.WFun τ - (1 - 2 * Work.Residues.Ept τ + 2 * (Work.Residues.Ept τ) ^ 4) ^ 4)
      + (192 * (Work.Residues.Ept τ) ^ 6 + 48 * (Work.Residues.Ept τ) ^ 8
          + 192 * (Work.Residues.Ept τ) ^ 10 + 64 * (Work.Residues.Ept τ) ^ 12
          + 32 * (Work.Residues.Ept τ) ^ 16)) :=
    (U_sub_poly.add W_sub_poly).add hres
  refine IsSm.congr hmain (fun τ => ?_)
  simp only [Work.Kernels.xi2Fun]
  ring

/-- `V = θ₁₀⁴ = 16e + 64e³ + 96e⁵ + O(‖e‖⁶)`. -/
private lemma V_exp6 : IsSm 6 (fun τ : ℍ => Work.Kernels.VFun τ
    - (16 * Work.Residues.Ept τ + 64 * (Work.Residues.Ept τ) ^ 3
        + 96 * (Work.Residues.Ept τ) ^ 5)) := by
  have hres : IsSm 6 (fun τ : ℍ => 128 * (Work.Residues.Ept τ) ^ 7
      + 192 * (Work.Residues.Ept τ) ^ 9 + 128 * (Work.Residues.Ept τ) ^ 13) :=
    IsSm.congr (IsSm_add6 (IsSm_add6 ((isSm6_pow (128) 7 (by norm_num))) ((isSm6_pow (192) 9 (by norm_num)))) ((isSm6_pow (128) 13 (by norm_num)))) (fun τ => by ring)
  have hmain : IsSm 6 (fun τ : ℍ =>
      (Work.Kernels.UFun τ - (1 + 2 * Work.Residues.Ept τ + 2 * (Work.Residues.Ept τ) ^ 4) ^ 4)
      - (Work.Kernels.WFun τ - (1 - 2 * Work.Residues.Ept τ + 2 * (Work.Residues.Ept τ) ^ 4) ^ 4)
      + (128 * (Work.Residues.Ept τ) ^ 7 + 192 * (Work.Residues.Ept τ) ^ 9
          + 128 * (Work.Residues.Ept τ) ^ 13)) :=
    (U_sub_poly.sub W_sub_poly).add hres
  refine IsSm.congr hmain (fun τ => ?_)
  have h := Work.Kernels.TildeFacts.theta_quartic τ
  rw [h]; ring

/-- `ξ₄ = U² + W² - 2V² = 2 - 288q - 1824q² + O(‖e‖⁶)`, `q = e²`. -/
private lemma xi4_exp6 : IsSm 6 (fun τ : ℍ => Work.Kernels.xi4Fun τ
    - (2 - 288 * (Work.Residues.Ept τ) ^ 2 - 1824 * ((Work.Residues.Ept τ) ^ 2) ^ 2)) := by
  have hdU : IsSm 6 (fun τ : ℍ => Work.Kernels.UFun τ ^ 2
      - ((1 + 2 * Work.Residues.Ept τ + 2 * (Work.Residues.Ept τ) ^ 4) ^ 4) ^ 2) := by
    refine IsSm.congr (U_sub_poly.mul (isSm_U0.add (isSm_A0.pow 4))) (fun τ => ?_)
    ring
  have hdW : IsSm 6 (fun τ : ℍ => Work.Kernels.WFun τ ^ 2
      - ((1 - 2 * Work.Residues.Ept τ + 2 * (Work.Residues.Ept τ) ^ 4) ^ 4) ^ 2) := by
    refine IsSm.congr (W_sub_poly.mul (isSm_W0.add (isSm_B0.pow 4))) (fun τ => ?_)
    ring
  have hV0 : IsSm 0 (fun τ : ℍ => (1 + 2 * Work.Residues.Ept τ
      + 2 * (Work.Residues.Ept τ) ^ 4) ^ 4
      - (1 - 2 * Work.Residues.Ept τ + 2 * (Work.Residues.Ept τ) ^ 4) ^ 4) :=
    (isSm_A0.pow 4).sub (isSm_B0.pow 4)
  have hdV : IsSm 6 (fun τ : ℍ => Work.Kernels.VFun τ ^ 2
      - ((1 + 2 * Work.Residues.Ept τ + 2 * (Work.Residues.Ept τ) ^ 4) ^ 4
          - (1 - 2 * Work.Residues.Ept τ + 2 * (Work.Residues.Ept τ) ^ 4) ^ 4) ^ 2) := by
    refine IsSm.congr ((U_sub_poly.sub W_sub_poly).mul (isSm_V0.add hV0)) (fun τ => ?_)
    have h := Work.Kernels.TildeFacts.theta_quartic τ
    rw [h]; ring
  have hres : IsSm 6 (fun τ : ℍ => -8064 * (Work.Residues.Ept τ) ^ 6
      - 14112 * (Work.Residues.Ept τ) ^ 8 - 35712 * (Work.Residues.Ept τ) ^ 10
      - 43648 * (Work.Residues.Ept τ) ^ 12 - 64512 * (Work.Residues.Ept τ) ^ 14
      - 57152 * (Work.Residues.Ept τ) ^ 16 - 69120 * (Work.Residues.Ept τ) ^ 18
      - 26112 * (Work.Residues.Ept τ) ^ 20 - 55296 * (Work.Residues.Ept τ) ^ 22
      + 3584 * (Work.Residues.Ept τ) ^ 24 - 18432 * (Work.Residues.Ept τ) ^ 26
      + 2048 * (Work.Residues.Ept τ) ^ 28 + 512 * (Work.Residues.Ept τ) ^ 32) :=
    IsSm.congr (IsSm_add6 (IsSm_add6 (IsSm_add6 (IsSm_add6 (IsSm_add6 (IsSm_add6 (IsSm_add6 (IsSm_add6 (IsSm_add6 (IsSm_add6 (IsSm_add6 (IsSm_add6 ((isSm6_pow (-8064) 6 le_rfl)) ((isSm6_pow (-14112) 8 (by norm_num)))) ((isSm6_pow (-35712) 10 (by norm_num)))) ((isSm6_pow (-43648) 12 (by norm_num)))) ((isSm6_pow (-64512) 14 (by norm_num)))) ((isSm6_pow (-57152) 16 (by norm_num)))) ((isSm6_pow (-69120) 18 (by norm_num)))) ((isSm6_pow (-26112) 20 (by norm_num)))) ((isSm6_pow (-55296) 22 (by norm_num)))) ((isSm6_pow (3584) 24 (by norm_num)))) ((isSm6_pow (-18432) 26 (by norm_num)))) ((isSm6_pow (2048) 28 (by norm_num)))) ((isSm6_pow (512) 32 (by norm_num)))) (fun τ => by ring)
  refine IsSm.congr (((hdU.add hdW).sub (hdV.const_mul 2)).add hres) (fun τ => ?_)
  simp only [Work.Kernels.xi4Fun]
  ring

/-! ## The explicit remainders of `θ₀₀` and `θ₀₁` -/

private lemma theta00Rem_bound (τ : ℍ) (hτ : 2 ≤ τ.im) :
    ‖Work.Asymptotics.KhatE1.theta00Rem τ‖ ≤ 4 * ‖Work.Residues.Ept τ‖ ^ 6 := by
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = ‖Work.Residues.Ept τ‖ := ⟨_, rfl⟩
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hr1 : r < 1 := by rw [hr]; exact Work.Residues.norm_Ept_lt_one τ
  have hr2 : r ≤ 1 / 2 := by
    rw [hr]
    exact (Work.Residues.norm_Ept_le_exp_neg_pi τ (by linarith)).trans exp_neg_pi_le_half
  have hy : 0 < (τ : ℂ).im := by simpa using τ.im_pos
  have htheta : Work.Kernels.theta00Fun τ
      = 1 + 2 * (∑' n : ℕ, Complex.exp (Real.pi * Complex.I * ((n : ℂ) + 1) ^ 2 * (τ : ℂ))) := by
    have h := jacobiTheta_eq_tsum_nat hy
    rw [show Work.Kernels.theta00Fun τ = jacobiTheta (τ : ℂ) from rfl, h]
  set F : ℕ → ℂ := fun n => Complex.exp (Real.pi * Complex.I * ((n : ℂ) + 1) ^ 2 * (τ : ℂ))
    with hFdef
  have hsm : Summable F := by
    have hsum : HasSum F ((Work.Kernels.theta00Fun τ - 1) / 2) := by
      simpa [Work.Kernels.theta00Fun] using hasSum_nat_jacobiTheta hy
    exact hsum.summable
  have hnorm_eq : ∀ m : ℕ, ‖F m‖ = r ^ ((m + 1) ^ 2) := by
    intro m
    have h1 : ‖F m‖ = Real.exp (-(Real.pi * ((m : ℝ) + 1) ^ 2 * τ.im)) := by
      simp only [hFdef]
      rw [Work.Residues.norm_cexp_pi_I_sq_mul' (τ : ℂ) m, UpperHalfPlane.coe_im]
    rw [h1, show ((m : ℝ) + 1) ^ 2 = (((m + 1) ^ 2 : ℕ) : ℝ) by push_cast; ring,
      Work.Residues.exp_neg_pi_im_nat_mul, ← hr]
  have hsplit : (∑' n : ℕ, F n) = F 0 + ∑' n : ℕ, F (n + 1) := hsm.tsum_eq_zero_add
  have hshift : (∑' n : ℕ, F (n + 1)) = F 1 + ∑' n : ℕ, F (n + 2) := by
    have hinj : Function.Injective (fun n : ℕ => n + 1) := fun a b h => Nat.succ_injective h
    have hsm' : Summable (fun n : ℕ => F (n + 1)) := hsm.comp_injective hinj
    have h := hsm'.tsum_eq_zero_add
    have h2 : (∑' n : ℕ, F (n + 1 + 1)) = ∑' n : ℕ, F (n + 2) :=
      tsum_congr (fun n => by rw [show n + 1 + 1 = n + 2 from by omega])
    rw [h2] at h
    simpa using h
  have hF0 : F 0 = Work.Residues.Ept τ := by simp [hFdef]
  have hF1 : F 1 = (Work.Residues.Ept τ) ^ 4 := by
    have hthis : Complex.exp (Real.pi * Complex.I * (((1 : ℕ) : ℂ) + 1) ^ 2 * (τ : ℂ))
        = (Work.Residues.Ept τ) ^ 4 := by
      have harg : Real.pi * Complex.I * (((1 : ℕ) : ℂ) + 1) ^ 2 * (τ : ℂ)
          = 4 * (Real.pi * Complex.I * (τ : ℂ)) := by norm_num; ring
      rw [harg, show Complex.exp (4 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ)))
          = (Complex.exp ((Real.pi : ℂ) * Complex.I * (τ : ℂ))) ^ 4 by
        rw [show (4 : ℂ) = ((4 : ℕ) : ℂ) by norm_num, Complex.exp_nat_mul]]
      rfl
    simpa only [hFdef] using hthis
  have hmain : Work.Asymptotics.KhatE1.theta00Rem τ = 2 * ∑' n : ℕ, F (n + 2) := by
    rw [Work.Asymptotics.KhatE1.theta00Rem, htheta, hsplit, hF0, hshift, hF1]
    ring
  have htailterm : ∀ n : ℕ, ‖F (n + 2)‖ ≤ r ^ (n + 6) := by
    intro n
    rw [hnorm_eq (n + 2)]
    have h2 : n + 6 ≤ (n + 3) ^ 2 := by nlinarith
    calc r ^ ((n + 2 + 1) ^ 2) = r ^ ((n + 3) ^ 2) := by ring_nf
      _ ≤ r ^ (n + 6) := pow_le_pow_of_le_one hr0 (le_of_lt hr1) h2
  have hg : HasSum (fun n : ℕ => r ^ (n + 6)) (r ^ 6 / (1 - r)) := by
    have h0 : HasSum (fun n : ℕ => r ^ n) (1 - r)⁻¹ := hasSum_geometric_of_lt_one hr0 hr1
    have h1 := h0.mul_left (r ^ 6)
    have h2 : r ^ 6 * (1 - r)⁻¹ = r ^ 6 / (1 - r) := by rw [div_eq_mul_inv]
    rw [h2] at h1
    refine h1.congr_fun (fun n => ?_)
    rw [mul_comm, pow_add]
  have hsumtail : Summable (fun n : ℕ => ‖F (n + 2)‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) htailterm hg.summable
  have htail : ‖∑' n : ℕ, F (n + 2)‖ ≤ r ^ 6 / (1 - r) := by
    refine le_trans (norm_tsum_le_tsum_norm hsumtail) ?_
    have h1 : (∑' n : ℕ, ‖F (n + 2)‖) ≤ ∑' n : ℕ, r ^ (n + 6) :=
      Summable.tsum_le_tsum htailterm hsumtail hg.summable
    rwa [hg.tsum_eq] at h1
  have hden : 0 < 1 - r := by linarith
  have hden2 : (1 - r)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hden (by norm_num : (0 : ℝ) < 2)]
    linarith
  rw [hmain, norm_mul, Complex.norm_ofNat]
  have hr6 : (0 : ℝ) ≤ r ^ 6 := by positivity
  calc 2 * ‖∑' n : ℕ, F (n + 2)‖ ≤ 2 * (r ^ 6 / (1 - r)) := by linarith [htail]
    _ = 2 * r ^ 6 * (1 - r)⁻¹ := by rw [div_eq_mul_inv]; ring
    _ ≤ 2 * r ^ 6 * 2 := by
        have h0 : (0 : ℝ) ≤ 2 * r ^ 6 := by positivity
        exact mul_le_mul_of_nonneg_left hden2 h0
    _ = 4 * r ^ 6 := by ring
    _ = 4 * ‖Work.Residues.Ept τ‖ ^ 6 := by rw [hr]

private lemma theta01Rem_bound (τ : ℍ) (hτ : 2 ≤ τ.im) :
    ‖Work.Asymptotics.KhatE1.theta01Rem τ‖ ≤ 4 * ‖Work.Residues.Ept τ‖ ^ 6 := by
  have hτ' : 2 ≤ (ModularGroup.T • τ).im := by
    rw [UpperHalfPlane.modular_T_smul, UpperHalfPlane.vadd_im]; exact hτ
  have h := theta00Rem_bound (ModularGroup.T • τ) hτ'
  have heq : Work.Asymptotics.KhatE1.theta00Rem (ModularGroup.T • τ)
      = Work.Asymptotics.KhatE1.theta01Rem τ := by
    simp only [Work.Asymptotics.KhatE1.theta00Rem, Work.Asymptotics.KhatE1.theta01Rem,
      Work.Kernels.theta00Fun_T, Work.Residues.Ept_T]
    ring
  rw [heq, Work.Residues.Ept_T, norm_neg] at h
  exact h

/-! ## The polynomial `P5` and its Lipschitz bound -/

private def P5 (w : ℂ) : ℂ := w - w ^ 2 / 2 + w ^ 3 / 3 - w ^ 4 / 4 + w ^ 5 / 5

private lemma norm_log_sub_P5 {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) :
    ‖Complex.log (1 + w) - P5 w‖ ≤ ‖w‖ ^ 6 :=
  norm_log_sub_poly6 hw

private lemma P5_sub_bound {u v : ℂ} (hu : ‖u‖ ≤ 1 / 2) (hv : ‖v‖ ≤ 1 / 2) :
    ‖P5 u - P5 v‖ ≤ 2 * ‖u - v‖ := by
  have hu0 : (0 : ℝ) ≤ ‖u‖ := norm_nonneg u
  have hv0 : (0 : ℝ) ≤ ‖v‖ := norm_nonneg v
  have hu2 : ‖u‖ ^ 2 ≤ 1 / 4 := by
    have h := pow_le_pow_left₀ hu0 hu 2; norm_num at h ⊢; exact h
  have hv2 : ‖v‖ ^ 2 ≤ 1 / 4 := by
    have h := pow_le_pow_left₀ hv0 hv 2; norm_num at h ⊢; exact h
  have hu3 : ‖u‖ ^ 3 ≤ 1 / 8 := by
    have h := pow_le_pow_left₀ hu0 hu 3; norm_num at h ⊢; exact h
  have hv3 : ‖v‖ ^ 3 ≤ 1 / 8 := by
    have h := pow_le_pow_left₀ hv0 hv 3; norm_num at h ⊢; exact h
  have hu4 : ‖u‖ ^ 4 ≤ 1 / 16 := by
    have h := pow_le_pow_left₀ hu0 hu 4; norm_num at h ⊢; exact h
  have hv4 : ‖v‖ ^ 4 ≤ 1 / 16 := by
    have h := pow_le_pow_left₀ hv0 hv 4; norm_num at h ⊢; exact h
  have hU2 : ‖u ^ 2‖ ≤ 1 / 4 := by rw [norm_pow]; exact hu2
  have hV2 : ‖v ^ 2‖ ≤ 1 / 4 := by rw [norm_pow]; exact hv2
  have hUV : ‖u * v‖ ≤ 1 / 4 := by rw [norm_mul]; nlinarith
  have hU3 : ‖u ^ 3‖ ≤ 1 / 8 := by rw [norm_pow]; exact hu3
  have hV3 : ‖v ^ 3‖ ≤ 1 / 8 := by rw [norm_pow]; exact hv3
  have hU2V : ‖u ^ 2 * v‖ ≤ 1 / 8 := by rw [norm_mul, norm_pow]; nlinarith
  have hUV2 : ‖u * v ^ 2‖ ≤ 1 / 8 := by rw [norm_mul, norm_pow]; nlinarith
  have hU4 : ‖u ^ 4‖ ≤ 1 / 16 := by rw [norm_pow]; exact hu4
  have hV4 : ‖v ^ 4‖ ≤ 1 / 16 := by rw [norm_pow]; exact hv4
  have hU3V : ‖u ^ 3 * v‖ ≤ 1 / 16 := by rw [norm_mul, norm_pow]; nlinarith
  have hU2V2 : ‖u ^ 2 * v ^ 2‖ ≤ 1 / 16 := by rw [norm_mul, norm_pow, norm_pow]; nlinarith
  have hUV3 : ‖u * v ^ 3‖ ≤ 1 / 16 := by rw [norm_mul, norm_pow]; nlinarith
  have hfact : P5 u - P5 v = (u - v) * (1 - (u + v) / 2 + (u ^ 2 + u * v + v ^ 2) / 3
      - (u ^ 3 + u ^ 2 * v + u * v ^ 2 + v ^ 3) / 4
      + (u ^ 4 + u ^ 3 * v + u ^ 2 * v ^ 2 + u * v ^ 3 + v ^ 4) / 5) := by
    unfold P5; ring
  have hb1 : ‖(u + v) / 2‖ ≤ 1 / 2 := by
    rw [norm_div, Complex.norm_ofNat]
    have h := norm_add_le u v
    linarith
  have hb2 : ‖(u ^ 2 + u * v + v ^ 2) / 3‖ ≤ 1 / 4 := by
    rw [norm_div, Complex.norm_ofNat]
    have h := norm_add_le (u ^ 2 + u * v) (v ^ 2)
    have h' := norm_add_le (u ^ 2) (u * v)
    linarith
  have hb3 : ‖(u ^ 3 + u ^ 2 * v + u * v ^ 2 + v ^ 3) / 4‖ ≤ 1 / 8 := by
    rw [norm_div, Complex.norm_ofNat]
    have h := norm_add_le (u ^ 3 + u ^ 2 * v + u * v ^ 2) (v ^ 3)
    have h' := norm_add_le (u ^ 3 + u ^ 2 * v) (u * v ^ 2)
    have h'' := norm_add_le (u ^ 3) (u ^ 2 * v)
    linarith
  have hb4 : ‖(u ^ 4 + u ^ 3 * v + u ^ 2 * v ^ 2 + u * v ^ 3 + v ^ 4) / 5‖ ≤ 1 / 16 := by
    rw [norm_div, Complex.norm_ofNat]
    have h := norm_add_le (u ^ 4 + u ^ 3 * v + u ^ 2 * v ^ 2 + u * v ^ 3) (v ^ 4)
    have h' := norm_add_le (u ^ 4 + u ^ 3 * v + u ^ 2 * v ^ 2) (u * v ^ 3)
    have h'' := norm_add_le (u ^ 4 + u ^ 3 * v) (u ^ 2 * v ^ 2)
    have h3 := norm_add_le (u ^ 4) (u ^ 3 * v)
    linarith
  have hQ : ‖1 - (u + v) / 2 + (u ^ 2 + u * v + v ^ 2) / 3
      - (u ^ 3 + u ^ 2 * v + u * v ^ 2 + v ^ 3) / 4
      + (u ^ 4 + u ^ 3 * v + u ^ 2 * v ^ 2 + u * v ^ 3 + v ^ 4) / 5‖ ≤ 2 := by
    have h1 := norm_add_le (((1 : ℂ) - (u + v) / 2 + (u ^ 2 + u * v + v ^ 2) / 3)
      - (u ^ 3 + u ^ 2 * v + u * v ^ 2 + v ^ 3) / 4)
      ((u ^ 4 + u ^ 3 * v + u ^ 2 * v ^ 2 + u * v ^ 3 + v ^ 4) / 5)
    have h2 := norm_sub_le ((1 : ℂ) - (u + v) / 2 + (u ^ 2 + u * v + v ^ 2) / 3)
      ((u ^ 3 + u ^ 2 * v + u * v ^ 2 + v ^ 3) / 4)
    have h3 := norm_add_le ((1 : ℂ) - (u + v) / 2) ((u ^ 2 + u * v + v ^ 2) / 3)
    have h4 := norm_sub_le (1 : ℂ) ((u + v) / 2)
    rw [norm_one] at h4
    linarith
  rw [hfact, norm_mul]
  calc ‖u - v‖ * ‖1 - (u + v) / 2 + (u ^ 2 + u * v + v ^ 2) / 3
        - (u ^ 3 + u ^ 2 * v + u * v ^ 2 + v ^ 3) / 4
        + (u ^ 4 + u ^ 3 * v + u ^ 2 * v ^ 2 + u * v ^ 3 + v ^ 4) / 5‖ ≤ ‖u - v‖ * 2 :=
        mul_le_mul_of_nonneg_left hQ (norm_nonneg _)
    _ = 2 * ‖u - v‖ := by ring

/-! ## The expansion of `Λ_S = 4(log θ₀₁ - log θ₀₀)` to order `e⁵` -/

private lemma log_ratio_expansion {a b q : ℂ} {M r : ℝ}
    (hr0 : 0 ≤ r) (hr8 : r ≤ 1 / 8) (hq : ‖q‖ ≤ r)
    (ha : ‖a‖ ≤ 3 * r) (hb : ‖b‖ ≤ 3 * r)
    (hA : ‖a + 2 * q - 2 * q ^ 4‖ ≤ M * r ^ 6)
    (hB : ‖b - 2 * q - 2 * q ^ 4‖ ≤ M * r ^ 6) :
    ‖Complex.log (1 + a) - Complex.log (1 + b) + 4 * q + (16 / 3 : ℂ) * q ^ 3
        + (24 / 5 : ℂ) * q ^ 5‖ ≤ (2000 + 4 * M) * r ^ 6 := by
  have hr1 : r ≤ 1 := by linarith
  have hr6 : (0 : ℝ) ≤ r ^ 6 := by positivity
  set a0 : ℂ := -2 * q + 2 * q ^ 4 with ha0
  set b0 : ℂ := 2 * q + 2 * q ^ 4 with hb0
  have haa0 : ‖a - a0‖ ≤ M * r ^ 6 := by
    have h : a - a0 = a + 2 * q - 2 * q ^ 4 := by rw [ha0]; ring
    rw [h]; exact hA
  have hbb0 : ‖b - b0‖ ≤ M * r ^ 6 := by
    have h : b - b0 = b - 2 * q - 2 * q ^ 4 := by rw [hb0]; ring
    rw [h]; exact hB
  have ha_half : ‖a‖ ≤ 1 / 2 := by linarith
  have hb_half : ‖b‖ ≤ 1 / 2 := by linarith
  have ha0_half : ‖a0‖ ≤ 1 / 2 := by
    rw [ha0]
    have h1 := norm_add_le ((-2 : ℂ) * q) ((2 : ℂ) * q ^ 4)
    have h2 : ‖(-2 : ℂ) * q‖ = 2 * ‖q‖ := by rw [norm_mul]; norm_num
    have h3 : ‖(2 : ℂ) * q ^ 4‖ = 2 * ‖q‖ ^ 4 := by rw [norm_mul, Complex.norm_ofNat, norm_pow]
    rw [h2, h3] at h1
    have h4 : ‖q‖ ^ 4 ≤ r ^ 4 := pow_le_pow_left₀ (norm_nonneg q) hq 4
    have h5 : r ^ 4 ≤ 1 / 16 := by
      have h := pow_le_pow_left₀ hr0 hr8 4
      linarith [h]
    linarith
  have hb0_half : ‖b0‖ ≤ 1 / 2 := by
    rw [hb0]
    have h1 := norm_add_le ((2 : ℂ) * q) ((2 : ℂ) * q ^ 4)
    have h2 : ‖(2 : ℂ) * q‖ = 2 * ‖q‖ := by rw [norm_mul]; norm_num
    have h3 : ‖(2 : ℂ) * q ^ 4‖ = 2 * ‖q‖ ^ 4 := by rw [norm_mul, Complex.norm_ofNat, norm_pow]
    rw [h2, h3] at h1
    have h4 : ‖q‖ ^ 4 ≤ r ^ 4 := pow_le_pow_left₀ (norm_nonneg q) hq 4
    have h5 : r ^ 4 ≤ 1 / 16 := by
      have h := pow_le_pow_left₀ hr0 hr8 4
      linarith [h]
    linarith
  have hra := norm_log_sub_P5 (w := a) ha_half
  have hrb := norm_log_sub_P5 (w := b) hb_half
  have hra' : ‖Complex.log (1 + a) - P5 a‖ ≤ 729 * r ^ 6 := by
    refine le_trans hra ?_
    have h6 : ‖a‖ ^ 6 ≤ (3 * r) ^ 6 := pow_le_pow_left₀ (norm_nonneg a) ha 6
    calc ‖a‖ ^ 6 ≤ (3 * r) ^ 6 := h6
      _ = 729 * r ^ 6 := by ring
  have hrb' : ‖Complex.log (1 + b) - P5 b‖ ≤ 729 * r ^ 6 := by
    refine le_trans hrb ?_
    have h6 : ‖b‖ ^ 6 ≤ (3 * r) ^ 6 := pow_le_pow_left₀ (norm_nonneg b) hb 6
    calc ‖b‖ ^ 6 ≤ (3 * r) ^ 6 := h6
      _ = 729 * r ^ 6 := by ring
  have hPa : ‖P5 a - P5 a0‖ ≤ 2 * (M * r ^ 6) := by
    have h := P5_sub_bound ha_half ha0_half
    linarith [h, haa0]
  have hPb : ‖P5 b - P5 b0‖ ≤ 2 * (M * r ^ 6) := by
    have h := P5_sub_bound hb_half hb0_half
    linarith [h, hbb0]
  have hpoly : P5 a0 - P5 b0 + 4 * q + (16 / 3 : ℂ) * q ^ 3 + (24 / 5 : ℂ) * q ^ 5
      = 32 * q ^ 7 - 16 * q ^ 9 - 128 * q ^ 11 + 32 * q ^ 13 - 64 * q ^ 17 := by
    rw [ha0, hb0]; unfold P5; ring
  have hpolyb : ‖32 * q ^ 7 - 16 * q ^ 9 - 128 * q ^ 11 + 32 * q ^ 13 - 64 * q ^ 17‖
      ≤ 272 * r ^ 6 := by
    have hq1 : (0 : ℝ) ≤ ‖q‖ := norm_nonneg q
    have k7 : ‖q‖ ^ 7 ≤ r ^ 6 := by
      have h := pow_le_pow_left₀ hq1 hq 7
      have h2 : r ^ 7 ≤ r ^ 6 := pow_le_pow_of_le_one hr0 hr1 (by norm_num)
      linarith
    have k9 : ‖q‖ ^ 9 ≤ r ^ 6 := by
      have h := pow_le_pow_left₀ hq1 hq 9
      have h2 : r ^ 9 ≤ r ^ 6 := pow_le_pow_of_le_one hr0 hr1 (by norm_num)
      linarith
    have k11 : ‖q‖ ^ 11 ≤ r ^ 6 := by
      have h := pow_le_pow_left₀ hq1 hq 11
      have h2 : r ^ 11 ≤ r ^ 6 := pow_le_pow_of_le_one hr0 hr1 (by norm_num)
      linarith
    have k13 : ‖q‖ ^ 13 ≤ r ^ 6 := by
      have h := pow_le_pow_left₀ hq1 hq 13
      have h2 : r ^ 13 ≤ r ^ 6 := pow_le_pow_of_le_one hr0 hr1 (by norm_num)
      linarith
    have k17 : ‖q‖ ^ 17 ≤ r ^ 6 := by
      have h := pow_le_pow_left₀ hq1 hq 17
      have h2 : r ^ 17 ≤ r ^ 6 := pow_le_pow_of_le_one hr0 hr1 (by norm_num)
      linarith
    have e1 : ‖(32 : ℂ) * q ^ 7‖ ≤ 32 * r ^ 6 := by
      rw [norm_mul, Complex.norm_ofNat, norm_pow]; linarith
    have e2 : ‖(16 : ℂ) * q ^ 9‖ ≤ 16 * r ^ 6 := by
      rw [norm_mul, Complex.norm_ofNat, norm_pow]; linarith
    have e3 : ‖(128 : ℂ) * q ^ 11‖ ≤ 128 * r ^ 6 := by
      rw [norm_mul, Complex.norm_ofNat, norm_pow]; linarith
    have e4 : ‖(32 : ℂ) * q ^ 13‖ ≤ 32 * r ^ 6 := by
      rw [norm_mul, Complex.norm_ofNat, norm_pow]; linarith
    have e5 : ‖(64 : ℂ) * q ^ 17‖ ≤ 64 * r ^ 6 := by
      rw [norm_mul, Complex.norm_ofNat, norm_pow]; linarith
    have hA := norm_sub_le ((32 : ℂ) * q ^ 7 - (16 : ℂ) * q ^ 9 - (128 : ℂ) * q ^ 11
      + (32 : ℂ) * q ^ 13) ((64 : ℂ) * q ^ 17)
    have hA' := norm_add_le ((32 : ℂ) * q ^ 7 - (16 : ℂ) * q ^ 9 - (128 : ℂ) * q ^ 11)
      ((32 : ℂ) * q ^ 13)
    have hA'' := norm_sub_le ((32 : ℂ) * q ^ 7 - (16 : ℂ) * q ^ 9) ((128 : ℂ) * q ^ 11)
    have hA''' := norm_sub_le ((32 : ℂ) * q ^ 7) ((16 : ℂ) * q ^ 9)
    linarith [hA, hA', hA'', hA''', e1, e2, e3, e4, e5]

  have key : Complex.log (1 + a) - Complex.log (1 + b) + 4 * q + (16 / 3 : ℂ) * q ^ 3
        + (24 / 5 : ℂ) * q ^ 5
      = ((Complex.log (1 + a) - P5 a) - (Complex.log (1 + b) - P5 b))
        + ((P5 a - P5 a0) - (P5 b - P5 b0))
        + (P5 a0 - P5 b0 + 4 * q + (16 / 3 : ℂ) * q ^ 3 + (24 / 5 : ℂ) * q ^ 5) := by
    ring
  rw [key]
  have h1 := norm_add_le (((Complex.log (1 + a) - P5 a) - (Complex.log (1 + b) - P5 b))
      + ((P5 a - P5 a0) - (P5 b - P5 b0)))
    (P5 a0 - P5 b0 + 4 * q + (16 / 3 : ℂ) * q ^ 3 + (24 / 5 : ℂ) * q ^ 5)
  have h2 := norm_add_le ((Complex.log (1 + a) - P5 a) - (Complex.log (1 + b) - P5 b))
    ((P5 a - P5 a0) - (P5 b - P5 b0))
  have h3 := norm_sub_le (Complex.log (1 + a) - P5 a) (Complex.log (1 + b) - P5 b)
  have h4 := norm_sub_le (P5 a - P5 a0) (P5 b - P5 b0)
  rw [hpoly] at h1 ⊢
  have hsum : 729 * r ^ 6 + 729 * r ^ 6 + 2 * (M * r ^ 6) + 2 * (M * r ^ 6) + 272 * r ^ 6
      ≤ (2000 + 4 * M) * r ^ 6 := by nlinarith [hr6]
  linarith [h1, h2, h3, h4, hra', hrb', hPa, hPb, hpolyb, hsum]

private lemma exp_neg_pi_le_eighth : Real.exp (-Real.pi) ≤ 1 / 8 := by
  have h : (8 : ℝ) ≤ Real.exp Real.pi := by
    have h1 : (2 : ℝ) ≤ Real.exp 1 := le_of_lt Real.exp_one_gt_two
    have h2 : (8 : ℝ) ≤ Real.exp 3 := by
      rw [show (3 : ℝ) = 1 + 1 + 1 by norm_num, Real.exp_add, Real.exp_add]
      nlinarith [h1, Real.exp_pos 1]
    have h3 : Real.exp 3 ≤ Real.exp Real.pi := Real.exp_le_exp.mpr (by linarith [Real.pi_gt_three])
    linarith
  rw [Real.exp_neg, inv_eq_one_div]
  exact one_div_le_one_div_of_le (by norm_num) h

private lemma LamS_exp6 : IsSm 6 (fun τ : ℍ => Work.Kernels.LogLambda.LamS (τ : ℂ)
    + 16 * Work.Residues.Ept τ + (64 / 3 : ℂ) * (Work.Residues.Ept τ) ^ 3
    + (96 / 5 : ℂ) * (Work.Residues.Ept τ) ^ 5) := by
  refine ⟨4 * (2000 + 16), by norm_num, fun τ hτ => ?_⟩
  set q : ℂ := Work.Residues.Ept τ with hq
  have hr8 : ‖q‖ ≤ 1 / 8 := by
    rw [hq]
    exact (Work.Residues.norm_Ept_le_exp_neg_pi τ (Work.Asymptotics.Funnel.im_one hτ)).trans
      exp_neg_pi_le_eighth
  have hq0 : (0 : ℝ) ≤ ‖q‖ := norm_nonneg q
  have hy : ‖Work.Asymptotics.KhatE1.theta01Rem τ‖ ≤ 4 * ‖q‖ ^ 6 := by
    have h := theta01Rem_bound τ (Work.Asymptotics.Funnel.im_two hτ)
    simpa [hq] using h
  have hx : ‖Work.Asymptotics.KhatE1.theta00Rem τ‖ ≤ 4 * ‖q‖ ^ 6 := by
    have h := theta00Rem_bound τ (Work.Asymptotics.Funnel.im_two hτ)
    simpa [hq] using h
  have hA : ‖(Work.Kernels.theta01Fun τ - 1) + 2 * q - 2 * q ^ 4‖ ≤ 4 * ‖q‖ ^ 6 := by
    have h : (Work.Kernels.theta01Fun τ - 1) + 2 * q - 2 * q ^ 4
        = Work.Asymptotics.KhatE1.theta01Rem τ := by
      rw [hq]; simp only [Work.Asymptotics.KhatE1.theta01Rem]; try ring
    calc ‖(Work.Kernels.theta01Fun τ - 1) + 2 * q - 2 * q ^ 4‖
        = ‖Work.Asymptotics.KhatE1.theta01Rem τ‖ := by rw [h]
      _ ≤ 4 * ‖q‖ ^ 6 := hy
  have hB : ‖(Work.Kernels.theta00Fun τ - 1) - 2 * q - 2 * q ^ 4‖ ≤ 4 * ‖q‖ ^ 6 := by
    have h : (Work.Kernels.theta00Fun τ - 1) - 2 * q - 2 * q ^ 4
        = Work.Asymptotics.KhatE1.theta00Rem τ := by
      rw [hq]; simp only [Work.Asymptotics.KhatE1.theta00Rem]; try ring
    calc ‖(Work.Kernels.theta00Fun τ - 1) - 2 * q - 2 * q ^ 4‖
        = ‖Work.Asymptotics.KhatE1.theta00Rem τ‖ := by rw [h]
      _ ≤ 4 * ‖q‖ ^ 6 := hx
  have h2a : ‖-((2 : ℂ) * q) + (2 : ℂ) * q ^ 4‖ ≤ 2 * ‖q‖ + 2 * ‖q‖ ^ 4 := by
    have h := norm_add_le (-((2 : ℂ) * q)) ((2 : ℂ) * q ^ 4)
    have e1 : ‖-((2 : ℂ) * q)‖ = 2 * ‖q‖ := by rw [norm_neg, norm_mul, Complex.norm_ofNat]
    have e2 : ‖(2 : ℂ) * q ^ 4‖ = 2 * ‖q‖ ^ 4 := by rw [norm_mul, Complex.norm_ofNat, norm_pow]
    simpa only [e1, e2] using h
  have h2b : ‖(2 : ℂ) * q + (2 : ℂ) * q ^ 4‖ ≤ 2 * ‖q‖ + 2 * ‖q‖ ^ 4 := by
    have h := norm_add_le ((2 : ℂ) * q) ((2 : ℂ) * q ^ 4)
    have e1 : ‖(2 : ℂ) * q‖ = 2 * ‖q‖ := by rw [norm_mul, Complex.norm_ofNat]
    have e2 : ‖(2 : ℂ) * q ^ 4‖ = 2 * ‖q‖ ^ 4 := by rw [norm_mul, Complex.norm_ofNat, norm_pow]
    simpa only [e1, e2] using h
  have h4 : ‖q‖ ^ 4 ≤ ‖q‖ * (1 / 8) ^ 3 := by
    have h := pow_le_pow_left₀ hq0 hr8 3
    nlinarith [h, hq0]
  have h6 : 4 * ‖q‖ ^ 6 ≤ ‖q‖ * (1 / 8) ^ 3 := by
    have h := pow_le_pow_left₀ hq0 hr8 5
    nlinarith [h, hq0]
  have ha : ‖Work.Kernels.theta01Fun τ - 1‖ ≤ 3 * ‖q‖ := by
    have h1 : ‖Work.Kernels.theta01Fun τ - 1‖
        ≤ ‖Work.Asymptotics.KhatE1.theta01Rem τ‖ + ‖-((2 : ℂ) * q) + (2 : ℂ) * q ^ 4‖ := by
      have h : Work.Kernels.theta01Fun τ - 1
          = Work.Asymptotics.KhatE1.theta01Rem τ + (-((2 : ℂ) * q) + (2 : ℂ) * q ^ 4) := by
        rw [hq]; simp only [Work.Asymptotics.KhatE1.theta01Rem]; try ring
      rw [h]; exact norm_add_le _ _
    linarith [h1, h2a, h4, h6, hy, hq0]
  have hb : ‖Work.Kernels.theta00Fun τ - 1‖ ≤ 3 * ‖q‖ := by
    have h1 : ‖Work.Kernels.theta00Fun τ - 1‖
        ≤ ‖Work.Asymptotics.KhatE1.theta00Rem τ‖ + ‖(2 : ℂ) * q + (2 : ℂ) * q ^ 4‖ := by
      have h : Work.Kernels.theta00Fun τ - 1
          = Work.Asymptotics.KhatE1.theta00Rem τ + ((2 : ℂ) * q + (2 : ℂ) * q ^ 4) := by
        rw [hq]; simp only [Work.Asymptotics.KhatE1.theta00Rem]; try ring
      rw [h]; exact norm_add_le _ _
    linarith [h1, h2b, h4, h6, hx, hq0]
  have hlog := log_ratio_expansion (a := Work.Kernels.theta01Fun τ - 1)
    (b := Work.Kernels.theta00Fun τ - 1) (q := q) (M := 4)
    hq0 hr8 (le_rfl) ha hb hA hB
  have hkey : Work.Kernels.LogLambda.LamS (τ : ℂ) + 16 * q + (64 / 3 : ℂ) * q ^ 3
        + (96 / 5 : ℂ) * q ^ 5
      = 4 * (Complex.log (1 + (Work.Kernels.theta01Fun τ - 1))
          - Complex.log (1 + (Work.Kernels.theta00Fun τ - 1)) + 4 * q
          + (16 / 3 : ℂ) * q ^ 3 + (24 / 5 : ℂ) * q ^ 5) := by
    simp only [Work.Kernels.LogLambda.LamS, Work.Kernels.LogLambda.thetaC01,
      Work.Kernels.LogLambda.thetaC00, Work.Kernels.theta01Fun, Work.Kernels.theta00Fun]
    ring
  change ‖Work.Kernels.LogLambda.LamS (τ : ℂ) + 16 * q + (64 / 3 : ℂ) * q ^ 3
      + (96 / 5 : ℂ) * q ^ 5‖ ≤ 4 * (2000 + 16) * ‖q‖ ^ 6
  rw [hkey, norm_mul]
  rw [show ‖(4 : ℂ)‖ = 4 from Complex.norm_ofNat 4]
  calc 4 * ‖Complex.log (1 + (Work.Kernels.theta01Fun τ - 1))
        - Complex.log (1 + (Work.Kernels.theta00Fun τ - 1)) + 4 * q
        + (16 / 3 : ℂ) * q ^ 3 + (24 / 5 : ℂ) * q ^ 5‖
      ≤ 4 * ((2000 + 4 * (4 : ℝ)) * ‖q‖ ^ 6) := by linarith [hlog]
    _ = 4 * (2000 + 16) * ‖q‖ ^ 6 := by ring_nf

private lemma log_ratio_Lfun_expansion {ρ b q : ℂ} {M r : ℝ}
    (hM0 : 0 ≤ M) (hr0 : 0 ≤ r) (hr8 : r ≤ 1 / 8) (hq : ‖q‖ ≤ r)
    (hb : ‖b‖ ≤ 3 * r) (hMr : M * r ^ 6 ≤ r ^ 2)
    (hrho : ‖ρ - 1 - q ^ 2‖ ≤ M * r ^ 6)
    (hB : ‖b - 2 * q - 2 * q ^ 4‖ ≤ M * r ^ 6) :
    ‖4 * Complex.log ρ - 4 * Complex.log (1 + b) + 8 * q - 12 * q ^ 2 + (32 / 3 : ℂ) * q ^ 3
        - 6 * q ^ 4 + (48 / 5 : ℂ) * q ^ 5‖ ≤ (5000 + 32 * M) * r ^ 6 := by
  have hr1 : r ≤ 1 := by linarith
  have hr6 : (0 : ℝ) ≤ r ^ 6 := by positivity
  have hq0 : (0 : ℝ) ≤ ‖q‖ := norm_nonneg q
  set a : ℂ := ρ - 1 - q ^ 2 with ha
  have ha' : ‖a‖ ≤ M * r ^ 6 := by rw [ha]; exact hrho
  set w : ℂ := q ^ 2 + a with hw
  have hrhow : ρ = 1 + w := by rw [hw, ha]; ring
  have hw1 : ‖w‖ ≤ 1 / 2 := by
    rw [hw]
    have h1 := norm_add_le (q ^ 2) a
    have h2 : ‖q ^ 2‖ = ‖q‖ ^ 2 := by rw [norm_pow]
    rw [h2] at h1
    have h3 : ‖q‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hq0 hq 2
    have h4 : r ^ 2 ≤ 1 / 4 := by nlinarith [hr0, hr8]
    linarith [h1, h3, h4, ha', hMr]
  have hq2_half : ‖q ^ 2‖ ≤ 1 / 2 := by
    rw [norm_pow]
    have h3 : ‖q‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hq0 hq 2
    have h4 : r ^ 2 ≤ 1 / 4 := by nlinarith [hr0, hr8]
    linarith
  have hb_half : ‖b‖ ≤ 1 / 2 := by linarith
  have hlogw := norm_log_sub_P5 (w := w) hw1
  have hlogb := norm_log_sub_P5 (w := b) hb_half
  set b0 : ℂ := 2 * q + 2 * q ^ 4 with hb0
  have hbb0 : ‖b - b0‖ ≤ M * r ^ 6 := by
    have h : b - b0 = b - 2 * q - 2 * q ^ 4 := by rw [hb0]; ring
    rw [h]; exact hB
  have hb0_half : ‖b0‖ ≤ 1 / 2 := by
    rw [hb0]
    have h1 := norm_add_le ((2 : ℂ) * q) ((2 : ℂ) * q ^ 4)
    have h2 : ‖(2 : ℂ) * q‖ = 2 * ‖q‖ := by rw [norm_mul, Complex.norm_ofNat]
    have h3 : ‖(2 : ℂ) * q ^ 4‖ = 2 * ‖q‖ ^ 4 := by rw [norm_mul, Complex.norm_ofNat, norm_pow]
    rw [h2, h3] at h1
    have h4 : ‖q‖ ^ 4 ≤ r ^ 4 := pow_le_pow_left₀ hq0 hq 4
    have h5 : r ^ 4 ≤ 1 / 16 := by
      have h := pow_le_pow_left₀ hr0 hr8 4
      linarith [h]
    linarith
  have hPb : ‖P5 b - P5 b0‖ ≤ 2 * (M * r ^ 6) := by
    have h := P5_sub_bound hb_half hb0_half
    linarith [h, hbb0]
  have hw6 : ‖P5 w - q ^ 2 + q ^ 4 / 2‖ ≤ (2 * M + 1) * r ^ 6 := by
    have hweq : P5 w - q ^ 2 + q ^ 4 / 2 = (P5 w - P5 (q ^ 2)) + (q ^ 6 / 3 - q ^ 8 / 4 + q ^ 10 / 5) := by
      unfold P5; ring
    rw [hweq]
    have h1 : ‖P5 w - P5 (q ^ 2)‖ ≤ 2 * ‖w - q ^ 2‖ := P5_sub_bound hw1 hq2_half
    have h2 : w - q ^ 2 = a := by rw [hw]; ring
    have h3 : ‖q ^ 6 / 3 - q ^ 8 / 4 + q ^ 10 / 5‖ ≤ r ^ 6 := by
      have e1 : ‖q ^ 6 / 3‖ = ‖q‖ ^ 6 / 3 := by rw [norm_div, norm_pow]; norm_num
      have e2 : ‖q ^ 8 / 4‖ = ‖q‖ ^ 8 / 4 := by rw [norm_div, norm_pow]; norm_num
      have e3 : ‖q ^ 10 / 5‖ = ‖q‖ ^ 10 / 5 := by rw [norm_div, norm_pow]; norm_num
      have hA := norm_sub_le (q ^ 6 / 3) (q ^ 8 / 4)
      have hC := norm_add_le (q ^ 6 / 3 - q ^ 8 / 4) (q ^ 10 / 5)
      rw [e1, e2] at hA
      rw [e3] at hC
      have k6 : ‖q‖ ^ 6 / 3 ≤ r ^ 6 / 3 := by
        have h := pow_le_pow_left₀ hq0 hq 6
        linarith
      have k8 : ‖q‖ ^ 8 / 4 ≤ r ^ 6 / 4 := by
        have h := pow_le_pow_left₀ hq0 hq 8
        have h2 : r ^ 8 ≤ r ^ 6 := pow_le_pow_of_le_one hr0 hr1 (by norm_num)
        linarith
      have k10 : ‖q‖ ^ 10 / 5 ≤ r ^ 6 / 5 := by
        have h := pow_le_pow_left₀ hq0 hq 10
        have h2 : r ^ 10 ≤ r ^ 6 := pow_le_pow_of_le_one hr0 hr1 (by norm_num)
        linarith
      linarith [hA, hC, k6, k8, k10, hr6]

    calc ‖(P5 w - P5 (q ^ 2)) + (q ^ 6 / 3 - q ^ 8 / 4 + q ^ 10 / 5)‖
        ≤ ‖P5 w - P5 (q ^ 2)‖ + ‖q ^ 6 / 3 - q ^ 8 / 4 + q ^ 10 / 5‖ := norm_add_le _ _
      _ ≤ 2 * ‖w - q ^ 2‖ + r ^ 6 := by linarith [h1, h3]
      _ = 2 * ‖a‖ + r ^ 6 := by rw [h2]
      _ ≤ (2 * M + 1) * r ^ 6 := by linarith [ha', hr6]
  have hpoly : 4 * q ^ 2 - 2 * q ^ 4 - 4 * P5 b0 + 8 * q - 12 * q ^ 2 + (32 / 3 : ℂ) * q ^ 3
        - 6 * q ^ 4 + (48 / 5 : ℂ) * q ^ 5
      = -32 * q ^ 6 + 64 * q ^ 7 - 120 * q ^ 8 - 32 * q ^ 9 + 96 * q ^ 10 - 256 * q ^ 11
        - (32 / 3 : ℂ) * q ^ 12 + 64 * q ^ 13 - 256 * q ^ 14 + 16 * q ^ 16 - 128 * q ^ 17
        - (128 / 5 : ℂ) * q ^ 20 := by
    rw [hb0]; unfold P5; ring
  have hpolyb : ‖-32 * q ^ 6 + 64 * q ^ 7 - 120 * q ^ 8 - 32 * q ^ 9 + 96 * q ^ 10
      - 256 * q ^ 11 - (32 / 3 : ℂ) * q ^ 12 + 64 * q ^ 13 - 256 * q ^ 14 + 16 * q ^ 16
      - 128 * q ^ 17 - (128 / 5 : ℂ) * q ^ 20‖ ≤ 1101 * r ^ 6 := by
    have hqk : ∀ k : ℕ, 6 ≤ k → ‖q ^ k‖ ≤ r ^ 6 := by
      intro k hk
      rw [norm_pow]
      have h1 := pow_le_pow_left₀ hq0 hq k
      have h2 : r ^ k ≤ r ^ 6 := pow_le_pow_of_le_one hr0 hr1 hk
      linarith
    have e1 : ‖-32 * q ^ 6‖ ≤ 32 * r ^ 6 := by
      have h : ‖-32 * q ^ 6‖ = 32 * ‖q ^ 6‖ := by
        rw [show -32 * q ^ 6 = -((32 : ℂ) * q ^ 6) from by ring, norm_neg, norm_mul,
          Complex.norm_ofNat]
      rw [h]; linarith [hqk 6 le_rfl]
    have e2 : ‖64 * q ^ 7‖ ≤ 64 * r ^ 6 := by
      have h : ‖64 * q ^ 7‖ = 64 * ‖q ^ 7‖ := by
        rw [show (64 : ℂ) * q ^ 7 = 64 * q ^ 7 from rfl, norm_mul, Complex.norm_ofNat]
      rw [h]; linarith [hqk 7 (by norm_num)]
    have e3 : ‖120 * q ^ 8‖ ≤ 120 * r ^ 6 := by
      have h : ‖120 * q ^ 8‖ = 120 * ‖q ^ 8‖ := by
        rw [show (120 : ℂ) * q ^ 8 = 120 * q ^ 8 from rfl, norm_mul, Complex.norm_ofNat]
      rw [h]; linarith [hqk 8 (by norm_num)]
    have e4 : ‖32 * q ^ 9‖ ≤ 32 * r ^ 6 := by
      have h : ‖32 * q ^ 9‖ = 32 * ‖q ^ 9‖ := by
        rw [show (32 : ℂ) * q ^ 9 = 32 * q ^ 9 from rfl, norm_mul, Complex.norm_ofNat]
      rw [h]; linarith [hqk 9 (by norm_num)]
    have e5 : ‖96 * q ^ 10‖ ≤ 96 * r ^ 6 := by
      have h : ‖96 * q ^ 10‖ = 96 * ‖q ^ 10‖ := by
        rw [show (96 : ℂ) * q ^ 10 = 96 * q ^ 10 from rfl, norm_mul, Complex.norm_ofNat]
      rw [h]; linarith [hqk 10 (by norm_num)]
    have e6 : ‖256 * q ^ 11‖ ≤ 256 * r ^ 6 := by
      have h : ‖256 * q ^ 11‖ = 256 * ‖q ^ 11‖ := by
        rw [show (256 : ℂ) * q ^ 11 = 256 * q ^ 11 from rfl, norm_mul, Complex.norm_ofNat]
      rw [h]; linarith [hqk 11 (by norm_num)]
    have e7 : ‖(32 / 3 : ℂ) * q ^ 12‖ ≤ 11 * r ^ 6 := by
      rw [norm_mul]
      have h32 : ‖(32 / 3 : ℂ)‖ = 32 / 3 := by rw [norm_div, Complex.norm_ofNat]; norm_num
      rw [h32]
      linarith [hqk 12 (by norm_num)]
    have e8 : ‖64 * q ^ 13‖ ≤ 64 * r ^ 6 := by
      have h : ‖64 * q ^ 13‖ = 64 * ‖q ^ 13‖ := by
        rw [show (64 : ℂ) * q ^ 13 = 64 * q ^ 13 from rfl, norm_mul, Complex.norm_ofNat]
      rw [h]; linarith [hqk 13 (by norm_num)]
    have e9 : ‖256 * q ^ 14‖ ≤ 256 * r ^ 6 := by
      have h : ‖256 * q ^ 14‖ = 256 * ‖q ^ 14‖ := by
        rw [show (256 : ℂ) * q ^ 14 = 256 * q ^ 14 from rfl, norm_mul, Complex.norm_ofNat]
      rw [h]; linarith [hqk 14 (by norm_num)]
    have e10 : ‖16 * q ^ 16‖ ≤ 16 * r ^ 6 := by
      have h : ‖16 * q ^ 16‖ = 16 * ‖q ^ 16‖ := by
        rw [show (16 : ℂ) * q ^ 16 = 16 * q ^ 16 from rfl, norm_mul, Complex.norm_ofNat]
      rw [h]; linarith [hqk 16 (by norm_num)]
    have e11 : ‖128 * q ^ 17‖ ≤ 128 * r ^ 6 := by
      have h : ‖128 * q ^ 17‖ = 128 * ‖q ^ 17‖ := by
        rw [show (128 : ℂ) * q ^ 17 = 128 * q ^ 17 from rfl, norm_mul, Complex.norm_ofNat]
      rw [h]; linarith [hqk 17 (by norm_num)]
    have e12 : ‖(128 / 5 : ℂ) * q ^ 20‖ ≤ 26 * r ^ 6 := by
      rw [norm_mul]
      have h128 : ‖(128 / 5 : ℂ)‖ = 128 / 5 := by rw [norm_div, Complex.norm_ofNat]; norm_num
      rw [h128]
      linarith [hqk 20 (by norm_num)]
    have hA1 := norm_sub_le (-32 * q ^ 6 + 64 * q ^ 7 - 120 * q ^ 8 - 32 * q ^ 9 + 96 * q ^ 10
      - 256 * q ^ 11 - (32 / 3 : ℂ) * q ^ 12 + 64 * q ^ 13 - 256 * q ^ 14 + 16 * q ^ 16
      - 128 * q ^ 17) ((128 / 5 : ℂ) * q ^ 20)
    have hA2 := norm_sub_le (-32 * q ^ 6 + 64 * q ^ 7 - 120 * q ^ 8 - 32 * q ^ 9 + 96 * q ^ 10
      - 256 * q ^ 11 - (32 / 3 : ℂ) * q ^ 12 + 64 * q ^ 13 - 256 * q ^ 14 + 16 * q ^ 16)
      (128 * q ^ 17)
    have hA3 := norm_add_le (-32 * q ^ 6 + 64 * q ^ 7 - 120 * q ^ 8 - 32 * q ^ 9 + 96 * q ^ 10
      - 256 * q ^ 11 - (32 / 3 : ℂ) * q ^ 12 + 64 * q ^ 13 - 256 * q ^ 14) (16 * q ^ 16)
    have hA4 := norm_sub_le (-32 * q ^ 6 + 64 * q ^ 7 - 120 * q ^ 8 - 32 * q ^ 9 + 96 * q ^ 10
      - 256 * q ^ 11 - (32 / 3 : ℂ) * q ^ 12 + 64 * q ^ 13) (256 * q ^ 14)
    have hA5 := norm_add_le (-32 * q ^ 6 + 64 * q ^ 7 - 120 * q ^ 8 - 32 * q ^ 9 + 96 * q ^ 10
      - 256 * q ^ 11 - (32 / 3 : ℂ) * q ^ 12) (64 * q ^ 13)
    have hA6 := norm_sub_le (-32 * q ^ 6 + 64 * q ^ 7 - 120 * q ^ 8 - 32 * q ^ 9 + 96 * q ^ 10
      - 256 * q ^ 11) ((32 / 3 : ℂ) * q ^ 12)
    have hA7 := norm_sub_le (-32 * q ^ 6 + 64 * q ^ 7 - 120 * q ^ 8 - 32 * q ^ 9 + 96 * q ^ 10)
      (256 * q ^ 11)
    have hA8 := norm_add_le (-32 * q ^ 6 + 64 * q ^ 7 - 120 * q ^ 8 - 32 * q ^ 9) (96 * q ^ 10)
    have hA9 := norm_sub_le (-32 * q ^ 6 + 64 * q ^ 7 - 120 * q ^ 8) (32 * q ^ 9)
    have hA10 := norm_sub_le (-32 * q ^ 6 + 64 * q ^ 7) (120 * q ^ 8)
    have hA11 := norm_add_le (-32 * q ^ 6) (64 * q ^ 7)
    linarith [hA1, hA2, hA3, hA4, hA5, hA6, hA7, hA8, hA9, hA10, hA11,
      e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12]

  have key : 4 * Complex.log ρ - 4 * Complex.log (1 + b) + 8 * q - 12 * q ^ 2
        + (32 / 3 : ℂ) * q ^ 3 - 6 * q ^ 4 + (48 / 5 : ℂ) * q ^ 5
      = 4 * (Complex.log (1 + w) - P5 w) - 4 * (Complex.log (1 + b) - P5 b)
        - 4 * (P5 b - P5 b0)
        + (4 * (P5 w - q ^ 2 + q ^ 4 / 2)
          + (4 * q ^ 2 - 2 * q ^ 4 - 4 * P5 b0 + 8 * q - 12 * q ^ 2 + (32 / 3 : ℂ) * q ^ 3
              - 6 * q ^ 4 + (48 / 5 : ℂ) * q ^ 5)) := by
    rw [hrhow]; ring
  have h1n : ‖Complex.log (1 + w) - P5 w‖ ≤ 64 * r ^ 6 := by
    refine le_trans hlogw ?_
    have hwn : ‖w‖ ≤ 2 * r ^ 2 := by
      rw [hw]
      have h1 := norm_add_le (q ^ 2) a
      have h2 : ‖q ^ 2‖ = ‖q‖ ^ 2 := by rw [norm_pow]
      rw [h2] at h1
      have h3 : ‖q‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hq0 hq 2
      linarith [h1, h3, ha', hMr]
    have h6 : ‖w‖ ^ 6 ≤ (2 * r ^ 2) ^ 6 := pow_le_pow_left₀ (norm_nonneg w) hwn 6
    have h2r : (2 * r ^ 2) ^ 6 = 64 * r ^ 12 := by ring
    have h3 : (64 : ℝ) * r ^ 12 ≤ 64 * r ^ 6 := by
      have h : r ^ 12 ≤ r ^ 6 := pow_le_pow_of_le_one hr0 hr1 (by norm_num)
      linarith
    linarith [h6, h3]
  have h2n : ‖Complex.log (1 + b) - P5 b‖ ≤ 729 * r ^ 6 := by
    refine le_trans hlogb ?_
    have h6 : ‖b‖ ^ 6 ≤ (3 * r) ^ 6 := pow_le_pow_left₀ (norm_nonneg b) hb 6
    calc ‖b‖ ^ 6 ≤ (3 * r) ^ 6 := h6
      _ = 729 * r ^ 6 := by ring
  rw [key]
  have hA := norm_add_le (4 * (Complex.log (1 + w) - P5 w) - 4 * (Complex.log (1 + b) - P5 b)
      - 4 * (P5 b - P5 b0))
    (4 * (P5 w - q ^ 2 + q ^ 4 / 2)
      + (4 * q ^ 2 - 2 * q ^ 4 - 4 * P5 b0 + 8 * q - 12 * q ^ 2 + (32 / 3 : ℂ) * q ^ 3
          - 6 * q ^ 4 + (48 / 5 : ℂ) * q ^ 5))
  have hB1 := norm_sub_le (4 * (Complex.log (1 + w) - P5 w) - 4 * (Complex.log (1 + b) - P5 b))
    (4 * (P5 b - P5 b0))
  have hB2 := norm_sub_le (4 * (Complex.log (1 + w) - P5 w)) (4 * (Complex.log (1 + b) - P5 b))
  have hB3 := norm_add_le (4 * (P5 w - q ^ 2 + q ^ 4 / 2))
    (4 * q ^ 2 - 2 * q ^ 4 - 4 * P5 b0 + 8 * q - 12 * q ^ 2 + (32 / 3 : ℂ) * q ^ 3
      - 6 * q ^ 4 + (48 / 5 : ℂ) * q ^ 5)
  have n1 : ‖4 * (Complex.log (1 + w) - P5 w)‖ ≤ 4 * (64 * r ^ 6) := by
    rw [norm_mul, show ‖(4 : ℂ)‖ = 4 from Complex.norm_ofNat 4]
    linarith [h1n]
  have n2 : ‖4 * (Complex.log (1 + b) - P5 b)‖ ≤ 4 * (729 * r ^ 6) := by
    rw [norm_mul, show ‖(4 : ℂ)‖ = 4 from Complex.norm_ofNat 4]
    linarith [h2n]
  have n3 : ‖4 * (P5 b - P5 b0)‖ ≤ 4 * (2 * (M * r ^ 6)) := by
    rw [norm_mul, show ‖(4 : ℂ)‖ = 4 from Complex.norm_ofNat 4]
    linarith [hPb]
  have n4 : ‖4 * (P5 w - q ^ 2 + q ^ 4 / 2)‖ ≤ 4 * ((2 * M + 1) * r ^ 6) := by
    rw [norm_mul, show ‖(4 : ℂ)‖ = 4 from Complex.norm_ofNat 4]
    linarith [hw6]
  rw [hpoly] at hA hB3 ⊢
  have hsum : 4 * (64 * r ^ 6) + 4 * (729 * r ^ 6) + 4 * (2 * (M * r ^ 6))
      + 4 * ((2 * M + 1) * r ^ 6) + 1101 * r ^ 6 ≤ (5000 + 32 * M) * r ^ 6 := by
    nlinarith [hr6, hM0]
  linarith [hA, hB1, hB2, hB3, n1, n2, n3, n4, hpolyb, hsum]

private lemma Lfun_exp6 : IsSm 6 (fun τ : ℍ =>
    Work.Kernels.LogLambda.Lfun (τ : ℂ)
      - ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + 4 * (Real.log 2 : ℂ)
          - 8 * Work.Residues.Ept τ + 12 * (Work.Residues.Ept τ) ^ 2
          - (32 / 3 : ℂ) * (Work.Residues.Ept τ) ^ 3 + 6 * (Work.Residues.Ept τ) ^ 4
          - (48 / 5 : ℂ) * (Work.Residues.Ept τ) ^ 5)) := by
  refine ⟨5000 + 32 * 4, by norm_num, fun τ hτ => ?_⟩
  change ‖Work.Kernels.LogLambda.Lfun (τ : ℂ)
      - ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + 4 * (Real.log 2 : ℂ)
          - 8 * Work.Residues.Ept τ + 12 * (Work.Residues.Ept τ) ^ 2
          - (32 / 3 : ℂ) * (Work.Residues.Ept τ) ^ 3 + 6 * (Work.Residues.Ept τ) ^ 4
          - (48 / 5 : ℂ) * (Work.Residues.Ept τ) ^ 5)‖
      ≤ (5000 + 32 * 4) * ‖Work.Residues.Ept τ‖ ^ 6
  set q : ℂ := Work.Residues.Ept τ with hq
  have hr8 : ‖q‖ ≤ 1 / 8 := by
    rw [hq]
    exact (Work.Residues.norm_Ept_le_exp_neg_pi τ (Work.Asymptotics.Funnel.im_one hτ)).trans
      exp_neg_pi_le_eighth
  have hq0 : (0 : ℝ) ≤ ‖q‖ := norm_nonneg q
  have hLU : Work.Kernels.LogLambda.Lfun (τ : ℂ)
      = (Real.pi : ℂ) * Complex.I * (τ : ℂ) + 4 * (Real.log 2 : ℂ)
        + 4 * Complex.log (jacobiTheta₂ ((τ : ℂ) / 2) (τ : ℂ) / 2)
        - 4 * Complex.log (Work.Kernels.theta00Fun τ) := by
    have hmem : (τ : ℂ) ∈ Work.Kernels.LogLambda.W := by
      show (1 / 2 : ℝ) < (τ : ℂ).im
      rw [UpperHalfPlane.coe_im]
      exact lt_of_lt_of_le (by norm_num) (Work.Asymptotics.Funnel.im_one hτ)
    rw [Work.Kernels.LogLambda.Lfun_eq_LU_on_W (τ : ℂ) hmem, Work.Kernels.LogLambda.LU,
      Work.Kernels.LogLambda.thetaC10_div_exp]
    simp only [Work.Kernels.LogLambda.thetaC00, Work.Kernels.theta00Fun]
  have hrho : ‖jacobiTheta₂ ((τ : ℂ) / 2) (τ : ℂ) / 2 - 1 - q ^ 2‖ ≤ 4 * ‖q‖ ^ 6 := by
    have him : (1 : ℝ) ≤ (τ : ℂ).im := by
      rw [UpperHalfPlane.coe_im]; exact Work.Asymptotics.Funnel.im_one hτ
    have h := psi_ratio_fourth (τ : ℂ) him
    have he : Complex.exp (Real.pi * Complex.I * (τ : ℂ)) = q := by
      rw [hq]; exact (Work.Residues.Ept_apply τ).symm
    rw [he] at h
    have hq6 : (0 : ℝ) ≤ ‖q‖ ^ 6 := pow_nonneg (norm_nonneg q) 6
    linarith [h, hq6]
  have hB : ‖(Work.Kernels.theta00Fun τ - 1) - 2 * q - 2 * q ^ 4‖ ≤ 4 * ‖q‖ ^ 6 := by
    have h : (Work.Kernels.theta00Fun τ - 1) - 2 * q - 2 * q ^ 4
        = Work.Asymptotics.KhatE1.theta00Rem τ := by
      rw [hq]; simp only [Work.Asymptotics.KhatE1.theta00Rem]; try ring
    have hx : ‖Work.Asymptotics.KhatE1.theta00Rem τ‖ ≤ 4 * ‖q‖ ^ 6 := by
      have h2 := theta00Rem_bound τ (Work.Asymptotics.Funnel.im_two hτ)
      simpa [hq] using h2
    calc ‖(Work.Kernels.theta00Fun τ - 1) - 2 * q - 2 * q ^ 4‖
        = ‖Work.Asymptotics.KhatE1.theta00Rem τ‖ := by rw [h]
      _ ≤ 4 * ‖q‖ ^ 6 := hx
  have hb : ‖Work.Kernels.theta00Fun τ - 1‖ ≤ 3 * ‖q‖ := by
    have h1 : ‖Work.Kernels.theta00Fun τ - 1‖
        ≤ ‖Work.Asymptotics.KhatE1.theta00Rem τ‖ + ‖(2 : ℂ) * q + (2 : ℂ) * q ^ 4‖ := by
      have h : Work.Kernels.theta00Fun τ - 1
          = Work.Asymptotics.KhatE1.theta00Rem τ + ((2 : ℂ) * q + (2 : ℂ) * q ^ 4) := by
        rw [hq]; simp only [Work.Asymptotics.KhatE1.theta00Rem]; try ring
      rw [h]; exact norm_add_le _ _
    have h2 : ‖(2 : ℂ) * q + (2 : ℂ) * q ^ 4‖ ≤ 2 * ‖q‖ + 2 * ‖q‖ ^ 4 := by
      have h := norm_add_le ((2 : ℂ) * q) ((2 : ℂ) * q ^ 4)
      have e1 : ‖(2 : ℂ) * q‖ = 2 * ‖q‖ := by rw [norm_mul, Complex.norm_ofNat]
      have e2 : ‖(2 : ℂ) * q ^ 4‖ = 2 * ‖q‖ ^ 4 := by rw [norm_mul, Complex.norm_ofNat, norm_pow]
      simpa only [e1, e2] using h
    have h4 : ‖q‖ ^ 4 ≤ ‖q‖ * (1 / 8) ^ 3 := by
      have h := pow_le_pow_left₀ hq0 hr8 3
      nlinarith [h, hq0]
    have h6 : 4 * ‖q‖ ^ 6 ≤ ‖q‖ * (1 / 8) ^ 3 := by
      have h := pow_le_pow_left₀ hq0 hr8 5
      nlinarith [h, hq0]
    have hx : ‖Work.Asymptotics.KhatE1.theta00Rem τ‖ ≤ 4 * ‖q‖ ^ 6 := by
      have h2 := theta00Rem_bound τ (Work.Asymptotics.Funnel.im_two hτ)
      simpa [hq] using h2
    linarith [h1, h2, h4, h6, hx, hq0]
  have hMr : (4 : ℝ) * ‖q‖ ^ 6 ≤ ‖q‖ ^ 2 := by
    have h4 : ‖q‖ ^ 4 ≤ (1 / 8 : ℝ) ^ 4 := pow_le_pow_left₀ hq0 hr8 4
    have h5 : (1 / 8 : ℝ) ^ 4 = 1 / 4096 := by norm_num
    nlinarith [h4, h5, hq0, pow_nonneg hq0 2]
  have hlog := log_ratio_Lfun_expansion
    (ρ := jacobiTheta₂ ((τ : ℂ) / 2) (τ : ℂ) / 2)
    (b := Work.Kernels.theta00Fun τ - 1) (q := q) (M := 4)
    (by norm_num) hq0 hr8 (le_rfl) hb hMr hrho hB
  have hkey : Work.Kernels.LogLambda.Lfun (τ : ℂ)
      - ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + 4 * (Real.log 2 : ℂ)
          - 8 * q + 12 * q ^ 2 - (32 / 3 : ℂ) * q ^ 3 + 6 * q ^ 4 - (48 / 5 : ℂ) * q ^ 5)
      = 4 * Complex.log (jacobiTheta₂ ((τ : ℂ) / 2) (τ : ℂ) / 2)
        - 4 * Complex.log (1 + (Work.Kernels.theta00Fun τ - 1))
        + 8 * q - 12 * q ^ 2 + (32 / 3 : ℂ) * q ^ 3 - 6 * q ^ 4 + (48 / 5 : ℂ) * q ^ 5 := by
    rw [hLU, show Work.Kernels.theta00Fun τ = 1 + (Work.Kernels.theta00Fun τ - 1) from by ring]
    ring
  rw [hkey]
  exact hlog

/-- `πiτ + c` with `c = cuspC ℓ`. -/
noncomputable def cuspLin (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  (Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ

/-- `xi2Rem2 τ = ξ₂ - (2 + 48q + 48q²)`. -/
noncomputable def xi2Rem2 (τ : ℍ) : ℂ :=
  Work.Kernels.xi2Fun τ
    - (2 + 48 * Work.Kernels.qParamFun τ + 48 * Work.Kernels.qParamFun τ ^ 2)

/-- `xi4Rem2 τ = ξ₄ - (2 - 288q - 1824q²)`. -/
noncomputable def xi4Rem2 (τ : ℍ) : ℂ :=
  Work.Kernels.xi4Fun τ
    - (2 - 288 * Work.Kernels.qParamFun τ - 1824 * Work.Kernels.qParamFun τ ^ 2)

/-- `(𝓛 - 𝓛_S/2) - (Λ + 12q + 6q²)`. -/
noncomputable def LplusRem2 (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  (ℓ.L τ - ℓ.L_S τ / 2)
    - (cuspLin ℓ τ + 12 * Work.Kernels.qParamFun τ + 6 * Work.Kernels.qParamFun τ ^ 2)

/-- `V𝓛_S + 256q + (4096/3)q²`. -/
noncomputable def VLSRem2 (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) : ℂ :=
  Work.Kernels.VFun τ * ℓ.L_S τ + 256 * Work.Kernels.qParamFun τ
    + (4096 / 3 : ℂ) * Work.Kernels.qParamFun τ ^ 2

private lemma cuspLin_bound (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    ‖cuspLin ℓ τ‖ ≤ (Real.pi + 4) * Work.Kernels.scale τ := by
  have hc : Work.Asymptotics.Compact.cuspC ℓ = 4 * (Real.log 2 : ℂ) :=
    Work.Asymptotics.CuspL_eq ℓ
  have hlog0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog1 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlog : ‖(4 : ℂ) * (Real.log 2 : ℂ)‖ ≤ 4 := by
    rw [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog0]
    linarith
  have hπ : ‖(Real.pi : ℂ) * Complex.I * (τ : ℂ)‖ ≤ Real.pi * Work.Kernels.scale τ := by
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    have h := Work.Kernels.coe_norm_le_scale τ
    nlinarith [Real.pi_pos]
  rw [cuspLin, hc]
  calc ‖(Real.pi : ℂ) * Complex.I * (τ : ℂ) + 4 * (Real.log 2 : ℂ)‖
      ≤ ‖(Real.pi : ℂ) * Complex.I * (τ : ℂ)‖ + ‖(4 : ℂ) * (Real.log 2 : ℂ)‖ := norm_add_le _ _
    _ ≤ Real.pi * Work.Kernels.scale τ + 4 := add_le_add hπ hlog
    _ ≤ (Real.pi + 4) * Work.Kernels.scale τ := by
        have h := Work.Kernels.one_le_scale τ
        nlinarith

private lemma isSm_xi2Rem2 : IsSm 6 xi2Rem2 := by
  refine IsSm.congr xi2_exp6 (fun τ => ?_)
  rw [xi2Rem2, Work.Asymptotics.Small.qParamFun_eq_Ept_sq τ]
  try ring

private lemma isSm_xi4Rem2 : IsSm 6 xi4Rem2 := by
  refine IsSm.congr xi4_exp6 (fun τ => ?_)
  rw [xi4Rem2, Work.Asymptotics.Small.qParamFun_eq_Ept_sq τ]
  try ring

private lemma isSm_LplusRem2 (ℓ : Work.Kernels.LogLambdaData) : IsSm 6 (LplusRem2 ℓ) := by
  have hL : IsSm 6 (fun τ : ℍ => ℓ.L τ - ((Real.pi : ℂ) * Complex.I * (τ : ℂ)
      + Work.Asymptotics.Compact.cuspC ℓ) + 8 * Work.Residues.Ept τ
      - 12 * (Work.Residues.Ept τ) ^ 2 + (32 / 3 : ℂ) * (Work.Residues.Ept τ) ^ 3
      - 6 * (Work.Residues.Ept τ) ^ 4 + (48 / 5 : ℂ) * (Work.Residues.Ept τ) ^ 5) := by
    refine IsSm.congr Lfun_exp6 (fun τ => ?_)
    rw [Work.Asymptotics.LogLambdaData_L_eq_Lfun ℓ τ,
      show Work.Asymptotics.Compact.cuspC ℓ = 4 * (Real.log 2 : ℂ)
        from Work.Asymptotics.CuspL_eq ℓ]
    ring
  have hS : IsSm 6 (fun τ : ℍ => ℓ.L_S τ + 16 * Work.Residues.Ept τ
      + (64 / 3 : ℂ) * (Work.Residues.Ept τ) ^ 3
      + (96 / 5 : ℂ) * (Work.Residues.Ept τ) ^ 5) := by
    refine IsSm.congr_on LamS_exp6 (fun τ hτ => ?_)
    rw [Work.Residues.LogLambdaData_LS_eq_LamS ℓ τ (lt_of_lt_of_le (by norm_num)
      (Work.Asymptotics.Funnel.im_one hτ))]
  have h0 : IsSm 6 (fun _ : ℍ => (0 : ℂ)) :=
    ⟨1, one_pos, fun τ _ => by simp⟩
  refine IsSm.congr_on (((hL.sub (hS.const_mul (1 / 2))).add h0)) (fun τ hτ => ?_)
  rw [LplusRem2, cuspLin, Work.Asymptotics.Small.qParamFun_eq_Ept_sq τ]
  ring

private lemma isSm_VLSRem2 (ℓ : Work.Kernels.LogLambdaData) : IsSm 6 (VLSRem2 ℓ) := by
  have hPV0 : IsSm 0 (fun τ : ℍ => 16 * Work.Residues.Ept τ + 64 * (Work.Residues.Ept τ) ^ 3
      + 96 * (Work.Residues.Ept τ) ^ 5) := by
    refine IsSm.bdd (B := 200) (by norm_num) (fun τ hτ => ?_)
    have he := ept_norm_le_one hτ
    have h1 : ‖(16 : ℂ) * Work.Residues.Ept τ‖ ≤ 16 := by
      rw [norm_mul, Complex.norm_ofNat]; linarith
    have h3 : ‖(64 : ℂ) * (Work.Residues.Ept τ) ^ 3‖ ≤ 64 := by
      rw [norm_mul, Complex.norm_ofNat, norm_pow]
      have h : ‖Work.Residues.Ept τ‖ ^ 3 ≤ 1 := pow_le_one₀ (norm_nonneg _) he
      nlinarith
    have h5 : ‖(96 : ℂ) * (Work.Residues.Ept τ) ^ 5‖ ≤ 96 := by
      rw [norm_mul, Complex.norm_ofNat, norm_pow]
      have h : ‖Work.Residues.Ept τ‖ ^ 5 ≤ 1 := pow_le_one₀ (norm_nonneg _) he
      nlinarith
    have hA := norm_add_le (((16 : ℂ) * Work.Residues.Ept τ
      + (64 : ℂ) * (Work.Residues.Ept τ) ^ 3)) ((96 : ℂ) * (Work.Residues.Ept τ) ^ 5)
    have hB := norm_add_le ((16 : ℂ) * Work.Residues.Ept τ)
      ((64 : ℂ) * (Work.Residues.Ept τ) ^ 3)
    linarith [hA, hB, h1, h3, h5]
  have hPS0 : IsSm 0 (fun τ : ℍ => 16 * Work.Residues.Ept τ
      + (64 / 3 : ℂ) * (Work.Residues.Ept τ) ^ 3
      + (96 / 5 : ℂ) * (Work.Residues.Ept τ) ^ 5) := by
    refine IsSm.bdd (B := 200) (by norm_num) (fun τ hτ => ?_)
    have he := ept_norm_le_one hτ
    have h1 : ‖(16 : ℂ) * Work.Residues.Ept τ‖ ≤ 16 := by
      rw [norm_mul, Complex.norm_ofNat]; linarith
    have h3 : ‖((64 / 3 : ℂ)) * (Work.Residues.Ept τ) ^ 3‖ ≤ 22 := by
      rw [norm_mul, norm_pow]
      have hc : ‖((64 / 3 : ℂ))‖ = 64 / 3 := by rw [norm_div, Complex.norm_ofNat]; norm_num
      rw [hc]
      have h : ‖Work.Residues.Ept τ‖ ^ 3 ≤ 1 := pow_le_one₀ (norm_nonneg _) he
      nlinarith
    have h5 : ‖((96 / 5 : ℂ)) * (Work.Residues.Ept τ) ^ 5‖ ≤ 20 := by
      rw [norm_mul, norm_pow]
      have hc : ‖((96 / 5 : ℂ))‖ = 96 / 5 := by rw [norm_div, Complex.norm_ofNat]; norm_num
      rw [hc]
      have h : ‖Work.Residues.Ept τ‖ ^ 5 ≤ 1 := pow_le_one₀ (norm_nonneg _) he
      nlinarith
    have hA := norm_add_le (((16 : ℂ) * Work.Residues.Ept τ
      + ((64 / 3 : ℂ)) * (Work.Residues.Ept τ) ^ 3))
      (((96 / 5 : ℂ)) * (Work.Residues.Ept τ) ^ 5)
    have hB := norm_add_le ((16 : ℂ) * Work.Residues.Ept τ)
      (((64 / 3 : ℂ)) * (Work.Residues.Ept τ) ^ 3)
    linarith [hA, hB, h1, h3, h5]
  have hV : IsSm 6 (fun τ : ℍ => Work.Kernels.VFun τ
      - (16 * Work.Residues.Ept τ + 64 * (Work.Residues.Ept τ) ^ 3
        + 96 * (Work.Residues.Ept τ) ^ 5)) := V_exp6
  have hS : IsSm 6 (fun τ : ℍ => ℓ.L_S τ + 16 * Work.Residues.Ept τ
      + (64 / 3 : ℂ) * (Work.Residues.Ept τ) ^ 3
      + (96 / 5 : ℂ) * (Work.Residues.Ept τ) ^ 5) := by
    refine IsSm.congr_on LamS_exp6 (fun τ hτ => ?_)
    have him : (1 / 2 : ℝ) < τ.im := lt_of_lt_of_le (by norm_num) (Work.Asymptotics.Funnel.im_one hτ)
    rw [Work.Residues.LogLambdaData_LS_eq_LamS ℓ τ him]
  have hres : IsSm 6 (fun τ : ℍ => -((48128 / 15 : ℂ)) * (Work.Residues.Ept τ) ^ 6
      - (16384 / 5 : ℂ) * (Work.Residues.Ept τ) ^ 8
      - (9216 / 5 : ℂ) * (Work.Residues.Ept τ) ^ 10) :=
    IsSm.congr (IsSm_add6 (IsSm_add6 (isSm6_pow (-(48128 / 15)) 6 le_rfl)
      (isSm6_pow (-(16384 / 5)) 8 (by norm_num)))
      (isSm6_pow (-(9216 / 5)) 10 (by norm_num))) (fun τ => by ring)
  have hcomb : IsSm 6 (fun τ : ℍ => -1 * ((Work.Kernels.VFun τ
        - (16 * Work.Residues.Ept τ + 64 * (Work.Residues.Ept τ) ^ 3
          + 96 * (Work.Residues.Ept τ) ^ 5))
        * (16 * Work.Residues.Ept τ + (64 / 3 : ℂ) * (Work.Residues.Ept τ) ^ 3
          + (96 / 5 : ℂ) * (Work.Residues.Ept τ) ^ 5))
      + (16 * Work.Residues.Ept τ + 64 * (Work.Residues.Ept τ) ^ 3
          + 96 * (Work.Residues.Ept τ) ^ 5)
        * (ℓ.L_S τ + 16 * Work.Residues.Ept τ
          + (64 / 3 : ℂ) * (Work.Residues.Ept τ) ^ 3
          + (96 / 5 : ℂ) * (Work.Residues.Ept τ) ^ 5)
      + (Work.Kernels.VFun τ - (16 * Work.Residues.Ept τ + 64 * (Work.Residues.Ept τ) ^ 3
          + 96 * (Work.Residues.Ept τ) ^ 5)) * (ℓ.L_S τ + 16 * Work.Residues.Ept τ
          + (64 / 3 : ℂ) * (Work.Residues.Ept τ) ^ 3
          + (96 / 5 : ℂ) * (Work.Residues.Ept τ) ^ 5)
      + (-((48128 / 15 : ℂ)) * (Work.Residues.Ept τ) ^ 6
        - (16384 / 5 : ℂ) * (Work.Residues.Ept τ) ^ 8
        - (9216 / 5 : ℂ) * (Work.Residues.Ept τ) ^ 10)) :=
    IsSm.congr (((((IsSm.const_mul (-1)
        (hV.mul hPS0)).add (hPV0.mul hS)).add ((hV.mul hS).mono (l := 6) (by norm_num))).add hres))
      (fun τ => by ring)
  refine IsSm.congr_on hcomb (fun τ hτ => ?_)
  rw [VLSRem2, Work.Asymptotics.Small.qParamFun_eq_Ept_sq τ]
  ring

/-! ## The `O(scale · ‖e‖⁶)` calculus -/

private def IsSmS (f : ℍ → ℂ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, Work.Asymptotics.Funnel τ →
    ‖f τ‖ ≤ C * Work.Kernels.scale τ * ‖Work.Residues.Ept τ‖ ^ 6

private lemma IsSmS_add {f g : ℍ → ℂ} (hf : IsSmS f) (hg : IsSmS g) :
    IsSmS (fun τ => f τ + g τ) := by
  obtain ⟨Cf, hCf, hf⟩ := hf
  obtain ⟨Cg, hCg, hg⟩ := hg
  refine ⟨Cf + Cg, by positivity, fun τ hτ => ?_⟩
  have h1 := hf τ hτ
  have h2 := hg τ hτ
  have h3 := norm_add_le (f τ) (g τ)
  calc ‖f τ + g τ‖ ≤ Cf * Work.Kernels.scale τ * ‖Work.Residues.Ept τ‖ ^ 6
        + Cg * Work.Kernels.scale τ * ‖Work.Residues.Ept τ‖ ^ 6 := le_trans h3 (add_le_add h1 h2)
    _ = (Cf + Cg) * Work.Kernels.scale τ * ‖Work.Residues.Ept τ‖ ^ 6 := by ring

private lemma IsSmS_const_mul (c : ℂ) {f : ℍ → ℂ} (hf : IsSmS f) :
    IsSmS (fun τ => c * f τ) := by
  obtain ⟨Cf, hCf, hf⟩ := hf
  refine ⟨‖c‖ * Cf + 1, by positivity, fun τ hτ => ?_⟩
  have hs : (0 : ℝ) ≤ Work.Kernels.scale τ := le_of_lt (Work.Kernels.scale_pos τ)
  have he : (0 : ℝ) ≤ ‖Work.Residues.Ept τ‖ ^ 6 := by positivity
  have h1 := hf τ hτ
  rw [norm_mul]
  have h0 : (0 : ℝ) ≤ Work.Kernels.scale τ * ‖Work.Residues.Ept τ‖ ^ 6 := mul_nonneg hs he
  calc ‖c‖ * ‖f τ‖ ≤ ‖c‖ * (Cf * Work.Kernels.scale τ * ‖Work.Residues.Ept τ‖ ^ 6) :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = (‖c‖ * Cf) * (Work.Kernels.scale τ * ‖Work.Residues.Ept τ‖ ^ 6) := by ring
    _ ≤ (‖c‖ * Cf + 1) * Work.Kernels.scale τ * ‖Work.Residues.Ept τ‖ ^ 6 := by
        nlinarith [h0, norm_nonneg c, hCf.le]

private lemma IsSmS_of_isSm {f : ℍ → ℂ} (hf : IsSm 6 f) : IsSmS f := by
  obtain ⟨C, hC, hf⟩ := hf
  refine ⟨C + 1, by positivity, fun τ hτ => ?_⟩
  have hs : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
  have he : (0 : ℝ) ≤ ‖Work.Residues.Ept τ‖ ^ 6 := by positivity
  have h1 := hf τ hτ
  have h' : ‖Work.Residues.Ept τ‖ ^ 6 ≤ Work.Kernels.scale τ * ‖Work.Residues.Ept τ‖ ^ 6 := by
    nlinarith [hs, he]
  have hsc : (0 : ℝ) ≤ Work.Kernels.scale τ * ‖Work.Residues.Ept τ‖ ^ 6 :=
    mul_nonneg (by linarith) he
  calc ‖f τ‖ ≤ C * ‖Work.Residues.Ept τ‖ ^ 6 := h1
    _ ≤ C * (Work.Kernels.scale τ * ‖Work.Residues.Ept τ‖ ^ 6) :=
        mul_le_mul_of_nonneg_left h' hC.le
    _ ≤ (C + 1) * (Work.Kernels.scale τ * ‖Work.Residues.Ept τ‖ ^ 6) :=
        mul_le_mul_of_nonneg_right (by linarith) hsc
    _ = (C + 1) * Work.Kernels.scale τ * ‖Work.Residues.Ept τ‖ ^ 6 := by ring

private lemma IsSmS_of_isSm' {k : ℕ} (hk : 6 ≤ k) {f : ℍ → ℂ} (hf : IsSm k f) : IsSmS f :=
  IsSmS_of_isSm (hf.mono hk)

private lemma IsSmS_lam_mul (ℓ : Work.Kernels.LogLambdaData) {f : ℍ → ℂ} (hf : IsSm 6 f) :
    IsSmS (fun τ => cuspLin ℓ τ * f τ) := by
  obtain ⟨C, hC, hf⟩ := hf
  refine ⟨(Real.pi + 4) * C + 1, by positivity, fun τ hτ => ?_⟩
  have h1 := cuspLin_bound ℓ τ
  have h2 := hf τ hτ
  have hs : (0 : ℝ) ≤ Work.Kernels.scale τ := le_of_lt (Work.Kernels.scale_pos τ)
  have he : (0 : ℝ) ≤ ‖Work.Residues.Ept τ‖ ^ 6 := by positivity
  have hp : (0 : ℝ) ≤ Real.pi + 4 := by linarith [Real.pi_pos]
  rw [norm_mul]
  have h0 : (0 : ℝ) ≤ Work.Kernels.scale τ * ‖Work.Residues.Ept τ‖ ^ 6 := mul_nonneg hs he
  calc ‖cuspLin ℓ τ‖ * ‖f τ‖
      ≤ ((Real.pi + 4) * Work.Kernels.scale τ) * (C * ‖Work.Residues.Ept τ‖ ^ 6) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = ((Real.pi + 4) * C) * (Work.Kernels.scale τ * ‖Work.Residues.Ept τ‖ ^ 6) := by ring
    _ ≤ ((Real.pi + 4) * C + 1) * Work.Kernels.scale τ * ‖Work.Residues.Ept τ‖ ^ 6 := by
        nlinarith [h0, hp, hC.le]

private lemma IsSmS_congr_on {f g : ℍ → ℂ} (hf : IsSmS f)
    (hfg : ∀ τ, Work.Asymptotics.Funnel τ → f τ = g τ) : IsSmS g := by
  obtain ⟨C, hC, hf⟩ := hf
  exact ⟨C, hC, fun τ hτ => by rw [← hfg τ hτ]; exact hf τ hτ⟩

/-! ## The two decomposition identities -/

private lemma xi2Rem2_eq (τ : ℍ) : xi2Rem2 τ = Work.Kernels.UFun τ + Work.Kernels.WFun τ
    - (2 + 48 * Work.Kernels.qParamFun τ + 48 * Work.Kernels.qParamFun τ ^ 2) := by
  rw [xi2Rem2, Work.Kernels.xi2Fun]

private lemma xi4Rem2_eq (τ : ℍ) : xi4Rem2 τ = Work.Kernels.UFun τ ^ 2 + Work.Kernels.WFun τ ^ 2
    - 2 * Work.Kernels.VFun τ ^ 2
    - (2 - 288 * Work.Kernels.qParamFun τ - 1824 * Work.Kernels.qParamFun τ ^ 2) := by
  rw [xi4Rem2, Work.Kernels.xi4Fun]

private lemma psi2_decomp (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    Work.Kernels.psi2 ℓ τ
        - 2 * cuspLin ℓ τ - (48 * cuspLin ℓ τ + 408) * Work.Kernels.qParamFun τ
        - (48 * cuspLin ℓ τ + 2636) * Work.Kernels.qParamFun τ ^ 2
      = xi2Rem2 τ * cuspLin ℓ τ + 12 * Work.Kernels.qParamFun τ * xi2Rem2 τ
        + 2 * LplusRem2 ℓ τ + 48 * Work.Kernels.qParamFun τ * LplusRem2 ℓ τ
        + xi2Rem2 τ * LplusRem2 ℓ τ + 6 * Work.Kernels.qParamFun τ ^ 2 * xi2Rem2 τ
        + 48 * Work.Kernels.qParamFun τ ^ 2 * LplusRem2 ℓ τ
        + 864 * Work.Kernels.qParamFun τ ^ 3 + 288 * Work.Kernels.qParamFun τ ^ 4
        + (-(3 / 2)) * VLSRem2 ℓ τ := by
  have hψ : Work.Kernels.psi2 ℓ τ = Work.Kernels.xi2Fun τ * ℓ.L τ
      + (-(Work.Kernels.UFun τ + Work.Kernels.VFun τ)) * ℓ.L_S τ := by
    rw [Work.Kernels.psi2, Work.Kernels.KernelFacts.xi2Fun_slash_S]
  have hY : LplusRem2 ℓ τ = (ℓ.L τ - ℓ.L_S τ / 2)
      - (cuspLin ℓ τ + 12 * Work.Kernels.qParamFun τ + 6 * Work.Kernels.qParamFun τ ^ 2) := rfl
  have hZ : VLSRem2 ℓ τ = Work.Kernels.VFun τ * ℓ.L_S τ + 256 * Work.Kernels.qParamFun τ
      + (4096 / 3 : ℂ) * Work.Kernels.qParamFun τ ^ 2 := rfl
  have hxi2 : Work.Kernels.xi2Fun τ = Work.Kernels.UFun τ + Work.Kernels.WFun τ := rfl
  rw [hψ, hxi2, xi2Rem2_eq τ, hY, hZ, cuspLin, Work.Kernels.TildeFacts.theta_quartic τ]
  ring

private lemma psi4_decomp (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    Work.Kernels.psi4 ℓ τ
        - 2 * cuspLin ℓ τ + (288 * cuspLin ℓ τ + 744) * Work.Kernels.qParamFun τ
        + (1824 * cuspLin ℓ τ + 25972) * Work.Kernels.qParamFun τ ^ 2
      = xi4Rem2 τ * cuspLin ℓ τ + 12 * Work.Kernels.qParamFun τ * xi4Rem2 τ
        + 2 * LplusRem2 ℓ τ + (-288) * Work.Kernels.qParamFun τ * LplusRem2 ℓ τ
        + xi4Rem2 τ * LplusRem2 ℓ τ + 6 * Work.Kernels.qParamFun τ ^ 2 * xi4Rem2 τ
        + (-1824) * Work.Kernels.qParamFun τ ^ 2 * LplusRem2 ℓ τ
        + 3 * VLSRem2 ℓ τ + (-384) * Work.Kernels.qParamFun τ * xi2Rem2 τ
        + 72 * Work.Kernels.qParamFun τ * VLSRem2 ℓ τ
        + (3 / 2) * VLSRem2 ℓ τ * xi2Rem2 τ
        + 72 * Work.Kernels.qParamFun τ ^ 2 * VLSRem2 ℓ τ
        + (-2048) * Work.Kernels.qParamFun τ ^ 2 * xi2Rem2 τ
        + (-109248) * Work.Kernels.qParamFun τ ^ 4
        + (-140352) * Work.Kernels.qParamFun τ ^ 3 := by
  have hψ : Work.Kernels.psi4 ℓ τ = Work.Kernels.xi4Fun τ * ℓ.L τ
      + (Work.Kernels.UFun τ ^ 2 + Work.Kernels.VFun τ ^ 2 - 2 * Work.Kernels.WFun τ ^ 2)
          * ℓ.L_S τ := by
    rw [Work.Kernels.psi4, Work.Kernels.KernelFacts.xi4S_apply]
  have hY : LplusRem2 ℓ τ = (ℓ.L τ - ℓ.L_S τ / 2)
      - (cuspLin ℓ τ + 12 * Work.Kernels.qParamFun τ + 6 * Work.Kernels.qParamFun τ ^ 2) := rfl
  have hZ : VLSRem2 ℓ τ = Work.Kernels.VFun τ * ℓ.L_S τ + 256 * Work.Kernels.qParamFun τ
      + (4096 / 3 : ℂ) * Work.Kernels.qParamFun τ ^ 2 := rfl
  have hxi4 : Work.Kernels.xi4Fun τ = Work.Kernels.UFun τ ^ 2 + Work.Kernels.WFun τ ^ 2
      - 2 * Work.Kernels.VFun τ ^ 2 := rfl
  have hxi2 : Work.Kernels.xi2Fun τ = Work.Kernels.UFun τ + Work.Kernels.WFun τ := rfl
  rw [hψ, hxi4, xi4Rem2_eq τ, xi2Rem2_eq τ, hY, hZ, cuspLin,
    Work.Kernels.TildeFacts.theta_quartic τ]
  ring

theorem psi_second_order (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : UpperHalfPlane, Work.Asymptotics.Funnel τ →
      ‖Work.Kernels.psi2 ℓ τ
          - 2 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ)
          - (48 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ) + 408)
              * Work.Kernels.qParamFun τ
          - (48 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ) + 2636)
              * Work.Kernels.qParamFun τ ^ 2‖
        ≤ C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖ ^ 3 ∧
      ‖Work.Kernels.psi4 ℓ τ
          - 2 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ)
          + (288 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ) + 744)
              * Work.Kernels.qParamFun τ
          + (1824 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ) + 25972)
              * Work.Kernels.qParamFun τ ^ 2‖
        ≤ C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖ ^ 3 := by
  have hX : IsSm 6 xi2Rem2 := isSm_xi2Rem2
  have hX4 : IsSm 6 xi4Rem2 := isSm_xi4Rem2
  have hY : IsSm 6 (LplusRem2 ℓ) := isSm_LplusRem2 ℓ
  have hZ : IsSm 6 (VLSRem2 ℓ) := isSm_VLSRem2 ℓ
  have hq : IsSm 2 (fun τ : ℍ => Work.Kernels.qParamFun τ) := isSm_qParam
  have t1 : IsSmS (fun τ : ℍ => xi2Rem2 τ * cuspLin ℓ τ) :=
    IsSmS_congr_on (IsSmS_lam_mul ℓ hX) (fun τ _ => by ring)
  have t2 : IsSmS (fun τ : ℍ => 12 * Work.Kernels.qParamFun τ * xi2Rem2 τ) :=
    IsSmS_of_isSm' (k := 8) (by norm_num) ((IsSm.const_mul 12 hq).mul hX)
  have t3 : IsSmS (fun τ : ℍ => 2 * LplusRem2 ℓ τ) :=
    IsSmS_of_isSm' le_rfl (IsSm.const_mul 2 hY)
  have t4 : IsSmS (fun τ : ℍ => 48 * Work.Kernels.qParamFun τ * LplusRem2 ℓ τ) :=
    IsSmS_of_isSm' (k := 8) (by norm_num) ((IsSm.const_mul 48 hq).mul hY)
  have t5 : IsSmS (fun τ : ℍ => xi2Rem2 τ * LplusRem2 ℓ τ) :=
    IsSmS_of_isSm' (k := 12) (by norm_num) (hX.mul hY)
  have t6 : IsSmS (fun τ : ℍ => 6 * Work.Kernels.qParamFun τ ^ 2 * xi2Rem2 τ) :=
    IsSmS_of_isSm' (k := 10) (by norm_num) ((IsSm.const_mul 6 (hq.pow 2)).mul hX)
  have t7 : IsSmS (fun τ : ℍ => 48 * Work.Kernels.qParamFun τ ^ 2 * LplusRem2 ℓ τ) :=
    IsSmS_of_isSm' (k := 10) (by norm_num) ((IsSm.const_mul 48 (hq.pow 2)).mul hY)
  have t8 : IsSmS (fun τ : ℍ => 864 * Work.Kernels.qParamFun τ ^ 3) :=
    IsSmS_of_isSm' le_rfl (IsSm.const_mul 864 (hq.pow 3))
  have t9 : IsSmS (fun τ : ℍ => 288 * Work.Kernels.qParamFun τ ^ 4) :=
    IsSmS_of_isSm' (k := 8) (by norm_num) (IsSm.const_mul 288 (hq.pow 4))
  have t10 : IsSmS (fun τ : ℍ => (-(3 / 2)) * VLSRem2 ℓ τ) :=
    IsSmS_of_isSm' le_rfl (IsSm.const_mul (-(3 / 2)) hZ)
  have hsum2 : IsSmS (fun τ : ℍ =>
      xi2Rem2 τ * cuspLin ℓ τ
        + 12 * Work.Kernels.qParamFun τ * xi2Rem2 τ
        + 2 * LplusRem2 ℓ τ
        + 48 * Work.Kernels.qParamFun τ * LplusRem2 ℓ τ
        + xi2Rem2 τ * LplusRem2 ℓ τ
        + 6 * Work.Kernels.qParamFun τ ^ 2 * xi2Rem2 τ
        + 48 * Work.Kernels.qParamFun τ ^ 2 * LplusRem2 ℓ τ
        + 864 * Work.Kernels.qParamFun τ ^ 3
        + 288 * Work.Kernels.qParamFun τ ^ 4
        + (-(3 / 2)) * VLSRem2 ℓ τ) :=
    IsSmS_add (IsSmS_add (IsSmS_add (IsSmS_add (IsSmS_add (IsSmS_add (IsSmS_add (IsSmS_add (IsSmS_add (t1) (t2)) (t3)) (t4)) (t5)) (t6)) (t7)) (t8)) (t9)) (t10)
  have hP2 : IsSmS (fun τ : ℍ => Work.Kernels.psi2 ℓ τ
      - 2 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ)
      - (48 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ) + 408)
          * Work.Kernels.qParamFun τ
      - (48 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ) + 2636)
          * Work.Kernels.qParamFun τ ^ 2) := by
    refine IsSmS_congr_on hsum2 (fun τ hτ => ?_)
    have hd := psi2_decomp ℓ τ
    simp only [cuspLin] at hd
    simp only [cuspLin]
    rw [hd]
    try ring
  have t1' : IsSmS (fun τ : ℍ => xi4Rem2 τ * cuspLin ℓ τ) :=
    IsSmS_congr_on (IsSmS_lam_mul ℓ hX4) (fun τ _ => by ring)
  have t2' : IsSmS (fun τ : ℍ => 12 * Work.Kernels.qParamFun τ * xi4Rem2 τ) :=
    IsSmS_of_isSm' (k := 8) (by norm_num) ((IsSm.const_mul 12 hq).mul hX4)
  have t3' : IsSmS (fun τ : ℍ => 2 * LplusRem2 ℓ τ) :=
    IsSmS_of_isSm' le_rfl (IsSm.const_mul 2 hY)
  have t4' : IsSmS (fun τ : ℍ => (-288) * Work.Kernels.qParamFun τ * LplusRem2 ℓ τ) :=
    IsSmS_of_isSm' (k := 8) (by norm_num) ((IsSm.const_mul (-288) hq).mul hY)
  have t5' : IsSmS (fun τ : ℍ => xi4Rem2 τ * LplusRem2 ℓ τ) :=
    IsSmS_of_isSm' (k := 12) (by norm_num) (hX4.mul hY)
  have t6' : IsSmS (fun τ : ℍ => 6 * Work.Kernels.qParamFun τ ^ 2 * xi4Rem2 τ) :=
    IsSmS_of_isSm' (k := 10) (by norm_num) ((IsSm.const_mul 6 (hq.pow 2)).mul hX4)
  have t7' : IsSmS (fun τ : ℍ => (-1824) * Work.Kernels.qParamFun τ ^ 2 * LplusRem2 ℓ τ) :=
    IsSmS_of_isSm' (k := 10) (by norm_num) ((IsSm.const_mul (-1824) (hq.pow 2)).mul hY)
  have t8' : IsSmS (fun τ : ℍ => 3 * VLSRem2 ℓ τ) :=
    IsSmS_of_isSm' le_rfl (IsSm.const_mul 3 hZ)
  have t9' : IsSmS (fun τ : ℍ => (-384) * Work.Kernels.qParamFun τ * xi2Rem2 τ) :=
    IsSmS_of_isSm' (k := 8) (by norm_num) ((IsSm.const_mul (-384) hq).mul hX)
  have t10' : IsSmS (fun τ : ℍ => 72 * Work.Kernels.qParamFun τ * VLSRem2 ℓ τ) :=
    IsSmS_of_isSm' (k := 8) (by norm_num) ((IsSm.const_mul 72 hq).mul hZ)
  have t11' : IsSmS (fun τ : ℍ => (3 / 2) * VLSRem2 ℓ τ * xi2Rem2 τ) := by
    refine IsSmS_of_isSm' (k := 12) (by norm_num) ((IsSm.const_mul (3 / 2) hZ).mul hX)
  have t12' : IsSmS (fun τ : ℍ => 72 * Work.Kernels.qParamFun τ ^ 2 * VLSRem2 ℓ τ) :=
    IsSmS_of_isSm' (k := 10) (by norm_num) ((IsSm.const_mul 72 (hq.pow 2)).mul hZ)
  have t13' : IsSmS (fun τ : ℍ => (-2048) * Work.Kernels.qParamFun τ ^ 2 * xi2Rem2 τ) :=
    IsSmS_of_isSm' (k := 10) (by norm_num) ((IsSm.const_mul (-2048) (hq.pow 2)).mul hX)
  have t14' : IsSmS (fun τ : ℍ => (-109248) * Work.Kernels.qParamFun τ ^ 4) :=
    IsSmS_of_isSm' (k := 8) (by norm_num) (IsSm.const_mul (-109248) (hq.pow 4))
  have t15' : IsSmS (fun τ : ℍ => (-140352) * Work.Kernels.qParamFun τ ^ 3) :=
    IsSmS_of_isSm' le_rfl (IsSm.const_mul (-140352) (hq.pow 3))
  have hsum4 : IsSmS (fun τ : ℍ =>
      xi4Rem2 τ * cuspLin ℓ τ
        + 12 * Work.Kernels.qParamFun τ * xi4Rem2 τ
        + 2 * LplusRem2 ℓ τ
        + (-288) * Work.Kernels.qParamFun τ * LplusRem2 ℓ τ
        + xi4Rem2 τ * LplusRem2 ℓ τ
        + 6 * Work.Kernels.qParamFun τ ^ 2 * xi4Rem2 τ
        + (-1824) * Work.Kernels.qParamFun τ ^ 2 * LplusRem2 ℓ τ
        + 3 * VLSRem2 ℓ τ
        + (-384) * Work.Kernels.qParamFun τ * xi2Rem2 τ
        + 72 * Work.Kernels.qParamFun τ * VLSRem2 ℓ τ
        + (3 / 2) * VLSRem2 ℓ τ * xi2Rem2 τ
        + 72 * Work.Kernels.qParamFun τ ^ 2 * VLSRem2 ℓ τ
        + (-2048) * Work.Kernels.qParamFun τ ^ 2 * xi2Rem2 τ
        + (-109248) * Work.Kernels.qParamFun τ ^ 4
        + (-140352) * Work.Kernels.qParamFun τ ^ 3) :=
    IsSmS_add (IsSmS_add (IsSmS_add (IsSmS_add (IsSmS_add (IsSmS_add (IsSmS_add (IsSmS_add (IsSmS_add (IsSmS_add (IsSmS_add (IsSmS_add (IsSmS_add (IsSmS_add (t1') (t2')) (t3')) (t4')) (t5')) (t6')) (t7')) (t8')) (t9')) (t10')) (t11')) (t12')) (t13')) (t14')) (t15')
  have hP4 : IsSmS (fun τ : ℍ => Work.Kernels.psi4 ℓ τ
      - 2 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ)
      + (288 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ) + 744)
          * Work.Kernels.qParamFun τ
      + (1824 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ) + 25972)
          * Work.Kernels.qParamFun τ ^ 2) := by
    refine IsSmS_congr_on hsum4 (fun τ hτ => ?_)
    have hd := psi4_decomp ℓ τ
    simp only [cuspLin] at hd
    simp only [cuspLin]
    rw [hd]
    try ring
  obtain ⟨C2, hC2, h2⟩ := hP2
  obtain ⟨C4, hC4, h4⟩ := hP4
  refine ⟨max C2 C4 + 1, 1, by positivity, by norm_num, fun τ hτ => ?_⟩
  have hs1 : (Work.Kernels.scale τ) ^ (1 : ℝ) = Work.Kernels.scale τ := Real.rpow_one _
  have hq3 : ‖Work.Kernels.qParamFun τ‖ ^ 3 = ‖Work.Residues.Ept τ‖ ^ 6 := by
    rw [Work.Asymptotics.Small.qParamFun_eq_Ept_sq τ, norm_pow]
    ring
  have h0 : (0 : ℝ) ≤ Work.Kernels.scale τ * ‖Work.Residues.Ept τ‖ ^ 6 :=
    mul_nonneg (le_of_lt (Work.Kernels.scale_pos τ)) (by positivity)
  have hle2 : C2 ≤ max C2 C4 + 1 := by linarith [le_max_left C2 C4]
  have hle4 : C4 ≤ max C2 C4 + 1 := by linarith [le_max_right C2 C4]
  constructor
  · rw [hs1, hq3]
    have h := h2 τ hτ
    calc ‖Work.Kernels.psi2 ℓ τ
          - 2 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ)
          - (48 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ) + 408)
              * Work.Kernels.qParamFun τ
          - (48 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ) + 2636)
              * Work.Kernels.qParamFun τ ^ 2‖
        ≤ C2 * Work.Kernels.scale τ * ‖Work.Residues.Ept τ‖ ^ 6 := h
      _ = C2 * (Work.Kernels.scale τ * ‖Work.Residues.Ept τ‖ ^ 6) := by ring
      _ ≤ (max C2 C4 + 1) * (Work.Kernels.scale τ * ‖Work.Residues.Ept τ‖ ^ 6) :=
          mul_le_mul_of_nonneg_right hle2 h0
      _ = (max C2 C4 + 1) * Work.Kernels.scale τ * ‖Work.Residues.Ept τ‖ ^ 6 := by ring
  · rw [hs1, hq3]
    have h := h4 τ hτ
    calc ‖Work.Kernels.psi4 ℓ τ
          - 2 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ)
          + (288 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ) + 744)
              * Work.Kernels.qParamFun τ
          + (1824 * ((Real.pi : ℂ) * Complex.I * (τ : ℂ) + Work.Asymptotics.Compact.cuspC ℓ) + 25972)
              * Work.Kernels.qParamFun τ ^ 2‖
        ≤ C4 * Work.Kernels.scale τ * ‖Work.Residues.Ept τ‖ ^ 6 := h
      _ = C4 * (Work.Kernels.scale τ * ‖Work.Residues.Ept τ‖ ^ 6) := by ring
      _ ≤ (max C2 C4 + 1) * (Work.Kernels.scale τ * ‖Work.Residues.Ept τ‖ ^ 6) :=
          mul_le_mul_of_nonneg_right hle4 h0
      _ = (max C2 C4 + 1) * Work.Kernels.scale τ * ‖Work.Residues.Ept τ‖ ^ 6 := by ring

end

end Work.Asymptotics.KhatE1Core
