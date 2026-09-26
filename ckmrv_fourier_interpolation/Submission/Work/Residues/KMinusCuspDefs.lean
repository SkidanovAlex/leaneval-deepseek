/-
# Cusp data and `CuspBound` calculus for the `K_-` estimate

This file collects the bookkeeping used by the proof of
`Work.Residues.KMinus_isBigO_atImInfty`.

* `Epar τ = e^{πiτ}` is the holomorphic cusp parameter and `tpar τ = e^{-π Im τ} = ‖Epar τ‖`
  is its size.
* `acusp τ = UFun τ - 1` and `bcusp τ = VFun τ` are the two elementary vanishing
  coordinates at the cusp `i∞` (both are `O(tpar)` there).
* `CuspBound f m k` is the assertion `‖f τ‖ ≤ C (1+‖τ‖)^m tpar τ^k` for `Im τ ≥ H`.
* For the polynomial identities we also record the explicit quotient polynomials
  `S_P1`, `S_P2`, `S_X`, `S_Q1`, `S_Q2`, `S_Y`, `S_Nt`, `S_Ntb` exhibiting the
  vanishing orders at the cusp.
-/
import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.Classical
import Submission.Work.Residues.ThetaDecay
import Submission.Work.Kernels.LogLambda.ThetaLower.theta_lower_bound
import Submission.Work.Residues.LogLambdaBound
import Submission.Work.Residues.XiSlashS
import Submission.Work.Residues.ThetaExpansion
import Submission.Work.Residues.KMinusClear_T
import Submission.Work.Kernels.TildeFacts.theta_quartic

namespace Work.Residues

open UpperHalfPlane ModularGroup Matrix
open scoped MatrixGroups Manifold ModularForm

open Work.Kernels

noncomputable section

set_option maxHeartbeats 2000000

/-! ## The cusp parameter -/

/-- The holomorphic cusp parameter `e^{πi τ}`. -/
def Epar (τ : ℍ) : ℂ := Complex.exp (Real.pi * Complex.I * (τ : ℂ))

/-- The real size parameter `tpar τ = e^{-π Im τ} = ‖Epar τ‖`. -/
def tpar (τ : ℍ) : ℝ := Real.exp (-(Real.pi * τ.im))

lemma norm_Epar (τ : ℍ) : ‖Epar τ‖ = tpar τ := by
  simp only [Epar, tpar, Complex.norm_exp]
  congr 1
  rw [show (Real.pi : ℂ) * Complex.I * (τ : ℂ) = ((Real.pi : ℝ) : ℂ) * (Complex.I * (τ : ℂ)) by
    ring, Complex.re_ofReal_mul, Complex.I_mul_re, UpperHalfPlane.coe_im]
  ring

lemma tpar_pos (τ : ℍ) : 0 < tpar τ := Real.exp_pos _

lemma tpar_nonneg (τ : ℍ) : 0 ≤ tpar τ := (tpar_pos τ).le

lemma tpar_le_one (τ : ℍ) : tpar τ ≤ 1 := by
  rw [tpar, Real.exp_le_one_iff]
  have := τ.im_pos
  nlinarith [Real.pi_pos]

/-- `tpar τ ^ n = e^{-n π Im τ}`. -/
lemma tpar_pow (τ : ℍ) (n : ℕ) : tpar τ ^ n = Real.exp (-((n : ℝ) * Real.pi * τ.im)) := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, ih, tpar, ← Real.exp_add]
      congr 1
      push_cast
      ring

lemma tpar_pow_two (τ : ℍ) : tpar τ ^ 2 = Real.exp (-(2 * Real.pi * τ.im)) := tpar_pow τ 2
lemma tpar_pow_three (τ : ℍ) : tpar τ ^ 3 = Real.exp (-(3 * Real.pi * τ.im)) := tpar_pow τ 3
lemma tpar_pow_four (τ : ℍ) : tpar τ ^ 4 = Real.exp (-(4 * Real.pi * τ.im)) := tpar_pow τ 4

/-- For large `Im τ`, `tpar τ ≤ 1/(C+1)`. -/
lemma tpar_le_inv_add_one {C : ℝ} (hC : 0 ≤ C) {τ : ℍ} (h : (C + 1) / Real.pi + 1 ≤ τ.im) :
    tpar τ ≤ 1 / (C + 1) := by
  have hC1 : 0 < C + 1 := by linarith
  have hpit : C + 1 ≤ Real.pi * τ.im := by
    have h2 : Real.pi * ((C + 1) / Real.pi + 1) = (C + 1) + Real.pi := by
      field_simp
    have h3 : Real.pi * ((C + 1) / Real.pi + 1) ≤ Real.pi * τ.im :=
      mul_le_mul_of_nonneg_left h Real.pi_pos.le
    rw [h2] at h3
    linarith [Real.pi_pos]
  have hexp : C + 1 ≤ Real.exp (Real.pi * τ.im) := by
    have := Real.add_one_le_exp (Real.pi * τ.im)
    linarith
  have h4 : 1 / Real.exp (Real.pi * τ.im) ≤ 1 / (C + 1) :=
    one_div_le_one_div_of_le hC1 hexp
  rw [one_div, one_div] at h4
  rw [tpar, Real.exp_neg, one_div]
  exact h4

/-- If `‖z - 1‖ ≤ 1/2` then `‖z‖ ≥ 1/2`. -/
lemma half_le_norm_of_norm_sub_one_le {z : ℂ} (h : ‖z - 1‖ ≤ 1 / 2) : (1 / 2 : ℝ) ≤ ‖z‖ := by
  have habs := abs_norm_sub_norm_le (1 : ℂ) (1 - z)
  have h1 : (1 : ℝ) - ‖1 - z‖ ≤ ‖(1 : ℂ) - (1 - z)‖ := by
    have := (abs_le.mp habs).2
    rw [norm_one] at this
    linarith
  have h5 : ((1 : ℂ) - (1 - z)) = z := by ring
  rw [h5] at h1
  have h6 : ‖1 - z‖ = ‖z - 1‖ := by
    rw [show (1 : ℂ) - z = -(z - 1) by ring, norm_neg]
  rw [h6] at h1
  linarith

/-! ## The cusp coordinates `U - 1`, `V` -/

/-- The cusp coordinate `U - 1`. -/
def acusp (τ : ℍ) : ℂ := UFun τ - 1

/-- The cusp coordinate `V`. -/
def bcusp (τ : ℍ) : ℂ := VFun τ

/-- `acusp = U - 1 = O(tpar)`. -/
lemma acusp_bound : ∃ H C : ℝ, 0 < C ∧ ∀ τ : ℍ, H ≤ τ.im → ‖acusp τ‖ ≤ C * tpar τ := by
  obtain ⟨C, hC, h⟩ := ThetaDecay.1
  exact ⟨1, C, hC, fun τ hτ => by simpa [acusp, tpar] using h τ hτ⟩

/-- `bcusp = V = O(tpar)`. -/
lemma bcusp_bound : ∃ H C : ℝ, 0 < C ∧ ∀ τ : ℍ, H ≤ τ.im → ‖bcusp τ‖ ≤ C * tpar τ := by
  obtain ⟨C, hC, h⟩ := ThetaDecay.2.2.1
  exact ⟨1, C, hC, fun τ hτ => by simpa [bcusp, tpar] using h τ hτ⟩

/-! ## Bounding a continuous function of `(acusp, bcusp)` -/

/-- A continuous function of two variables is bounded on the unit ball of `ℂ × ℂ`. -/
lemma exists_norm_poly2_le (S : ℂ → ℂ → ℂ)
    (hS : Continuous fun p : ℂ × ℂ => S p.1 p.2) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ a b : ℂ, ‖a‖ ≤ 1 → ‖b‖ ≤ 1 → ‖S a b‖ ≤ D := by
  have hcomp : IsCompact (Metric.closedBall (0 : ℂ × ℂ) 1) := isCompact_closedBall _ _
  obtain ⟨D, hD⟩ := hcomp.exists_bound_of_continuousOn hS.continuousOn
  refine ⟨max D 0, le_max_right _ _, fun a b ha hb => ?_⟩
  have hmem : (a, b) ∈ Metric.closedBall (0 : ℂ × ℂ) 1 := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    simp only [sub_zero, Prod.norm_def]
    exact max_le ha hb
  exact le_trans (hD (a, b) hmem) (le_max_left _ _)

/-- Near the cusp, any continuous function of `(acusp, bcusp)` is bounded. -/
lemma poly2_cusp_bound (S : ℂ → ℂ → ℂ)
    (hS : Continuous fun p : ℂ × ℂ => S p.1 p.2) :
    ∃ H C : ℝ, 0 < C ∧ ∀ τ : ℍ, H ≤ τ.im → ‖S (acusp τ) (bcusp τ)‖ ≤ C := by
  obtain ⟨D, hD0, hD⟩ := exists_norm_poly2_le S hS
  obtain ⟨H1, C1, hC1, h1⟩ := acusp_bound
  obtain ⟨H2, C2, hC2, h2⟩ := bcusp_bound
  set C0 : ℝ := max (max C1 C2) (1/2) with hC0
  have hC0n : 0 ≤ C0 := le_trans (by norm_num) (le_max_right _ _)
  have hC0pos : 0 < C0 := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hl1 : ∀ τ : ℍ, H1 ≤ τ.im → ‖acusp τ‖ ≤ C0 * tpar τ := by
    intro τ hτ
    exact le_trans (h1 τ hτ)
      (mul_le_mul_of_nonneg_right (le_trans (le_max_left _ _) (le_max_left _ _)) (tpar_nonneg τ))
  have hl2 : ∀ τ : ℍ, H2 ≤ τ.im → ‖bcusp τ‖ ≤ C0 * tpar τ := by
    intro τ hτ
    exact le_trans (h2 τ hτ)
      (mul_le_mul_of_nonneg_right (le_trans (le_max_right _ _) (le_max_left _ _)) (tpar_nonneg τ))
  refine ⟨max (max H1 H2) (max 1 ((C0 + 1) / Real.pi + 1)), D + 1, by linarith, fun τ hτ => ?_⟩
  have hτH1 : H1 ≤ τ.im := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hτ
  have hτH2 : H2 ≤ τ.im := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hτ
  have hτbig : (C0 + 1) / Real.pi + 1 ≤ τ.im :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hτ
  have ht : C0 * tpar τ ≤ 1 := by
    have h := tpar_le_inv_add_one hC0n hτbig
    have h3 : C0 * (1 / (C0 + 1)) ≤ 1 := by
      rw [mul_one_div, div_le_one (by linarith)]
      linarith
    exact le_trans (mul_le_mul_of_nonneg_left h hC0n) h3
  have ha : ‖acusp τ‖ ≤ 1 := le_trans (hl1 τ hτH1) ht
  have hb : ‖bcusp τ‖ ≤ 1 := le_trans (hl2 τ hτH2) ht
  linarith [hD (acusp τ) (bcusp τ) ha hb]

/-! ## Lower bounds at the cusp -/

/-- `VFun = θ₁₀⁴ ≥ c tpar` near the cusp. -/
lemma VFun_lower : ∃ c : ℝ, 0 < c ∧ ∀ τ : ℍ, 1 / 2 ≤ τ.im → c * tpar τ ≤ ‖VFun τ‖ := by
  refine ⟨(1 / 8 : ℝ) ^ 4, by norm_num, fun τ hτ => ?_⟩
  have h := Work.Kernels.LogLambda.ThetaLower.theta10_region_lower τ hτ
  have h4 : ((1 : ℝ) / 8 * Real.exp (-(Real.pi * τ.im / 4))) ^ 4
      = (1 / 8 : ℝ) ^ 4 * tpar τ := by
    rw [mul_pow, ← Real.exp_nat_mul, tpar]
    congr 2
    push_cast
    ring
  rw [VFun, norm_pow, ← h4]
  exact pow_le_pow_left₀ (by positivity) h 4

/-- `‖UFun‖ ≥ 1/2` and `‖WFun‖ ≥ 1/2` near the cusp. -/
lemma UFun_WFun_lower : ∃ H : ℝ, ∀ τ : ℍ, H ≤ τ.im →
    (1 / 2 : ℝ) ≤ ‖UFun τ‖ ∧ (1 / 2 : ℝ) ≤ ‖WFun τ‖ := by
  obtain ⟨C1, hC1, h1⟩ := ThetaDecay.1
  obtain ⟨C2, hC2, h2⟩ := ThetaDecay.2.1
  set M : ℝ := max C1 C2 with hM
  have hMpos : 0 < M := lt_of_lt_of_le hC1 (le_max_left _ _)
  refine ⟨max 1 ((2 * M + 1) / Real.pi + 1), fun τ hτ => ?_⟩
  have hτ1 : 1 ≤ τ.im := le_trans (le_max_left _ _) hτ
  have hτbig : (2 * M + 1) / Real.pi + 1 ≤ τ.im := le_trans (le_max_right _ _) hτ
  have ht : tpar τ ≤ 1 / (2 * M + 1) := tpar_le_inv_add_one (by linarith) hτbig
  have hMt : M * tpar τ ≤ 1 / 2 := by
    have h3 : M * (1 / (2 * M + 1)) ≤ 1 / 2 := by
      rw [mul_one_div, div_le_iff₀ (by linarith)]
      linarith
    exact le_trans (mul_le_mul_of_nonneg_left ht hMpos.le) h3
  have hU : ‖UFun τ - 1‖ ≤ 1 / 2 :=
    le_trans (h1 τ hτ1)
      (le_trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (tpar_nonneg τ)) hMt)
  have hW : ‖WFun τ - 1‖ ≤ 1 / 2 :=
    le_trans (h2 τ hτ1)
      (le_trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (tpar_nonneg τ)) hMt)
  exact ⟨half_le_norm_of_norm_sub_one_le hU, half_le_norm_of_norm_sub_one_le hW⟩

/-- `Δ = U²V²W²/256 ≥ c tpar²` near the cusp. -/
lemma DeltaFun_lower : ∃ H c : ℝ, 0 < c ∧ ∀ τ : ℍ, H ≤ τ.im → c * tpar τ ^ 2 ≤ ‖DeltaFun τ‖ := by
  obtain ⟨cV, hcV, hV⟩ := VFun_lower
  obtain ⟨H, hUW⟩ := UFun_WFun_lower
  refine ⟨max (1 / 2) H, cV ^ 2 / 4096, by positivity, fun τ hτ => ?_⟩
  have hτV : 1 / 2 ≤ τ.im := le_trans (le_max_left _ _) hτ
  have hτH : H ≤ τ.im := le_trans (le_max_right _ _) hτ
  have hVτ := hV τ hτV
  have hUWτ := hUW τ hτH
  have hnorm : ‖DeltaFun τ‖ = ‖UFun τ‖ ^ 2 * ‖VFun τ‖ ^ 2 * ‖WFun τ‖ ^ 2 / 256 := by
    rw [KMinusT_DeltaFun_eq_theta τ]
    simp only [norm_div, norm_mul, norm_pow, Complex.norm_ofNat]
  rw [hnorm, le_div_iff₀ (by norm_num : (0 : ℝ) < 256)]
  have e1 : ((1 : ℝ) / 2) ^ 2 ≤ ‖UFun τ‖ ^ 2 := by
    nlinarith [hUWτ.1, norm_nonneg (UFun τ)]
  have e3 : ((1 : ℝ) / 2) ^ 2 ≤ ‖WFun τ‖ ^ 2 := by
    nlinarith [hUWτ.2, norm_nonneg (WFun τ)]
  have e2 : (cV * tpar τ) ^ 2 ≤ ‖VFun τ‖ ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hcV.le (tpar_nonneg τ)) hVτ 2
  have hcoef : cV ^ 2 / 4096 * tpar τ ^ 2 * 256
      = ((1 : ℝ) / 2) ^ 2 * (cV * tpar τ) ^ 2 * ((1 : ℝ) / 2) ^ 2 := by ring
  rw [hcoef]
  have hUV : ((1 : ℝ) / 2) ^ 2 * (cV * tpar τ) ^ 2 ≤ ‖UFun τ‖ ^ 2 * ‖VFun τ‖ ^ 2 :=
    mul_le_mul e1 e2 (by positivity) (by positivity)
  exact mul_le_mul hUV e3 (by positivity) (by positivity)

/-! ## The `CuspBound` calculus -/

/-- `CuspBound f m k` means `‖f τ‖ ≤ C (1+‖τ‖)^m tpar τ^k` for all large `Im τ`, with a
constant `C > 0`. -/
def CuspBound (f : ℍ → ℂ) (m : ℕ) (k : ℕ) : Prop :=
  ∃ H C : ℝ, 0 < C ∧ ∀ τ : ℍ, H ≤ τ.im → ‖f τ‖ ≤ C * (1 + ‖(τ : ℂ)‖) ^ m * tpar τ ^ k

lemma one_le_one_add_norm (τ : ℍ) : (1 : ℝ) ≤ 1 + ‖(τ : ℂ)‖ := by
  have := norm_nonneg (τ : ℂ)
  linarith

lemma zero_le_one_add_norm (τ : ℍ) : (0 : ℝ) ≤ 1 + ‖(τ : ℂ)‖ := by
  have := norm_nonneg (τ : ℂ)
  linarith

lemma monomial_nonneg (τ : ℍ) (m k : ℕ) :
    (0 : ℝ) ≤ (1 + ‖(τ : ℂ)‖) ^ m * tpar τ ^ k :=
  mul_nonneg (pow_nonneg (zero_le_one_add_norm τ) m) (pow_nonneg (tpar_nonneg τ) k)

lemma CuspBound.mono {f : ℍ → ℂ} {m k m' k' : ℕ} (h : CuspBound f m k) (hm : m ≤ m') (hk : k' ≤ k) :
    CuspBound f m' k' := by
  obtain ⟨H, C, hC, hb⟩ := h
  refine ⟨max H 1, C + 1, by linarith, fun τ hτ => ?_⟩
  have hτH : H ≤ τ.im := le_trans (le_max_left _ _) hτ
  have ht : tpar τ ≤ 1 := tpar_le_one τ
  have ht0 : 0 < tpar τ := tpar_pos τ
  have hA : (1 + ‖(τ : ℂ)‖) ^ m ≤ (1 + ‖(τ : ℂ)‖) ^ m' :=
    pow_le_pow_right₀ (one_le_one_add_norm τ) hm
  have hB : tpar τ ^ k ≤ tpar τ ^ k' := pow_le_pow_of_le_one ht0.le ht hk
  have h1 : (1 + ‖(τ : ℂ)‖) ^ m * tpar τ ^ k ≤ (1 + ‖(τ : ℂ)‖) ^ m' * tpar τ ^ k' :=
    mul_le_mul hA hB (pow_nonneg ht0.le k) (pow_nonneg (zero_le_one_add_norm τ) m')
  calc ‖f τ‖ ≤ C * (1 + ‖(τ : ℂ)‖) ^ m * tpar τ ^ k := hb τ hτH
    _ = C * ((1 + ‖(τ : ℂ)‖) ^ m * tpar τ ^ k) := by ring
    _ ≤ C * ((1 + ‖(τ : ℂ)‖) ^ m' * tpar τ ^ k') := mul_le_mul_of_nonneg_left h1 hC.le
    _ ≤ (C + 1) * ((1 + ‖(τ : ℂ)‖) ^ m' * tpar τ ^ k') := by nlinarith [monomial_nonneg τ m' k']
    _ = (C + 1) * (1 + ‖(τ : ℂ)‖) ^ m' * tpar τ ^ k' := by ring

/-- Bounded functions are `CuspBound` for any exponents. -/
lemma CuspBound.of_bdd {f : ℍ → ℂ} {C : ℝ} (hC : 0 < C)
    (h : ∀ τ : ℍ, ‖f τ‖ ≤ C) (m : ℕ) : CuspBound f m 0 := by
  refine ⟨1, C + 1, by linarith, fun τ _ => ?_⟩
  have hA : (1 : ℝ) ≤ (1 + ‖(τ : ℂ)‖) ^ m := one_le_pow₀ (one_le_one_add_norm τ)
  calc ‖f τ‖ ≤ C := h τ
    _ ≤ (C + 1) * (1 + ‖(τ : ℂ)‖) ^ m := by nlinarith
    _ = (C + 1) * (1 + ‖(τ : ℂ)‖) ^ m * tpar τ ^ 0 := by ring

lemma CuspBound.add {f g : ℍ → ℂ} {m₁ k₁ m₂ k₂ : ℕ}
    (hf : CuspBound f m₁ k₁) (hg : CuspBound g m₂ k₂) :
    CuspBound (fun τ => f τ + g τ) (max m₁ m₂) (min k₁ k₂) := by
  obtain ⟨H1, C1, hC1, h1⟩ := hf
  obtain ⟨H2, C2, hC2, h2⟩ := hg
  refine ⟨max (max H1 H2) 1, C1 + C2, by linarith, fun τ hτ => ?_⟩
  have hτ1 : H1 ≤ τ.im := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hτ
  have hτ2 : H2 ≤ τ.im := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hτ
  have ht0 : 0 < tpar τ := tpar_pos τ
  have ht1 : tpar τ ≤ 1 := tpar_le_one τ
  have hA1 : (1 + ‖(τ : ℂ)‖) ^ m₁ ≤ (1 + ‖(τ : ℂ)‖) ^ max m₁ m₂ :=
    pow_le_pow_right₀ (one_le_one_add_norm τ) (le_max_left _ _)
  have hA2 : (1 + ‖(τ : ℂ)‖) ^ m₂ ≤ (1 + ‖(τ : ℂ)‖) ^ max m₁ m₂ :=
    pow_le_pow_right₀ (one_le_one_add_norm τ) (le_max_right _ _)
  have hB1 : tpar τ ^ k₁ ≤ tpar τ ^ min k₁ k₂ :=
    pow_le_pow_of_le_one ht0.le ht1 (min_le_left _ _)
  have hB2 : tpar τ ^ k₂ ≤ tpar τ ^ min k₁ k₂ :=
    pow_le_pow_of_le_one ht0.le ht1 (min_le_right _ _)
  have e1 : C1 * (1 + ‖(τ : ℂ)‖) ^ m₁ * tpar τ ^ k₁
      ≤ C1 * (1 + ‖(τ : ℂ)‖) ^ max m₁ m₂ * tpar τ ^ min k₁ k₂ := by
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul hA1 hB1 (pow_nonneg ht0.le k₁)
      (pow_nonneg (zero_le_one_add_norm τ) _)) hC1.le
  have e2 : C2 * (1 + ‖(τ : ℂ)‖) ^ m₂ * tpar τ ^ k₂
      ≤ C2 * (1 + ‖(τ : ℂ)‖) ^ max m₁ m₂ * tpar τ ^ min k₁ k₂ := by
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_left (mul_le_mul hA2 hB2 (pow_nonneg ht0.le k₂)
      (pow_nonneg (zero_le_one_add_norm τ) _)) hC2.le
  calc ‖f τ + g τ‖ ≤ ‖f τ‖ + ‖g τ‖ := norm_add_le _ _
    _ ≤ C1 * (1 + ‖(τ : ℂ)‖) ^ m₁ * tpar τ ^ k₁
          + C2 * (1 + ‖(τ : ℂ)‖) ^ m₂ * tpar τ ^ k₂ := add_le_add (h1 τ hτ1) (h2 τ hτ2)
    _ ≤ C1 * (1 + ‖(τ : ℂ)‖) ^ max m₁ m₂ * tpar τ ^ min k₁ k₂
          + C2 * (1 + ‖(τ : ℂ)‖) ^ max m₁ m₂ * tpar τ ^ min k₁ k₂ := add_le_add e1 e2
    _ = (C1 + C2) * (1 + ‖(τ : ℂ)‖) ^ max m₁ m₂ * tpar τ ^ min k₁ k₂ := by ring

lemma CuspBound.mul {f g : ℍ → ℂ} {m₁ k₁ m₂ k₂ : ℕ}
    (hf : CuspBound f m₁ k₁) (hg : CuspBound g m₂ k₂) :
    CuspBound (fun τ => f τ * g τ) (m₁ + m₂) (k₁ + k₂) := by
  obtain ⟨H1, C1, hC1, h1⟩ := hf
  obtain ⟨H2, C2, hC2, h2⟩ := hg
  refine ⟨max H1 H2, C1 * C2, mul_pos hC1 hC2, fun τ hτ => ?_⟩
  have hτ1 : H1 ≤ τ.im := le_trans (le_max_left _ _) hτ
  have hτ2 : H2 ≤ τ.im := le_trans (le_max_right _ _) hτ
  have h1' := h1 τ hτ1
  have h2' := h2 τ hτ2
  rw [show C1 * (1 + ‖(τ : ℂ)‖) ^ m₁ * tpar τ ^ k₁
      = C1 * ((1 + ‖(τ : ℂ)‖) ^ m₁ * tpar τ ^ k₁) by ring] at h1'
  rw [show C2 * (1 + ‖(τ : ℂ)‖) ^ m₂ * tpar τ ^ k₂
      = C2 * ((1 + ‖(τ : ℂ)‖) ^ m₂ * tpar τ ^ k₂) by ring] at h2'
  rw [norm_mul]
  calc ‖f τ‖ * ‖g τ‖
      ≤ (C1 * ((1 + ‖(τ : ℂ)‖) ^ m₁ * tpar τ ^ k₁))
          * (C2 * ((1 + ‖(τ : ℂ)‖) ^ m₂ * tpar τ ^ k₂)) :=
        mul_le_mul h1' h2' (norm_nonneg _) (mul_nonneg hC1.le (monomial_nonneg τ m₁ k₁))
    _ = C1 * C2 * (1 + ‖(τ : ℂ)‖) ^ (m₁ + m₂) * tpar τ ^ (k₁ + k₂) := by
        rw [pow_add, pow_add]; ring

lemma CuspBound.const_mul (c : ℂ) {f : ℍ → ℂ} {m k : ℕ} (hf : CuspBound f m k) :
    CuspBound (fun τ => c * f τ) m k := by
  obtain ⟨H, C, hC, h⟩ := hf
  refine ⟨H, ‖c‖ * C + 1, by positivity, fun τ hτ => ?_⟩
  rw [norm_mul]
  have h1 := h τ hτ
  have h2 : (0 : ℝ) ≤ (1 + ‖(τ : ℂ)‖) ^ m * tpar τ ^ k := monomial_nonneg τ m k
  have h3 : ‖c‖ * (C * (1 + ‖(τ : ℂ)‖) ^ m * tpar τ ^ k)
      = (‖c‖ * C) * ((1 + ‖(τ : ℂ)‖) ^ m * tpar τ ^ k) := by ring
  have h4 : (0 : ℝ) ≤ ‖c‖ * C := by positivity
  calc ‖c‖ * ‖f τ‖ ≤ ‖c‖ * (C * (1 + ‖(τ : ℂ)‖) ^ m * tpar τ ^ k) :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg c)
    _ = (‖c‖ * C) * ((1 + ‖(τ : ℂ)‖) ^ m * tpar τ ^ k) := h3
    _ ≤ (‖c‖ * C + 1) * ((1 + ‖(τ : ℂ)‖) ^ m * tpar τ ^ k) := by nlinarith
    _ = (‖c‖ * C + 1) * (1 + ‖(τ : ℂ)‖) ^ m * tpar τ ^ k := by ring


/-! ## Vanishing orders at the cusp

The eight quantities below are the coefficients that occur in the two decompositions
`KMinus8_eq` and `KMinus24_eq` of `Work.Residues.KMinus_isBigO_atImInfty`.  Each of them
is an explicit polynomial in `(U,V,W)` (with `U = W + V`), and each is divisible by a power
of `V = bcusp`; the corresponding quotient is an explicit polynomial in `(U-1, V)`, recorded
here as `S_P1`, ….  The quotients are bounded near the cusp by `poly2_cusp_bound`.
-/

/-- Quotient of `P₁ = ξ₂E₁₄ - ξ₄E₆²` by `V²`. -/
def S_P1 (a b : ℂ) : ℂ :=
  (9 : ℂ) + (54 : ℂ) * a + (-27 : ℂ) * b + (135 : ℂ) * a^2 + (-135 : ℂ) * a*b + ((45 : ℂ)/4) * b^2 + (180 : ℂ) * a^3 + (-270 : ℂ) * a^2*b + (45 : ℂ) * a*b^2 + ((45 : ℂ)/2) * b^3 + (135 : ℂ) * a^4 + (-270 : ℂ) * a^3*b + ((135 : ℂ)/2) * a^2*b^2 + ((135 : ℂ)/2) * a*b^3 + ((-81 : ℂ)/4) * b^4 + (54 : ℂ) * a^5 + (-135 : ℂ) * a^4*b + (45 : ℂ) * a^3*b^2 + ((135 : ℂ)/2) * a^2*b^3 + ((-81 : ℂ)/2) * a*b^4 + ((9 : ℂ)/2) * b^5 + (9 : ℂ) * a^6 + (-27 : ℂ) * a^5*b + ((45 : ℂ)/4) * a^4*b^2 + ((45 : ℂ)/2) * a^3*b^3 + ((-81 : ℂ)/4) * a^2*b^4 + ((9 : ℂ)/2) * a*b^5


def S_P2 (a b : ℂ) : ℂ :=
  ((9 : ℂ)/2) + (27 : ℂ) * a + ((-27 : ℂ)/2) * b + ((135 : ℂ)/2) * a^2 + ((-135 : ℂ)/2) * a*b + ((45 : ℂ)/2) * b^2 + (90 : ℂ) * a^3 + (-135 : ℂ) * a^2*b + (90 : ℂ) * a*b^2 + ((-45 : ℂ)/2) * b^3 + ((135 : ℂ)/2) * a^4 + (-135 : ℂ) * a^3*b + (135 : ℂ) * a^2*b^2 + ((-135 : ℂ)/2) * a*b^3 + ((27 : ℂ)/2) * b^4 + (27 : ℂ) * a^5 + ((-135 : ℂ)/2) * a^4*b + (90 : ℂ) * a^3*b^2 + ((-135 : ℂ)/2) * a^2*b^3 + (27 : ℂ) * a*b^4 + ((-9 : ℂ)/2) * b^5 + ((9 : ℂ)/2) * a^6 + ((-27 : ℂ)/2) * a^5*b + ((45 : ℂ)/2) * a^4*b^2 + ((-45 : ℂ)/2) * a^3*b^3 + ((27 : ℂ)/2) * a^2*b^4 + ((-9 : ℂ)/2) * a*b^5


def S_X (a b : ℂ) : ℂ :=
  ((9 : ℂ)/2) + (18 : ℂ) * a + (-9 : ℂ) * b + (27 : ℂ) * a^2 + (-27 : ℂ) * a*b + (9 : ℂ) * b^2 + (18 : ℂ) * a^3 + (-27 : ℂ) * a^2*b + (18 : ℂ) * a*b^2 + ((-9 : ℂ)/2) * b^3 + ((9 : ℂ)/2) * a^4 + (-9 : ℂ) * a^3*b + (9 : ℂ) * a^2*b^2 + ((-9 : ℂ)/2) * a*b^3


def S_Nt (a b : ℂ) : ℂ :=
  ((-135 : ℂ)/4) + (-135 : ℂ) * a + ((135 : ℂ)/2) * b + ((-405 : ℂ)/2) * a^2 + ((405 : ℂ)/2) * a*b + ((-189 : ℂ)/4) * b^2 + (-135 : ℂ) * a^3 + ((405 : ℂ)/2) * a^2*b + ((-189 : ℂ)/2) * a*b^2 + ((27 : ℂ)/2) * b^3 + ((-135 : ℂ)/4) * a^4 + ((135 : ℂ)/2) * a^3*b + ((-189 : ℂ)/4) * a^2*b^2 + ((27 : ℂ)/2) * a*b^3


def S_Q1 (a b : ℂ) : ℂ :=
  ((-9 : ℂ)/2) + ((-63 : ℂ)/2) * a + ((45 : ℂ)/4) * b + ((-189 : ℂ)/2) * a^2 + ((135 : ℂ)/2) * a*b + ((9 : ℂ)/2) * b^2 + ((-315 : ℂ)/2) * a^3 + ((675 : ℂ)/4) * a^2*b + ((45 : ℂ)/2) * a*b^2 + ((-45 : ℂ)/2) * b^3 + ((-315 : ℂ)/2) * a^4 + (225 : ℂ) * a^3*b + (45 : ℂ) * a^2*b^2 + (-90 : ℂ) * a*b^3 + ((9 : ℂ)/2) * b^4 + ((-189 : ℂ)/2) * a^5 + ((675 : ℂ)/4) * a^4*b + (45 : ℂ) * a^3*b^2 + (-135 : ℂ) * a^2*b^3 + ((27 : ℂ)/2) * a*b^4 + ((45 : ℂ)/4) * b^5 + ((-63 : ℂ)/2) * a^6 + ((135 : ℂ)/2) * a^5*b + ((45 : ℂ)/2) * a^4*b^2 + (-90 : ℂ) * a^3*b^3 + ((27 : ℂ)/2) * a^2*b^4 + ((45 : ℂ)/2) * a*b^5 + ((-9 : ℂ)/2) * b^6 + ((-9 : ℂ)/2) * a^7 + ((45 : ℂ)/4) * a^6*b + ((9 : ℂ)/2) * a^5*b^2 + ((-45 : ℂ)/2) * a^4*b^3 + ((9 : ℂ)/2) * a^3*b^4 + ((45 : ℂ)/4) * a^2*b^5 + ((-9 : ℂ)/2) * a*b^6


def S_Q2 (a b : ℂ) : ℂ :=
  ((9 : ℂ)/2) + ((63 : ℂ)/2) * a + (-18 : ℂ) * b + ((189 : ℂ)/2) * a^2 + (-108 : ℂ) * a*b + (36 : ℂ) * b^2 + ((315 : ℂ)/2) * a^3 + (-270 : ℂ) * a^2*b + (180 : ℂ) * a*b^2 + (-45 : ℂ) * b^3 + ((315 : ℂ)/2) * a^4 + (-360 : ℂ) * a^3*b + (360 : ℂ) * a^2*b^2 + (-180 : ℂ) * a*b^3 + (36 : ℂ) * b^4 + ((189 : ℂ)/2) * a^5 + (-270 : ℂ) * a^4*b + (360 : ℂ) * a^3*b^2 + (-270 : ℂ) * a^2*b^3 + (108 : ℂ) * a*b^4 + (-18 : ℂ) * b^5 + ((63 : ℂ)/2) * a^6 + (-108 : ℂ) * a^5*b + (180 : ℂ) * a^4*b^2 + (-180 : ℂ) * a^3*b^3 + (108 : ℂ) * a^2*b^4 + (-36 : ℂ) * a*b^5 + ((9 : ℂ)/2) * b^6 + ((9 : ℂ)/2) * a^7 + (-18 : ℂ) * a^6*b + (36 : ℂ) * a^5*b^2 + (-45 : ℂ) * a^4*b^3 + (36 : ℂ) * a^3*b^4 + (-18 : ℂ) * a^2*b^5 + ((9 : ℂ)/2) * a*b^6


def S_Y (a b : ℂ) : ℂ :=
  ((9 : ℂ)/2) + ((45 : ℂ)/2) * a + ((-27 : ℂ)/2) * b + (45 : ℂ) * a^2 + (-54 : ℂ) * a*b + (18 : ℂ) * b^2 + (45 : ℂ) * a^3 + (-81 : ℂ) * a^2*b + (54 : ℂ) * a*b^2 + ((-27 : ℂ)/2) * b^3 + ((45 : ℂ)/2) * a^4 + (-54 : ℂ) * a^3*b + (54 : ℂ) * a^2*b^2 + (-27 : ℂ) * a*b^3 + ((9 : ℂ)/2) * b^4 + ((9 : ℂ)/2) * a^5 + ((-27 : ℂ)/2) * a^4*b + (18 : ℂ) * a^3*b^2 + ((-27 : ℂ)/2) * a^2*b^3 + ((9 : ℂ)/2) * a*b^4


def S_Ntb (a b : ℂ) : ℂ :=
  ((-27 : ℂ)/2) + ((-189 : ℂ)/2) * a + ((189 : ℂ)/4) * b + ((-567 : ℂ)/2) * a^2 + ((567 : ℂ)/2) * a*b + ((-135 : ℂ)/2) * b^2 + ((-945 : ℂ)/2) * a^3 + ((2835 : ℂ)/4) * a^2*b + ((-675 : ℂ)/2) * a*b^2 + ((135 : ℂ)/2) * b^3 + ((-945 : ℂ)/2) * a^4 + (945 : ℂ) * a^3*b + (-675 : ℂ) * a^2*b^2 + (270 : ℂ) * a*b^3 + ((-135 : ℂ)/2) * b^4 + ((-567 : ℂ)/2) * a^5 + ((2835 : ℂ)/4) * a^4*b + (-675 : ℂ) * a^3*b^2 + (405 : ℂ) * a^2*b^3 + ((-405 : ℂ)/2) * a*b^4 + ((189 : ℂ)/4) * b^5 + ((-189 : ℂ)/2) * a^6 + ((567 : ℂ)/2) * a^5*b + ((-675 : ℂ)/2) * a^4*b^2 + (270 : ℂ) * a^3*b^3 + ((-405 : ℂ)/2) * a^2*b^4 + ((189 : ℂ)/2) * a*b^5 + ((-27 : ℂ)/2) * b^6 + ((-27 : ℂ)/2) * a^7 + ((189 : ℂ)/4) * a^6*b + ((-135 : ℂ)/2) * a^5*b^2 + ((135 : ℂ)/2) * a^4*b^3 + ((-135 : ℂ)/2) * a^3*b^4 + ((189 : ℂ)/4) * a^2*b^5 + ((-27 : ℂ)/2) * a*b^6



/-- `P₁ = ξ₂E₁₄ - ξ₄E₆²`. -/
def P1fun (τ : ℍ) : ℂ := xi2Fun τ * E14Fun τ - xi4Fun τ * E6Fun τ ^ 2

/-- `P₂ = ξ₄E₄³ - ξ₂E₁₄`. -/
def P2fun (τ : ℍ) : ℂ := xi4Fun τ * E4Fun τ ^ 3 - xi2Fun τ * E14Fun τ

/-- `X = ξ₄E₈ - ξ₂E₁₀`. -/
def Xfun (τ : ℍ) : ℂ := xi4Fun τ * E8Fun τ - xi2Fun τ * E10Fun τ

/-- `Ñ = 3ξ₂E₄²E₆ - 2ξ₄E₄³ - ξ₄E₆²`. -/
def Ntfun (τ : ℍ) : ℂ :=
  -2 * xi4Fun τ * E4Fun τ ^ 3 + 3 * xi2Fun τ * E4Fun τ ^ 2 * E6Fun τ - xi4Fun τ * E6Fun τ ^ 2

lemma xi2Fun_slash_S_apply (τ : ℍ) :
    (xi2Fun ∣[(2 : ℤ)] ModularGroup.S) τ = -(UFun τ + VFun τ) := congr_fun XiSlashS.1 τ

lemma xi4Fun_slash_S_apply (τ : ℍ) :
    (xi4Fun ∣[(4 : ℤ)] ModularGroup.S) τ
      = UFun τ ^ 2 + VFun τ ^ 2 - 2 * WFun τ ^ 2 := congr_fun XiSlashS.2 τ

/-- `Q₁ = (ξ₂|₂S)E₁₄ - (ξ₄|₄S)E₆²`. -/
def Q1fun (τ : ℍ) : ℂ :=
  (xi2Fun ∣[(2 : ℤ)] ModularGroup.S) τ * E14Fun τ
    - (xi4Fun ∣[(4 : ℤ)] ModularGroup.S) τ * E6Fun τ ^ 2

/-- `Q₂ = (ξ₄|₄S)E₄³ - (ξ₂|₂S)E₁₄`. -/
def Q2fun (τ : ℍ) : ℂ :=
  (xi4Fun ∣[(4 : ℤ)] ModularGroup.S) τ * E4Fun τ ^ 3
    - (xi2Fun ∣[(2 : ℤ)] ModularGroup.S) τ * E14Fun τ

/-- `Y = (ξ₄|₄S)E₈ - (ξ₂|₂S)E₁₀`. -/
def Yfun (τ : ℍ) : ℂ :=
  (xi4Fun ∣[(4 : ℤ)] ModularGroup.S) τ * E8Fun τ
    - (xi2Fun ∣[(2 : ℤ)] ModularGroup.S) τ * E10Fun τ

/-- `Ñ = 3(ξ₂|₂S)E₄²E₆ - 2(ξ₄|₄S)E₄³ - (ξ₄|₄S)E₆²`. -/
def Ntbfun (τ : ℍ) : ℂ :=
  -2 * (xi4Fun ∣[(4 : ℤ)] ModularGroup.S) τ * E4Fun τ ^ 3
    + 3 * (xi2Fun ∣[(2 : ℤ)] ModularGroup.S) τ * E4Fun τ ^ 2 * E6Fun τ
    - (xi4Fun ∣[(4 : ℤ)] ModularGroup.S) τ * E6Fun τ ^ 2

/-- The ring identities: each named quantity is the stated power of `bcusp = V` times the
corresponding quotient polynomial evaluated at `(acusp, bcusp) = (U-1, V)`. -/
lemma P1fun_eq (τ : ℍ) : P1fun τ = bcusp τ ^ 2 * S_P1 (acusp τ) (bcusp τ) := by
  simp only [P1fun, S_P1, acusp, bcusp, xi2Fun, xi4Fun, E14Fun,
    KMinusT_E4Fun_eq_theta, KMinusT_E6Fun_eq_theta, Work.Kernels.TildeFacts.theta_quartic]
  ring

lemma P2fun_eq (τ : ℍ) : P2fun τ = bcusp τ ^ 2 * S_P2 (acusp τ) (bcusp τ) := by
  simp only [P2fun, S_P2, acusp, bcusp, xi2Fun, xi4Fun, E14Fun,
    KMinusT_E4Fun_eq_theta, KMinusT_E6Fun_eq_theta, Work.Kernels.TildeFacts.theta_quartic]
  ring

lemma Xfun_eq (τ : ℍ) : Xfun τ = bcusp τ ^ 2 * S_X (acusp τ) (bcusp τ) := by
  simp only [Xfun, S_X, acusp, bcusp, xi2Fun, xi4Fun, E8Fun, E10Fun,
    KMinusT_E4Fun_eq_theta, KMinusT_E6Fun_eq_theta, Work.Kernels.TildeFacts.theta_quartic]
  ring

lemma Ntfun_eq (τ : ℍ) : Ntfun τ = bcusp τ ^ 4 * S_Nt (acusp τ) (bcusp τ) := by
  simp only [Ntfun, S_Nt, acusp, bcusp, xi2Fun, xi4Fun, E8Fun, E10Fun,
    KMinusT_E4Fun_eq_theta, KMinusT_E6Fun_eq_theta, Work.Kernels.TildeFacts.theta_quartic]
  ring

lemma Q1fun_eq (τ : ℍ) : Q1fun τ = bcusp τ * S_Q1 (acusp τ) (bcusp τ) := by
  simp only [Q1fun, S_Q1, acusp, bcusp, xi2Fun_slash_S_apply, xi4Fun_slash_S_apply,
    xi2Fun, xi4Fun, E14Fun,
    KMinusT_E4Fun_eq_theta, KMinusT_E6Fun_eq_theta, Work.Kernels.TildeFacts.theta_quartic]
  ring

lemma Q2fun_eq (τ : ℍ) : Q2fun τ = bcusp τ * S_Q2 (acusp τ) (bcusp τ) := by
  simp only [Q2fun, S_Q2, acusp, bcusp, xi2Fun_slash_S_apply, xi4Fun_slash_S_apply,
    xi2Fun, xi4Fun, E14Fun,
    KMinusT_E4Fun_eq_theta, KMinusT_E6Fun_eq_theta, Work.Kernels.TildeFacts.theta_quartic]
  ring

lemma Yfun_eq (τ : ℍ) : Yfun τ = bcusp τ * S_Y (acusp τ) (bcusp τ) := by
  simp only [Yfun, S_Y, acusp, bcusp, xi2Fun_slash_S_apply, xi4Fun_slash_S_apply,
    xi2Fun, xi4Fun, E8Fun, E10Fun,
    KMinusT_E4Fun_eq_theta, KMinusT_E6Fun_eq_theta, Work.Kernels.TildeFacts.theta_quartic]
  ring

lemma Ntbfun_eq (τ : ℍ) : Ntbfun τ = bcusp τ * S_Ntb (acusp τ) (bcusp τ) := by
  simp only [Ntbfun, S_Ntb, acusp, bcusp, xi2Fun_slash_S_apply, xi4Fun_slash_S_apply,
    xi2Fun, xi4Fun, E8Fun, E10Fun,
    KMinusT_E4Fun_eq_theta, KMinusT_E6Fun_eq_theta, Work.Kernels.TildeFacts.theta_quartic]
  ring


/-! ## The cusp expansions in `Epar`/`tpar` vocabulary -/

lemma Epar_eq_Ept (τ : ℍ) : Epar τ = Ept τ := rfl

lemma tpar_eq_norm_Ept (τ : ℍ) : tpar τ = ‖Ept τ‖ := by
  rw [tpar, Ept, Complex.norm_exp]
  congr 1
  rw [show (Real.pi : ℂ) * Complex.I * (τ : ℂ)
      = ((Real.pi : ℝ) : ℂ) * (Complex.I * (τ : ℂ)) by ring]
  rw [Complex.re_ofReal_mul, Complex.I_mul_re, UpperHalfPlane.coe_im]
  ring

/-- `U - 1 = 8E + O(E²)`. -/
theorem acusp_expansion : ∃ H C : ℝ, 0 < C ∧ ∀ τ : ℍ, H ≤ τ.im →
    ‖acusp τ - 8 * Epar τ‖ ≤ C * tpar τ ^ 2 := by
  obtain ⟨C, hC, h⟩ := UFun_expansion
  refine ⟨1, C, hC, fun τ hτ => ?_⟩
  have h' := h τ hτ
  rw [← tpar_eq_norm_Ept τ] at h'
  exact h'

/-- `V = 16E + O(E³)`. -/
theorem bcusp_expansion : ∃ H C : ℝ, 0 < C ∧ ∀ τ : ℍ, H ≤ τ.im →
    ‖bcusp τ - 16 * Epar τ‖ ≤ C * tpar τ ^ 3 := by
  obtain ⟨C, hC, h⟩ := VFun_expansion
  refine ⟨1, C, hC, fun τ hτ => ?_⟩
  have h' := h τ hτ
  rw [← tpar_eq_norm_Ept τ] at h'
  exact h'

/-- `Δ = E² + O(E⁴)`. -/
theorem Deltafun_expansion : ∃ H C : ℝ, 0 < C ∧ ∀ τ : ℍ, H ≤ τ.im →
    ‖DeltaFun τ - Epar τ ^ 2‖ ≤ C * tpar τ ^ 4 := by
  obtain ⟨C, hC, h⟩ := DeltaExpansion
  refine ⟨1, C, hC, fun τ hτ => ?_⟩
  have h' := h τ hτ
  rw [← tpar_eq_norm_Ept τ] at h'
  exact h'

/-- `𝓛_S = -16E + O(E³)`. -/
theorem LS_expansion (ℓ : LogLambdaData) : ∃ H C : ℝ, 0 < C ∧ ∀ τ : ℍ, H ≤ τ.im →
    ‖ℓ.L_S τ + 16 * Epar τ‖ ≤ C * tpar τ ^ 3 := by
  obtain ⟨C, hC, h⟩ := LamSExpansion
  refine ⟨1, C, hC, fun τ hτ => ?_⟩
  rw [LogLambdaData_LS_eq_LamS ℓ τ (by linarith)]
  have h' := h τ (by linarith)
  rw [← tpar_eq_norm_Ept τ] at h'
  exact h'

/-! ## Discriminant and `j`-invariant -/

lemma discr_eq (τ : ℍ) : (1728 : ℂ) * DeltaFun τ = E4Fun τ ^ 3 - E6Fun τ ^ 2 := by
  have h := ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq τ
  rw [show ModularForm.discriminant τ = DeltaFun τ from rfl] at h
  rw [h, show ModularForm.E₄ τ = E4Fun τ from rfl, show ModularForm.E₆ τ = E6Fun τ from rfl]
  rw [mul_comm]
  exact div_mul_cancel₀ _ (by norm_num : (1728 : ℂ) ≠ 0)

lemma c1728_eq (τ : ℍ) : c1728 = (E4Fun τ ^ 3 - E6Fun τ ^ 2) / DeltaFun τ := by
  have hD : DeltaFun τ ≠ 0 := ClassicalFacts.DeltaFun_ne_zero τ
  have h := discr_eq τ
  rw [show c1728 = (1728 : ℂ) from rfl, ← h, mul_div_cancel_right₀ _ hD]

lemma jInvariantFun_mul (τ : ℍ) : DeltaFun τ * jInvariantFun τ = E4Fun τ ^ 3 := by
  have hD : DeltaFun τ ≠ 0 := ClassicalFacts.DeltaFun_ne_zero τ
  rw [jInvariantFun, mul_comm, div_mul_cancel₀ _ hD]

/-! ## The two brackets -/

/-- `Γ = ψ₂E₁₄/Δ + ψ₄(1728 − j) = (ψ₂E₁₄ − ψ₄E₆²)/Δ`. -/
def Gamm (ℓ : LogLambdaData) (τ : ℍ) : ℂ :=
  psi2 ℓ τ * E14Fun τ / DeltaFun τ + psi4 ℓ τ * (c1728 - jInvariantFun τ)

/-- `Λ = ψ₄j − ψ₂E₁₄/Δ = (ψ₄E₄³ − ψ₂E₁₄)/Δ`. -/
def Lamb (ℓ : LogLambdaData) (τ : ℍ) : ℂ :=
  psi4 ℓ τ * jInvariantFun τ - psi2 ℓ τ * E14Fun τ / DeltaFun τ

lemma Gamm_eq (ℓ : LogLambdaData) (τ : ℍ) :
    Gamm ℓ τ = (psi2 ℓ τ * E14Fun τ - psi4 ℓ τ * E6Fun τ ^ 2) / DeltaFun τ := by
  rw [Gamm, c1728_eq τ]
  ring

lemma Lamb_eq (ℓ : LogLambdaData) (τ : ℍ) :
    Lamb ℓ τ = (psi4 ℓ τ * E4Fun τ ^ 3 - psi2 ℓ τ * E14Fun τ) / DeltaFun τ := by
  rw [Lamb]
  ring

/-- The bracket of `KMinus8_eq`, regrouped for the estimate. -/
def bracket8 (ℓ : LogLambdaData) (z τ : ℍ) : ℂ :=
  ((-2 : ℂ) * c1728) * E4Fun τ * E10Fun z * ℓ.L z
    + (E8Fun z * WFun z) * Gamm ℓ τ
    + (E6Fun z * (UFun z ^ 2 - VFun z ^ 2)) * Lamb ℓ τ

/-- The same quantity as it appears in `KMinus8_eq`. -/
def bracket8e (ℓ : LogLambdaData) (z τ : ℍ) : ℂ :=
  ((-2 : ℂ) * c1728) * E4Fun τ * E10Fun z * ℓ.L z
    + psi2 ℓ τ * (E14Fun τ / DeltaFun τ) * (E8Fun z * WFun z
        - E6Fun z * (UFun z ^ 2 - VFun z ^ 2))
    + psi4 ℓ τ * ((c1728 - jInvariantFun τ) * E8Fun z * WFun z
        + jInvariantFun τ * E6Fun z * (UFun z ^ 2 - VFun z ^ 2))

lemma bracket8_eq (ℓ : LogLambdaData) (z τ : ℍ) : bracket8 ℓ z τ = bracket8e ℓ z τ := by
  simp only [bracket8, bracket8e, Gamm, Lamb]
  ring

/-- `B' = -3456Δ(j−jz) + ψ₂E₁₀(j+2(j−jz)) + ψ₄E₈(1728−2(j−jz)−j)`. -/
def BprimeExp (ℓ : LogLambdaData) (z τ : ℍ) : ℂ :=
  -3456 * DeltaFun τ * (jInvariantFun τ - jInvariantFun z)
    + psi2 ℓ τ * E10Fun τ * (jInvariantFun τ + 2 * (jInvariantFun τ - jInvariantFun z))
    + psi4 ℓ τ * E8Fun τ * (c1728 - 2 * (jInvariantFun τ - jInvariantFun z) - jInvariantFun τ)

/-- `B₀` with the `𝓛`-coefficient: `E₄²Ñ/Δ`, where `Ñ = 3ξ₂E₄²E₆ - 2ξ₄E₄³ - ξ₄E₆²`. -/
def B0core (τ : ℍ) : ℂ := E4Fun τ ^ 2 * Ntfun τ / DeltaFun τ

/-- The `𝓛_S`-part: `𝓛_S·E₄²Ñ/Δ - 3456E₄³`. -/
def Ccore (ℓ : LogLambdaData) (τ : ℍ) : ℂ :=
  ℓ.L_S τ * E4Fun τ ^ 2 * Ntbfun τ / DeltaFun τ - 3456 * E4Fun τ ^ 3

/-- `B'`, regrouped in the form used for the estimate. -/
def Bprimefun (ℓ : LogLambdaData) (z τ : ℍ) : ℂ :=
  ℓ.L τ * B0core τ + 2 * jInvariantFun z * (ℓ.L τ * Xfun τ) + Ccore ℓ τ
    + 2 * jInvariantFun z * (ℓ.L_S τ * Yfun τ) + 3456 * DeltaFun τ * jInvariantFun z

lemma h1728_eq (τ : ℍ) : (1728 : ℂ) = (E4Fun τ ^ 3 - E6Fun τ ^ 2) / DeltaFun τ := by
  have hD : DeltaFun τ ≠ 0 := ClassicalFacts.DeltaFun_ne_zero τ
  rw [eq_div_iff hD]
  exact discr_eq τ

lemma B0core_eq (τ : ℍ) :
    B0core τ = 1728 * (xi4Fun τ * E8Fun τ) - 3 * jInvariantFun τ * Xfun τ := by
  have hD : DeltaFun τ ≠ 0 := ClassicalFacts.DeltaFun_ne_zero τ
  have h1728 := h1728_eq τ
  rw [h1728]
  simp only [B0core, Xfun, Ntfun, E8Fun, E10Fun, E14Fun, jInvariantFun]
  field_simp
  ring

lemma Ccore_eq (ℓ : LogLambdaData) (τ : ℍ) :
    Ccore ℓ τ = ℓ.L_S τ * (1728 * ((xi4Fun ∣[(4 : ℤ)] ModularGroup.S) τ * E8Fun τ)
        - 3 * jInvariantFun τ * Yfun τ) - 3456 * E4Fun τ ^ 3 := by
  have hD : DeltaFun τ ≠ 0 := ClassicalFacts.DeltaFun_ne_zero τ
  have h1728 := h1728_eq τ
  rw [h1728]
  simp only [Ccore, Yfun, Ntbfun, E8Fun, E10Fun, E14Fun, jInvariantFun,
    xi2Fun_slash_S_apply, xi4Fun_slash_S_apply]
  field_simp
  ring

lemma Bprimefun_eq (ℓ : LogLambdaData) (z τ : ℍ) : Bprimefun ℓ z τ = BprimeExp ℓ z τ := by
  have hD : DeltaFun τ ≠ 0 := ClassicalFacts.DeltaFun_ne_zero τ
  have h1728 := h1728_eq τ
  simp only [Bprimefun, BprimeExp, B0core, Ccore, Xfun, Yfun, Ntfun, Ntbfun, psi2, psi4,
    E8Fun, E10Fun, E14Fun, jInvariantFun, c1728, xi2Fun_slash_S_apply, xi4Fun_slash_S_apply]
  rw [h1728]
  field_simp
  ring

/-- `ψ₄E₈ - ψ₂E₁₀ = 𝓛·X + 𝓛_S·Y`. -/
lemma psi4E8_sub (ℓ : LogLambdaData) (τ : ℍ) :
    psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ
      = ℓ.L τ * Xfun τ + ℓ.L_S τ * Yfun τ := by
  simp only [psi2, psi4, Xfun, Yfun, E8Fun, E10Fun, xi2Fun, xi4Fun,
    xi2Fun_slash_S_apply, xi4Fun_slash_S_apply]
  ring

/-- The bracket of `KMinus24_eq`, regrouped for the estimate. -/
def bracket24 (ℓ : LogLambdaData) (z τ : ℍ) : ℂ :=
  WFun z * BprimeExp ℓ z τ
    + (E10Fun z / DeltaFun z) * (UFun z ^ 2 - VFun z ^ 2)
        * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ)
    - 3456 * DeltaFun τ * (E14Fun z / DeltaFun z) * ℓ.L z

/-- The same quantity as it appears in `KMinus24_eq`. -/
def bracket24e (ℓ : LogLambdaData) (z τ : ℍ) : ℂ :=
  DeltaFun τ * (((-2 : ℂ) * c1728) * (E14Fun z / DeltaFun z) * ℓ.L z
      + ((-2 : ℂ) * c1728) * (jInvariantFun τ - jInvariantFun z) * WFun z)
    + psi2 ℓ τ * E10Fun τ *
        ((jInvariantFun τ + 2 * (jInvariantFun τ - jInvariantFun z)) * WFun z
          - (E10Fun z / DeltaFun z) * (UFun z ^ 2 - VFun z ^ 2))
    + psi4 ℓ τ * E8Fun τ *
        ((c1728 - 2 * (jInvariantFun τ - jInvariantFun z) - jInvariantFun τ) * WFun z
          + (E10Fun z / DeltaFun z) * (UFun z ^ 2 - VFun z ^ 2))

lemma bracket24_eq (ℓ : LogLambdaData) (z τ : ℍ) : bracket24 ℓ z τ = bracket24e ℓ z τ := by
  simp only [bracket24, bracket24e, BprimeExp, psi2, psi4, c1728]
  ring

/-- The regrouped form used for the estimate: `ψ₄E₈ - ψ₂E₁₀ = 𝓛X + 𝓛_SY`. -/
lemma bracket24_regroup (ℓ : LogLambdaData) (z τ : ℍ) :
    bracket24e ℓ z τ
      = WFun z * Bprimefun ℓ z τ
        + (E10Fun z / DeltaFun z) * (UFun z ^ 2 - VFun z ^ 2)
            * (ℓ.L τ * Xfun τ + ℓ.L_S τ * Yfun τ)
        - 3456 * DeltaFun τ * (E14Fun z / DeltaFun z) * ℓ.L z := by
  rw [Bprimefun_eq ℓ z τ, ← psi4E8_sub ℓ τ]
  simp only [bracket24e, BprimeExp, c1728]
  ring


/-! ## The sharp second-order bound for `Ñ + 216E` -/

def S_Ntb_rem1 (a b : ℂ) : ℂ :=
  (((-567 : ℂ)/2))*a^0*b^0 + (((-945 : ℂ)/2))*a^1*b^0 + (((2835 : ℂ)/4))*a^0*b^1 + (((-945 : ℂ)/2))*a^2*b^0 + ((945 : ℂ))*a^1*b^1 + ((-675 : ℂ))*a^0*b^2 + (((-567 : ℂ)/2))*a^3*b^0 + (((2835 : ℂ)/4))*a^2*b^1 + ((-675 : ℂ))*a^1*b^2 + ((405 : ℂ))*a^0*b^3 + (((-189 : ℂ)/2))*a^4*b^0 + (((567 : ℂ)/2))*a^3*b^1 + (((-675 : ℂ)/2))*a^2*b^2 + ((270 : ℂ))*a^1*b^3 + (((-405 : ℂ)/2))*a^0*b^4 + (((-27 : ℂ)/2))*a^5*b^0 + (((189 : ℂ)/4))*a^4*b^1 + (((-135 : ℂ)/2))*a^3*b^2 + (((135 : ℂ)/2))*a^2*b^3 + (((-135 : ℂ)/2))*a^1*b^4 + (((189 : ℂ)/4))*a^0*b^5

def S_Ntb_rem2 (a b : ℂ) : ℂ :=
  (((567 : ℂ)/2))*a^0*b^0 + (((-675 : ℂ)/2))*a^0*b^1 + ((270 : ℂ))*a^0*b^2 + (((-405 : ℂ)/2))*a^0*b^3 + (((189 : ℂ)/2))*a^0*b^4 + (((-27 : ℂ)/2))*a^0*b^5

def S_Ntb_rem3 (a b : ℂ) : ℂ :=
  (((-135 : ℂ)/2))*a^0*b^0 + (((135 : ℂ)/2))*a^0*b^1 + (((-135 : ℂ)/2))*a^0*b^2 + (((189 : ℂ)/4))*a^0*b^3 + (((-27 : ℂ)/2))*a^0*b^4

lemma S_Ntb_split (a b : ℂ) :
    S_Ntb a b = a ^ 2 * S_Ntb_rem1 a b + a * b * S_Ntb_rem2 a b + b ^ 2 * S_Ntb_rem3 a b
      + (189 / 4) * b - (189 / 2) * a - 27 / 2 := by
  simp only [S_Ntb, S_Ntb_rem1, S_Ntb_rem2, S_Ntb_rem3]
  ring

lemma Ntbfun_add_216E (τ : ℍ) :
    Ntbfun τ + 216 * Epar τ
      = (acusp τ ^ 2 * bcusp τ * S_Ntb_rem1 (acusp τ) (bcusp τ)
          + acusp τ * bcusp τ ^ 2 * S_Ntb_rem2 (acusp τ) (bcusp τ)
          + bcusp τ ^ 3 * S_Ntb_rem3 (acusp τ) (bcusp τ))
        + (189 / 4) * (bcusp τ * (bcusp τ - 2 * acusp τ))
        - (27 / 2) * (bcusp τ - 16 * Epar τ) := by
  have h := Ntbfun_eq τ
  have h2 := S_Ntb_split (acusp τ) (bcusp τ)
  rw [h, h2]
  ring

/-! ## Boundedness of polynomials in the cusp coordinates -/

/-- Bounded functions, with any `Im τ` threshold. -/
lemma CuspBound.of_bdd' {f : ℍ → ℂ} {H0 C : ℝ} (hC : 0 < C)
    (h : ∀ τ : ℍ, H0 ≤ τ.im → ‖f τ‖ ≤ C) (m : ℕ) : CuspBound f m 0 := by
  refine ⟨max H0 1, C + 1, by linarith, fun τ hτ => ?_⟩
  have h1 := h τ (le_trans (le_max_left _ _) hτ)
  have hA : (1 : ℝ) ≤ (1 + ‖(τ : ℂ)‖) ^ m := one_le_pow₀ (one_le_one_add_norm τ)
  calc ‖f τ‖ ≤ C := h1
    _ ≤ (C + 1) * (1 + ‖(τ : ℂ)‖) ^ m := by nlinarith
    _ = (C + 1) * (1 + ‖(τ : ℂ)‖) ^ m * tpar τ ^ 0 := by ring

/-- Division by a function that dominates `tpar²`. -/
lemma CuspBound.div_of_lower {f g : ℍ → ℂ} {m k : ℕ} {H0 c : ℝ} (hc : 0 < c)
    (hf : CuspBound f m k) (hk : 2 ≤ k)
    (hg : ∀ τ : ℍ, H0 ≤ τ.im → c * tpar τ ^ 2 ≤ ‖g τ‖) :
    CuspBound (fun τ => f τ / g τ) m (k - 2) := by
  obtain ⟨H1, C1, hC1, h1⟩ := hf
  refine ⟨max H0 (max H1 1), C1 / c + 1, by positivity, fun τ hτ => ?_⟩
  have hτ0 : H0 ≤ τ.im := le_trans (le_max_left _ _) hτ
  have hτ1 : H1 ≤ τ.im := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hτ
  have hgτ := hg τ hτ0
  have hfτ := h1 τ hτ1
  have ht0 : 0 < tpar τ := tpar_pos τ
  have hΔpos : 0 < ‖g τ‖ := lt_of_lt_of_le (by positivity) hgτ
  rw [norm_div, div_le_iff₀ hΔpos]
  have hpow : tpar τ ^ k = tpar τ ^ 2 * tpar τ ^ (k - 2) := by
    rw [← pow_add]
    congr 1
    omega
  have hkey : C1 * tpar τ ^ 2 ≤ (C1 / c + 1) * ‖g τ‖ := by
    have h2 : (C1 / c + 1) * (c * tpar τ ^ 2) ≤ (C1 / c + 1) * ‖g τ‖ :=
      mul_le_mul_of_nonneg_left hgτ (by positivity)
    have h3 : (C1 / c + 1) * (c * tpar τ ^ 2) = (C1 + c) * tpar τ ^ 2 := by
      field_simp
    rw [h3] at h2
    nlinarith [tpar_nonneg τ, hc, hC1]
  calc ‖f τ‖ ≤ C1 * (1 + ‖(τ : ℂ)‖) ^ m * tpar τ ^ k := hfτ
    _ = (C1 * tpar τ ^ 2) * ((1 + ‖(τ : ℂ)‖) ^ m * tpar τ ^ (k - 2)) := by rw [hpow]; ring
    _ ≤ ((C1 / c + 1) * ‖g τ‖) * ((1 + ‖(τ : ℂ)‖) ^ m * tpar τ ^ (k - 2)) :=
        mul_le_mul_of_nonneg_right hkey (by positivity)
    _ = (C1 / c + 1) * (1 + ‖(τ : ℂ)‖) ^ m * tpar τ ^ (k - 2) * ‖g τ‖ := by ring

/-- `f = bcusp^j · S(acusp,bcusp)` gives `CuspBound f 0 j`. -/
lemma CuspBound.of_bcusp_pow {f : ℍ → ℂ} {S : ℂ → ℂ → ℂ}
    (hS : Continuous fun p : ℂ × ℂ => S p.1 p.2) {j : ℕ}
    (hid : ∀ τ : ℍ, f τ = bcusp τ ^ j * S (acusp τ) (bcusp τ)) : CuspBound f 0 j := by
  obtain ⟨H1, C1, hC1, h1⟩ := poly2_cusp_bound S hS
  obtain ⟨H2, C2, hC2, h2⟩ := bcusp_bound
  refine ⟨max H1 H2, C1 * C2 ^ j + 1, by positivity, fun τ hτ => ?_⟩
  have hτ1 : H1 ≤ τ.im := le_trans (le_max_left _ _) hτ
  have hτ2 : H2 ≤ τ.im := le_trans (le_max_right _ _) hτ
  have hb := h2 τ hτ2
  have hS1 := h1 τ hτ1
  have ht0 : 0 ≤ tpar τ := tpar_nonneg τ
  rw [hid τ, norm_mul, norm_pow]
  calc ‖bcusp τ‖ ^ j * ‖S (acusp τ) (bcusp τ)‖
      ≤ (C2 * tpar τ) ^ j * C1 :=
        mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hb j) hS1 (norm_nonneg _) (by positivity)
    _ = C1 * C2 ^ j * tpar τ ^ j := by rw [mul_pow]; ring
    _ ≤ (C1 * C2 ^ j + 1) * (1 + ‖(τ : ℂ)‖) ^ 0 * tpar τ ^ j := by
        rw [pow_zero, mul_one]
        have := pow_nonneg ht0 j
        linarith

/-! ## The eight polynomial bounds -/

lemma P1_cusp : CuspBound P1fun 0 2 :=
  CuspBound.of_bcusp_pow (S := S_P1) (by unfold S_P1; fun_prop) P1fun_eq

lemma P2_cusp : CuspBound P2fun 0 2 :=
  CuspBound.of_bcusp_pow (S := S_P2) (by unfold S_P2; fun_prop) P2fun_eq

lemma X_cusp : CuspBound Xfun 0 2 :=
  CuspBound.of_bcusp_pow (S := S_X) (by unfold S_X; fun_prop) Xfun_eq

lemma Q1_cusp : CuspBound Q1fun 0 1 :=
  CuspBound.of_bcusp_pow (S := S_Q1) (by unfold S_Q1; fun_prop) (fun τ => by rw [Q1fun_eq, pow_one])

lemma Q2_cusp : CuspBound Q2fun 0 1 :=
  CuspBound.of_bcusp_pow (S := S_Q2) (by unfold S_Q2; fun_prop) (fun τ => by rw [Q2fun_eq, pow_one])

lemma Y_cusp : CuspBound Yfun 0 1 :=
  CuspBound.of_bcusp_pow (S := S_Y) (by unfold S_Y; fun_prop) (fun τ => by rw [Yfun_eq, pow_one])

lemma Nt_cusp : CuspBound Ntfun 0 4 :=
  CuspBound.of_bcusp_pow (S := S_Nt) (by unfold S_Nt; fun_prop) Ntfun_eq

lemma Ntb_cusp : CuspBound Ntbfun 0 1 :=
  CuspBound.of_bcusp_pow (S := S_Ntb) (by unfold S_Ntb; fun_prop) (fun τ => by rw [Ntbfun_eq, pow_one])

/-! ## Basic single-variable bounds -/

lemma E4_sub_one_cusp : ∃ H C : ℝ, 0 < C ∧ ∀ τ : ℍ, H ≤ τ.im →
    ‖E4Fun τ - 1‖ ≤ C * tpar τ ^ 2 := by
  obtain ⟨C, hC, h⟩ := ThetaDecay.2.2.2.2.1
  refine ⟨1, C, hC, fun τ hτ => ?_⟩
  have h1 := h τ hτ
  rw [show Real.exp (-(2 * Real.pi * τ.im)) = tpar τ ^ 2 from (tpar_pow_two τ).symm] at h1
  exact h1

lemma E4_cusp : CuspBound (fun τ : ℍ => E4Fun τ) 0 0 := by
  obtain ⟨H0, C, hC, h⟩ := E4_sub_one_cusp
  refine CuspBound.of_bdd' (C := C + 1) (H0 := max H0 1) (by linarith) (fun τ hτ => ?_) 0
  have h1 := h τ (le_trans (le_max_left _ _) hτ)
  have h4 := norm_add_le (E4Fun τ - 1) (1 : ℂ)
  rw [sub_add_cancel, norm_one] at h4
  have ht : tpar τ ^ 2 ≤ 1 := pow_le_one₀ (tpar_nonneg τ) (tpar_le_one τ)
  have h2 : C * tpar τ ^ 2 ≤ C := by nlinarith [tpar_nonneg τ]
  linarith

lemma Delta_cusp : CuspBound (fun τ : ℍ => DeltaFun τ) 0 2 := by
  obtain ⟨C, hC, h⟩ := ThetaDecay.2.2.2.1
  refine ⟨1, C, hC, fun τ hτ => ?_⟩
  have h1 := h τ hτ
  rw [show Real.exp (-(2 * Real.pi * τ.im)) = tpar τ ^ 2 from (tpar_pow_two τ).symm] at h1
  simpa using h1

lemma L_cusp (ℓ : LogLambdaData) : CuspBound (fun τ : ℍ => ℓ.L τ) 1 0 := by
  obtain ⟨C, hC, h⟩ := (LogLambdaBound ℓ).1
  refine ⟨1, C + Real.pi + 1, by positivity, fun τ hτ => ?_⟩
  have h1 := h τ hτ
  have h2 : ‖ℓ.L τ‖ ≤ C + Real.pi * ‖(τ : ℂ)‖ := by
    have hsplit : (ℓ.L τ - (Real.pi : ℂ) * Complex.I * (τ : ℂ))
        + (Real.pi : ℂ) * Complex.I * (τ : ℂ) = ℓ.L τ := by ring
    calc ‖ℓ.L τ‖ = ‖(ℓ.L τ - (Real.pi : ℂ) * Complex.I * (τ : ℂ))
          + (Real.pi : ℂ) * Complex.I * (τ : ℂ)‖ := by rw [hsplit]
      _ ≤ ‖ℓ.L τ - (Real.pi : ℂ) * Complex.I * (τ : ℂ)‖
            + ‖(Real.pi : ℂ) * Complex.I * (τ : ℂ)‖ := norm_add_le _ _
      _ ≤ C + Real.pi * ‖(τ : ℂ)‖ := by
          have h3 : ‖(Real.pi : ℂ) * Complex.I * (τ : ℂ)‖ = Real.pi * ‖(τ : ℂ)‖ := by
            rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
              abs_of_pos Real.pi_pos]
          rw [h3]
          linarith
  have h3 : tpar τ ^ 0 = 1 := pow_zero _
  have h4 : (1 + ‖(τ : ℂ)‖) ^ 1 = 1 + ‖(τ : ℂ)‖ := pow_one _
  rw [h3, h4, mul_one]
  nlinarith [norm_nonneg (τ : ℂ), Real.pi_pos, hC]

lemma LS_cusp (ℓ : LogLambdaData) : CuspBound (fun τ : ℍ => ℓ.L_S τ) 0 1 := by
  obtain ⟨C, hC, h⟩ := (LogLambdaBound ℓ).2
  refine ⟨1, C + 1, by linarith, fun τ hτ => ?_⟩
  have h1 : ‖ℓ.L_S τ‖ ≤ C * tpar τ := by
    have hh := h τ hτ
    simpa only [tpar] using hh
  have h3 : (1 + ‖(τ : ℂ)‖) ^ 0 = 1 := pow_zero _
  rw [h3, mul_one, pow_one]
  nlinarith [tpar_nonneg τ]

/-! ## The two brackets `Γ`, `Λ` -/

lemma Gamm_num (ℓ : LogLambdaData) (τ : ℍ) :
    psi2 ℓ τ * E14Fun τ - psi4 ℓ τ * E6Fun τ ^ 2
      = ℓ.L τ * P1fun τ + ℓ.L_S τ * Q1fun τ := by
  simp only [psi2, psi4, P1fun, Q1fun, E14Fun, xi2Fun, xi4Fun,
    xi2Fun_slash_S_apply, xi4Fun_slash_S_apply]
  ring

lemma Lamb_num (ℓ : LogLambdaData) (τ : ℍ) :
    psi4 ℓ τ * E4Fun τ ^ 3 - psi2 ℓ τ * E14Fun τ
      = ℓ.L τ * P2fun τ + ℓ.L_S τ * Q2fun τ := by
  simp only [psi4, psi2, P2fun, Q2fun, E14Fun, xi2Fun, xi4Fun,
    xi2Fun_slash_S_apply, xi4Fun_slash_S_apply]
  ring

lemma Gamma_cusp (ℓ : LogLambdaData) : CuspBound (Gamm ℓ) 1 0 := by
  obtain ⟨Hd, cd, hcd, hd⟩ := DeltaFun_lower
  have hfun : Gamm ℓ = fun τ => (ℓ.L τ * P1fun τ + ℓ.L_S τ * Q1fun τ) / DeltaFun τ := by
    funext τ
    rw [Gamm_eq ℓ τ, Gamm_num ℓ τ]
  rw [hfun]
  refine CuspBound.div_of_lower hcd ?_ (le_refl 2) hd
  have h1 : CuspBound (fun τ => ℓ.L τ * P1fun τ) 1 2 := CuspBound.mul (L_cusp ℓ) P1_cusp
  have h2 : CuspBound (fun τ => ℓ.L_S τ * Q1fun τ) 0 2 := CuspBound.mul (LS_cusp ℓ) Q1_cusp
  exact CuspBound.add h1 h2

lemma Lamb_cusp (ℓ : LogLambdaData) : CuspBound (Lamb ℓ) 1 0 := by
  obtain ⟨Hd, cd, hcd, hd⟩ := DeltaFun_lower
  have hfun : Lamb ℓ = fun τ => (ℓ.L τ * P2fun τ + ℓ.L_S τ * Q2fun τ) / DeltaFun τ := by
    funext τ
    rw [Lamb_eq ℓ τ, Lamb_num ℓ τ]
  rw [hfun]
  refine CuspBound.div_of_lower hcd ?_ (le_refl 2) hd
  have h1 : CuspBound (fun τ => ℓ.L τ * P2fun τ) 1 2 := CuspBound.mul (L_cusp ℓ) P2_cusp
  have h2 : CuspBound (fun τ => ℓ.L_S τ * Q2fun τ) 0 2 := CuspBound.mul (LS_cusp ℓ) Q2_cusp
  exact CuspBound.add h1 h2


/-! ## Polynomials in the cusp coordinates times monomials -/

/-- `‖a^i b^j · S(a,b)‖ = O(tpar^{i+j})` for continuous `S`. -/
lemma poly2_cusp_bound_aux (S : ℂ → ℂ → ℂ)
    (hS : Continuous fun p : ℂ × ℂ => S p.1 p.2) (i j : ℕ) :
    ∃ H C : ℝ, 0 < C ∧ ∀ τ : ℍ, H ≤ τ.im →
      ‖acusp τ ^ i * bcusp τ ^ j * S (acusp τ) (bcusp τ)‖ ≤ C * tpar τ ^ (i + j) := by
  obtain ⟨D, hD0, hD⟩ := exists_norm_poly2_le S hS
  obtain ⟨H1, C1, hC1, h1⟩ := acusp_bound
  obtain ⟨H2, C2, hC2, h2⟩ := bcusp_bound
  set C0 : ℝ := max (max C1 C2) (1 / 2) with hC0
  have hC0n : 0 ≤ C0 := le_trans (by norm_num) (le_max_right _ _)
  have hC0pos : 0 < C0 := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  refine ⟨max (max H1 H2) (max 1 ((C0 + 1) / Real.pi + 1)),
      C0 ^ (i + j) * (D + 1) + 1, by positivity, fun τ hτ => ?_⟩
  obtain ⟨hτA, hτB⟩ := max_le_iff.mp hτ
  obtain ⟨hτH1, hτH2⟩ := max_le_iff.mp hτA
  obtain ⟨_hτ1, hτbig'⟩ := max_le_iff.mp hτB
  have ht : C0 * tpar τ ≤ 1 := by
    have h := tpar_le_inv_add_one hC0n hτbig'
    have h3 : C0 * (1 / (C0 + 1)) ≤ 1 := by
      rw [mul_one_div, div_le_one (by linarith)]
      linarith
    exact le_trans (mul_le_mul_of_nonneg_left h hC0n) h3
  have ha : ‖acusp τ‖ ≤ C0 * tpar τ := by
    refine le_trans (h1 τ hτH1) ?_
    exact mul_le_mul_of_nonneg_right (le_trans (le_max_left _ _) (le_max_left _ _)) (tpar_nonneg τ)
  have hb : ‖bcusp τ‖ ≤ C0 * tpar τ := by
    refine le_trans (h2 τ hτH2) ?_
    exact mul_le_mul_of_nonneg_right (le_trans (le_max_right _ _) (le_max_left _ _)) (tpar_nonneg τ)
  have hS1 : ‖S (acusp τ) (bcusp τ)‖ ≤ D + 1 := by
    have h4 : ‖acusp τ‖ ≤ 1 := le_trans ha ht
    have h5 : ‖bcusp τ‖ ≤ 1 := le_trans hb ht
    linarith [hD (acusp τ) (bcusp τ) h4 h5]
  have hNC0 : (0 : ℝ) ≤ (C0 * tpar τ) ^ (i + j) := by
    rw [mul_pow]
    exact mul_nonneg (pow_nonneg hC0n _) (pow_nonneg (tpar_nonneg τ) _)
  have hpow : ‖acusp τ‖ ^ i * ‖bcusp τ‖ ^ j ≤ (C0 * tpar τ) ^ (i + j) := by
    have h1 : ‖acusp τ‖ ^ i ≤ (C0 * tpar τ) ^ i := pow_le_pow_left₀ (norm_nonneg _) ha i
    have h2 : ‖bcusp τ‖ ^ j ≤ (C0 * tpar τ) ^ j := pow_le_pow_left₀ (norm_nonneg _) hb j
    have h3 := mul_le_mul h1 h2 (pow_nonneg (norm_nonneg _) j)
      (pow_nonneg (mul_nonneg hC0n (tpar_nonneg τ)) i)
    rwa [← pow_add] at h3
  rw [norm_mul, norm_mul, norm_pow, norm_pow]
  calc ‖acusp τ‖ ^ i * ‖bcusp τ‖ ^ j * ‖S (acusp τ) (bcusp τ)‖
      ≤ (C0 * tpar τ) ^ (i + j) * (D + 1) :=
        mul_le_mul hpow hS1 (by positivity) (by positivity)
    _ = C0 ^ (i + j) * (D + 1) * tpar τ ^ (i + j) := by rw [mul_pow]; ring
    _ ≤ (C0 ^ (i + j) * (D + 1) + 1) * tpar τ ^ (i + j) := by
        have := pow_nonneg (tpar_nonneg τ) (i + j)
        nlinarith

/-! ## The sharp second-order bound `Ñ + 216E = O(tpar³)` -/

theorem Ntb_216E_bound : ∃ H C : ℝ, 0 < C ∧ ∀ τ : ℍ, H ≤ τ.im →
    ‖Ntbfun τ + 216 * Epar τ‖ ≤ C * tpar τ ^ 3 := by
  obtain ⟨Ha, Ca, hCa, ha⟩ :=
    poly2_cusp_bound_aux (fun a b => S_Ntb_rem1 a b) (by unfold S_Ntb_rem1; fun_prop) 2 1
  obtain ⟨Hb, Cb, hCb, hb⟩ :=
    poly2_cusp_bound_aux (fun a b => S_Ntb_rem2 a b) (by unfold S_Ntb_rem2; fun_prop) 1 2
  obtain ⟨Hc, Cc, hCc, hc⟩ :=
    poly2_cusp_bound_aux (fun a b => S_Ntb_rem3 a b) (by unfold S_Ntb_rem3; fun_prop) 0 3
  obtain ⟨Hd, Cd, hCd, hd⟩ := bcusp_bound
  obtain ⟨He, Ce, hCe, he⟩ := bcusp_expansion
  obtain ⟨Hf, Cf, hCf, hf⟩ := acusp_expansion
  refine ⟨max (max (max Ha Hb) (max Hc Hd)) (max (max He Hf) 1),
      Ca + Cb + Cc + (189 / 4) * (Cd * (Ce + 2 * Cf)) + (27 / 2) * Ce + 1, by positivity,
    fun τ hτ => ?_⟩
  obtain ⟨hτA, hτB⟩ := max_le_iff.mp hτ
  obtain ⟨hτab, hτcd⟩ := max_le_iff.mp hτA
  obtain ⟨hτef, _hτ1⟩ := max_le_iff.mp hτB
  obtain ⟨hτa, hτb⟩ := max_le_iff.mp hτab
  obtain ⟨hτc, hτd⟩ := max_le_iff.mp hτcd
  obtain ⟨hτe, hτf⟩ := max_le_iff.mp hτef
  have ht0 : 0 ≤ tpar τ := tpar_nonneg τ
  have ht1 : tpar τ ≤ 1 := tpar_le_one τ
  have ht43 : tpar τ ^ 4 ≤ tpar τ ^ 3 := by
    have h := pow_le_pow_of_le_one ht0 ht1 (show 3 ≤ 4 by norm_num)
    simpa using h
  set T1 : ℂ := acusp τ ^ 2 * bcusp τ * S_Ntb_rem1 (acusp τ) (bcusp τ) with hT1
  set T2 : ℂ := acusp τ * bcusp τ ^ 2 * S_Ntb_rem2 (acusp τ) (bcusp τ) with hT2
  set T3 : ℂ := bcusp τ ^ 3 * S_Ntb_rem3 (acusp τ) (bcusp τ) with hT3
  set D1 : ℂ := (189 / 4) * (bcusp τ * (bcusp τ - 2 * acusp τ)) with hD1
  set E1 : ℂ := (27 / 2) * (bcusp τ - 16 * Epar τ) with hE1
  have hA : ‖T1‖ ≤ Ca * tpar τ ^ 3 := by
    rw [hT1]
    simpa using ha τ hτa
  have hB : ‖T2‖ ≤ Cb * tpar τ ^ 3 := by
    rw [hT2]
    simpa using hb τ hτb
  have hC' : ‖T3‖ ≤ Cc * tpar τ ^ 3 := by
    rw [hT3]
    simpa using hc τ hτc
  have hb' := hd τ hτd
  have he' := he τ hτe
  have hf' := hf τ hτf
  have hinner : ‖bcusp τ - 2 * acusp τ‖ ≤ Ce * tpar τ ^ 3 + 2 * (Cf * tpar τ ^ 2) := by
    have hsplit : bcusp τ - 2 * acusp τ
        = (bcusp τ - 16 * Epar τ) - 2 * (acusp τ - 8 * Epar τ) := by ring
    calc ‖bcusp τ - 2 * acusp τ‖
        = ‖(bcusp τ - 16 * Epar τ) - 2 * (acusp τ - 8 * Epar τ)‖ := by rw [hsplit]
      _ ≤ ‖bcusp τ - 16 * Epar τ‖ + ‖2 * (acusp τ - 8 * Epar τ)‖ := norm_sub_le _ _
      _ ≤ Ce * tpar τ ^ 3 + 2 * (Cf * tpar τ ^ 2) := by
          have h6 : ‖2 * (acusp τ - 8 * Epar τ)‖ = 2 * ‖acusp τ - 8 * Epar τ‖ := by
            rw [norm_mul, Complex.norm_ofNat]
          rw [h6]
          linarith
  have hD : ‖D1‖ ≤ (189 / 4) * (Cd * (Ce + 2 * Cf)) * tpar τ ^ 3 := by
    have hnorm : ‖D1‖ = 189 / 4 * (‖bcusp τ‖ * ‖bcusp τ - 2 * acusp τ‖) := by
      rw [hD1]
      simp only [norm_mul, norm_div, Complex.norm_ofNat]
    rw [hnorm]
    have h7 : ‖bcusp τ‖ * ‖bcusp τ - 2 * acusp τ‖
        ≤ (Cd * tpar τ) * (Ce * tpar τ ^ 3 + 2 * (Cf * tpar τ ^ 2)) :=
      mul_le_mul hb' hinner (norm_nonneg _) (by positivity)
    have h8 : (Cd * tpar τ) * (Ce * tpar τ ^ 3 + 2 * (Cf * tpar τ ^ 2))
        ≤ (Cd * (Ce + 2 * Cf)) * tpar τ ^ 3 := by
      have h9 : (Cd * tpar τ) * (Ce * tpar τ ^ 3 + 2 * (Cf * tpar τ ^ 2))
          = Cd * Ce * tpar τ ^ 4 + 2 * (Cd * Cf * tpar τ ^ 3) := by ring
      rw [h9]
      have h10 : Cd * Ce * tpar τ ^ 4 ≤ Cd * Ce * tpar τ ^ 3 :=
        mul_le_mul_of_nonneg_left ht43 (by positivity)
      nlinarith [h10, pow_nonneg ht0 3, hCd, hCe, hCf]
    calc 189 / 4 * (‖bcusp τ‖ * ‖bcusp τ - 2 * acusp τ‖)
        ≤ 189 / 4 * ((Cd * tpar τ) * (Ce * tpar τ ^ 3 + 2 * (Cf * tpar τ ^ 2))) :=
          mul_le_mul_of_nonneg_left h7 (by norm_num)
      _ ≤ 189 / 4 * ((Cd * (Ce + 2 * Cf)) * tpar τ ^ 3) :=
          mul_le_mul_of_nonneg_left h8 (by norm_num)
      _ = 189 / 4 * (Cd * (Ce + 2 * Cf)) * tpar τ ^ 3 := by ring
  have hE : ‖E1‖ ≤ (27 / 2) * Ce * tpar τ ^ 3 := by
    have hnorm : ‖E1‖ = 27 / 2 * ‖bcusp τ - 16 * Epar τ‖ := by
      rw [hE1]
      simp only [norm_mul, norm_div, Complex.norm_ofNat]
    rw [hnorm]
    have := mul_le_mul_of_nonneg_left he' (by norm_num : (0:ℝ) ≤ 27 / 2)
    linarith
  have hsum : ‖T1 + T2 + T3‖ ≤ (Ca + Cb + Cc) * tpar τ ^ 3 := by
    have h6 : ‖T1 + T2‖ ≤ (Ca + Cb) * tpar τ ^ 3 := by
      calc ‖T1 + T2‖ ≤ ‖T1‖ + ‖T2‖ := norm_add_le _ _
        _ ≤ Ca * tpar τ ^ 3 + Cb * tpar τ ^ 3 := add_le_add hA hB
        _ = (Ca + Cb) * tpar τ ^ 3 := by ring
    calc ‖T1 + T2 + T3‖ ≤ ‖T1 + T2‖ + ‖T3‖ := norm_add_le _ _
      _ ≤ (Ca + Cb) * tpar τ ^ 3 + Cc * tpar τ ^ 3 := add_le_add h6 hC'
      _ = (Ca + Cb + Cc) * tpar τ ^ 3 := by ring
  rw [Ntbfun_add_216E τ, ← hT1, ← hT2, ← hT3, ← hD1, ← hE1]
  calc ‖T1 + T2 + T3 + D1 - E1‖ ≤ ‖T1 + T2 + T3 + D1‖ + ‖E1‖ := norm_sub_le _ _
    _ ≤ (‖T1 + T2 + T3‖ + ‖D1‖) + ‖E1‖ := by linarith [norm_add_le (T1 + T2 + T3) D1]
    _ ≤ ((Ca + Cb + Cc) * tpar τ ^ 3 + (189 / 4) * (Cd * (Ce + 2 * Cf)) * tpar τ ^ 3)
          + (27 / 2) * Ce * tpar τ ^ 3 := add_le_add (add_le_add hsum hD) hE
    _ ≤ (Ca + Cb + Cc + (189 / 4) * (Cd * (Ce + 2 * Cf)) + (27 / 2) * Ce + 1) * tpar τ ^ 3 := by
        have := pow_nonneg ht0 3
        nlinarith [this]


/-! ## `B₀` and `Ccore` -/

lemma CuspBound.congr {f g : ℍ → ℂ} {m k : ℕ} (h : CuspBound f m k)
    (hfg : ∀ τ : ℍ, f τ = g τ) : CuspBound g m k := by
  obtain ⟨H, C, hC, hb⟩ := h
  exact ⟨H, C, hC, fun τ hτ => by rw [← hfg τ]; exact hb τ hτ⟩

lemma B0core_cusp : CuspBound B0core 0 2 := by
  obtain ⟨H1, C1, hC1, h1⟩ := Nt_cusp
  obtain ⟨H2, C2, hC2, h2⟩ := E4_cusp
  obtain ⟨H3, c3, hc3, h3⟩ := DeltaFun_lower
  refine ⟨max (max H1 H2) H3, C1 * C2 ^ 2 / c3 + 1, by positivity, fun τ hτ => ?_⟩
  obtain ⟨hτA, hτ3⟩ := max_le_iff.mp hτ
  obtain ⟨hτ1, hτ2⟩ := max_le_iff.mp hτA
  have hA := h1 τ hτ1
  have hB := h2 τ hτ2
  have hD := h3 τ hτ3
  simp only [pow_zero, mul_one] at hA hB
  have ht0 : 0 ≤ tpar τ := tpar_nonneg τ
  rw [B0core, norm_div]
  have hΔpos : 0 < ‖DeltaFun τ‖ := lt_of_lt_of_le (mul_pos hc3 (pow_pos (tpar_pos τ) 2)) hD
  rw [div_le_iff₀ hΔpos]
  have h10 : ‖E4Fun τ ^ 2 * Ntfun τ‖ = ‖E4Fun τ‖ ^ 2 * ‖Ntfun τ‖ := by rw [norm_mul, norm_pow]
  rw [h10, pow_zero, mul_one]
  have h4 : ‖E4Fun τ‖ ^ 2 * ‖Ntfun τ‖ ≤ C1 * C2 ^ 2 * tpar τ ^ 4 := by
    have h5 : ‖E4Fun τ‖ ^ 2 ≤ C2 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hB 2
    have h6 := mul_le_mul h5 hA (norm_nonneg _) (by positivity : (0:ℝ) ≤ C2 ^ 2)
    calc ‖E4Fun τ‖ ^ 2 * ‖Ntfun τ‖ ≤ C2 ^ 2 * (C1 * tpar τ ^ 4) := h6
      _ = C1 * C2 ^ 2 * tpar τ ^ 4 := by ring
  have h7 : C1 * C2 ^ 2 * tpar τ ^ 4
      ≤ (C1 * C2 ^ 2 / c3 + 1) * tpar τ ^ 2 * ‖DeltaFun τ‖ := by
    have h8 : (C1 * C2 ^ 2 / c3 + 1) * (c3 * tpar τ ^ 2)
        ≤ (C1 * C2 ^ 2 / c3 + 1) * ‖DeltaFun τ‖ :=
      mul_le_mul_of_nonneg_left hD (by positivity)
    have h9 : (C1 * C2 ^ 2 / c3 + 1) * (c3 * tpar τ ^ 2) = (C1 * C2 ^ 2 + c3) * tpar τ ^ 2 := by
      field_simp
    rw [h9] at h8
    have h11 : (C1 * C2 ^ 2 + c3) * tpar τ ^ 2 * tpar τ ^ 2
        ≤ (C1 * C2 ^ 2 / c3 + 1) * ‖DeltaFun τ‖ * tpar τ ^ 2 :=
      mul_le_mul_of_nonneg_right h8 (pow_nonneg ht0 2)
    have ht4 : tpar τ ^ 4 = tpar τ ^ 2 * tpar τ ^ 2 := by ring
    nlinarith [h11, ht4, hc3, hC1, hC2, norm_nonneg (DeltaFun τ), pow_nonneg ht0 2]
  linarith [h4, h7]

lemma Ccore_id (ℓ : LogLambdaData) (τ : ℍ) :
    Ccore ℓ τ = E4Fun τ ^ 2 / DeltaFun τ
      * (ℓ.L_S τ * Ntbfun τ - 3456 * E4Fun τ * DeltaFun τ) := by
  have hD : DeltaFun τ ≠ 0 := ClassicalFacts.DeltaFun_ne_zero τ
  rw [Ccore]
  field_simp

lemma Ccore_cusp (ℓ : LogLambdaData) : CuspBound (Ccore ℓ) 0 2 := by
  obtain ⟨H1, C1, hC1, h1⟩ := LS_expansion ℓ
  obtain ⟨H2, C2, hC2, h2⟩ := Ntb_cusp
  obtain ⟨H3, C3, hC3, h3⟩ := Ntb_216E_bound
  obtain ⟨H4, C4, hC4, h4⟩ := Deltafun_expansion
  obtain ⟨H5, C5, hC5, h5⟩ := E4_sub_one_cusp
  obtain ⟨H6, C6, hC6, h6⟩ := E4_cusp
  obtain ⟨H7, C7, hC7, h7⟩ := Delta_cusp
  obtain ⟨H8, c8, hc8, h8⟩ := DeltaFun_lower
  refine ⟨max (max (max H1 H2) (max H3 H4)) (max (max H5 H6) (max H7 H8)),
      C6 ^ 2 * (C1 * C2 + 16 * C3 + 3456 * (C4 + C5 * C7) + 1) / c8 + 1, by positivity,
    fun τ hτ => ?_⟩
  obtain ⟨hτA, hτB⟩ := max_le_iff.mp hτ
  obtain ⟨hτab, hτcd⟩ := max_le_iff.mp hτA
  obtain ⟨hτef, hτgh⟩ := max_le_iff.mp hτB
  obtain ⟨hτ1, hτ2⟩ := max_le_iff.mp hτab
  obtain ⟨hτ3, hτ4⟩ := max_le_iff.mp hτcd
  obtain ⟨hτ5, hτ6⟩ := max_le_iff.mp hτef
  obtain ⟨hτ7, hτ8⟩ := max_le_iff.mp hτgh
  have ha := h1 τ hτ1
  have hb := h2 τ hτ2
  have hc := h3 τ hτ3
  have hd := h4 τ hτ4
  have he := h5 τ hτ5
  have hf := h6 τ hτ6
  have hg := h7 τ hτ7
  have hh := h8 τ hτ8
  simp only [pow_zero, mul_one, pow_one] at hb hf hg
  have hkey : ‖ℓ.L_S τ * Ntbfun τ - 3456 * E4Fun τ * DeltaFun τ‖
      ≤ (C1 * C2 + 16 * C3 + 3456 * (C4 + C5 * C7)) * tpar τ ^ 4 := by
    have hid : ℓ.L_S τ * Ntbfun τ - 3456 * E4Fun τ * DeltaFun τ
        = (ℓ.L_S τ + 16 * Epar τ) * Ntbfun τ - 16 * Epar τ * (Ntbfun τ + 216 * Epar τ)
          + 3456 * (Epar τ ^ 2 - E4Fun τ * DeltaFun τ) := by ring
    rw [hid]
    have hp1 : ‖(ℓ.L_S τ + 16 * Epar τ) * Ntbfun τ‖ ≤ C1 * C2 * tpar τ ^ 4 := by
      rw [norm_mul]
      have ht0 : 0 ≤ tpar τ := tpar_nonneg τ
      calc ‖ℓ.L_S τ + 16 * Epar τ‖ * ‖Ntbfun τ‖ ≤ (C1 * tpar τ ^ 3) * (C2 * tpar τ) :=
            mul_le_mul ha hb (norm_nonneg _) (mul_nonneg hC1.le (pow_nonneg ht0 3))
        _ = C1 * C2 * tpar τ ^ 4 := by ring
    have hp2 : ‖16 * Epar τ * (Ntbfun τ + 216 * Epar τ)‖ ≤ 16 * C3 * tpar τ ^ 4 := by
      rw [norm_mul, norm_mul, Complex.norm_ofNat, norm_Epar]
      calc 16 * tpar τ * ‖Ntbfun τ + 216 * Epar τ‖ ≤ 16 * tpar τ * (C3 * tpar τ ^ 3) :=
            mul_le_mul_of_nonneg_left hc (mul_nonneg (by norm_num) (tpar_nonneg τ))
        _ = 16 * C3 * tpar τ ^ 4 := by ring
    have hp3 : ‖3456 * (Epar τ ^ 2 - E4Fun τ * DeltaFun τ)‖
        ≤ 3456 * (C4 + C5 * C7) * tpar τ ^ 4 := by
      rw [norm_mul, Complex.norm_ofNat]
      have hsplit : Epar τ ^ 2 - E4Fun τ * DeltaFun τ
          = (Epar τ ^ 2 - DeltaFun τ) + (1 - E4Fun τ) * DeltaFun τ := by ring
      rw [hsplit]
      have h1' : ‖(Epar τ ^ 2 - DeltaFun τ) + (1 - E4Fun τ) * DeltaFun τ‖
          ≤ C4 * tpar τ ^ 4 + C5 * tpar τ ^ 2 * (C7 * tpar τ ^ 2) := by
        calc ‖(Epar τ ^ 2 - DeltaFun τ) + (1 - E4Fun τ) * DeltaFun τ‖
            ≤ ‖Epar τ ^ 2 - DeltaFun τ‖ + ‖(1 - E4Fun τ) * DeltaFun τ‖ := norm_add_le _ _
          _ ≤ C4 * tpar τ ^ 4 + C5 * tpar τ ^ 2 * (C7 * tpar τ ^ 2) := by
              refine add_le_add ?_ ?_
              · rw [norm_sub_rev]
                exact hd
              · rw [norm_mul, show ‖(1 : ℂ) - E4Fun τ‖ = ‖E4Fun τ - 1‖ by
                  rw [show (1 : ℂ) - E4Fun τ = -(E4Fun τ - 1) by ring, norm_neg]]
                exact mul_le_mul he hg (norm_nonneg _)
                  (mul_nonneg hC5.le (pow_nonneg (tpar_nonneg τ) 2))
      calc 3456 * ‖(Epar τ ^ 2 - DeltaFun τ) + (1 - E4Fun τ) * DeltaFun τ‖
          ≤ 3456 * (C4 * tpar τ ^ 4 + C5 * tpar τ ^ 2 * (C7 * tpar τ ^ 2)) := by
            have := mul_le_mul_of_nonneg_left h1' (by norm_num : (0:ℝ) ≤ 3456)
            linarith
        _ = 3456 * (C4 + C5 * C7) * tpar τ ^ 4 := by ring
    calc ‖(ℓ.L_S τ + 16 * Epar τ) * Ntbfun τ - 16 * Epar τ * (Ntbfun τ + 216 * Epar τ)
          + 3456 * (Epar τ ^ 2 - E4Fun τ * DeltaFun τ)‖
        ≤ ‖(ℓ.L_S τ + 16 * Epar τ) * Ntbfun τ - 16 * Epar τ * (Ntbfun τ + 216 * Epar τ)‖
          + ‖3456 * (Epar τ ^ 2 - E4Fun τ * DeltaFun τ)‖ := norm_add_le _ _
      _ ≤ (C1 * C2 * tpar τ ^ 4 + 16 * C3 * tpar τ ^ 4) + 3456 * (C4 + C5 * C7) * tpar τ ^ 4 := by
          refine add_le_add ?_ hp3
          calc ‖(ℓ.L_S τ + 16 * Epar τ) * Ntbfun τ - 16 * Epar τ * (Ntbfun τ + 216 * Epar τ)‖
              ≤ ‖(ℓ.L_S τ + 16 * Epar τ) * Ntbfun τ‖
                + ‖16 * Epar τ * (Ntbfun τ + 216 * Epar τ)‖ := norm_sub_le _ _
            _ ≤ C1 * C2 * tpar τ ^ 4 + 16 * C3 * tpar τ ^ 4 := add_le_add hp1 hp2
      _ = (C1 * C2 + 16 * C3 + 3456 * (C4 + C5 * C7)) * tpar τ ^ 4 := by ring
  rw [Ccore_id ℓ τ, norm_mul, norm_div, div_mul_eq_mul_div]
  have hΔpos : 0 < ‖DeltaFun τ‖ := lt_of_lt_of_le (mul_pos hc8 (pow_pos (tpar_pos τ) 2)) hh
  rw [div_le_iff₀ hΔpos]
  have hE2 : ‖E4Fun τ ^ 2‖ ≤ C6 ^ 2 := by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hf 2
  have hm : ‖E4Fun τ ^ 2‖ * ‖ℓ.L_S τ * Ntbfun τ - 3456 * E4Fun τ * DeltaFun τ‖
      ≤ C6 ^ 2 * ((C1 * C2 + 16 * C3 + 3456 * (C4 + C5 * C7)) * tpar τ ^ 4) := by
    have hC6sq : (0 : ℝ) ≤ C6 ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_right hE2 (norm_nonneg _) |>.trans
      (mul_le_mul_of_nonneg_left hkey hC6sq)
  have hfin : C6 ^ 2 * ((C1 * C2 + 16 * C3 + 3456 * (C4 + C5 * C7)) * tpar τ ^ 4)
      ≤ (C6 ^ 2 * (C1 * C2 + 16 * C3 + 3456 * (C4 + C5 * C7) + 1) / c8 + 1)
          * (1 + ‖(τ : ℂ)‖) ^ 0 * tpar τ ^ 2 * ‖DeltaFun τ‖ := by
    rw [pow_zero, mul_one]
    have h9 : (C6 ^ 2 * (C1 * C2 + 16 * C3 + 3456 * (C4 + C5 * C7) + 1) / c8 + 1)
        * (c8 * tpar τ ^ 2)
        = (C6 ^ 2 * (C1 * C2 + 16 * C3 + 3456 * (C4 + C5 * C7) + 1) + c8) * tpar τ ^ 2 := by
      field_simp
    have h10 := mul_le_mul_of_nonneg_left hh (by positivity :
      (0 : ℝ) ≤ C6 ^ 2 * (C1 * C2 + 16 * C3 + 3456 * (C4 + C5 * C7) + 1) / c8 + 1)
    rw [h9] at h10
    have ht2 : (0 : ℝ) ≤ tpar τ ^ 2 := by positivity
    have ht4 : tpar τ ^ 4 = tpar τ ^ 2 * tpar τ ^ 2 := by ring
    nlinarith [h10, ht2, ht4, hc8, hC6, hC1, hC2, hC3, hC4, hC5, hC7,
      norm_nonneg (DeltaFun τ)]
  linarith [hm, hfin]

/-! ## The bracket bounds -/

lemma Bprime_cusp (ℓ : LogLambdaData) (z : ℍ) : CuspBound (Bprimefun ℓ z) 1 2 := by
  have hL := L_cusp ℓ
  have hLS := LS_cusp ℓ
  have h0 := B0core_cusp
  have hX := X_cusp
  have hY := Y_cusp
  have hC := Ccore_cusp ℓ
  have hD := Delta_cusp
  have h1 : CuspBound (fun τ => ℓ.L τ * B0core τ) 1 2 := CuspBound.mul hL h0
  have h2 : CuspBound (fun τ => (2 * jInvariantFun z) * (ℓ.L τ * Xfun τ)) 1 2 :=
    CuspBound.congr
      (CuspBound.mono (CuspBound.mul (CuspBound.const_mul (2 * jInvariantFun z) hL) hX)
        (by decide) (by decide)) (fun τ => by ring)
  have h3 : CuspBound (fun τ => (2 * jInvariantFun z) * (ℓ.L_S τ * Yfun τ)) 0 2 :=
    CuspBound.congr
      (CuspBound.mono (CuspBound.mul (CuspBound.const_mul (2 * jInvariantFun z) hLS) hY)
        (by decide) (by decide)) (fun τ => by ring)
  have h4 : CuspBound (fun τ => (3456 * jInvariantFun z) * DeltaFun τ) 0 2 :=
    CuspBound.const_mul (3456 * jInvariantFun z) hD
  have hsum : CuspBound (fun τ => ℓ.L τ * B0core τ + (2 * jInvariantFun z) * (ℓ.L τ * Xfun τ)
        + Ccore ℓ τ + (2 * jInvariantFun z) * (ℓ.L_S τ * Yfun τ)
        + (3456 * jInvariantFun z) * DeltaFun τ) 1 2 :=
    CuspBound.add (CuspBound.add (CuspBound.add (CuspBound.add h1 h2) hC) h3) h4
  refine CuspBound.congr (CuspBound.mono hsum (by decide) (by decide)) (fun τ => ?_)
  rw [Bprimefun]
  ring

lemma bracket8_cusp (ℓ : LogLambdaData) (z : ℍ) : CuspBound (bracket8 ℓ z) 1 0 := by
  have h1 : CuspBound (fun τ => (((-2 : ℂ) * c1728) * E10Fun z * ℓ.L z) * E4Fun τ) 0 0 :=
    CuspBound.const_mul (((-2 : ℂ) * c1728) * E10Fun z * ℓ.L z) E4_cusp
  have h2 : CuspBound (fun τ => (E8Fun z * WFun z) * Gamm ℓ τ) 1 0 :=
    CuspBound.const_mul (E8Fun z * WFun z) (Gamma_cusp ℓ)
  have h3 : CuspBound (fun τ => (E6Fun z * (UFun z ^ 2 - VFun z ^ 2)) * Lamb ℓ τ) 1 0 :=
    CuspBound.const_mul (E6Fun z * (UFun z ^ 2 - VFun z ^ 2)) (Lamb_cusp ℓ)
  refine CuspBound.congr (CuspBound.mono (CuspBound.add (CuspBound.add h1 h2) h3)
    (by decide) (by decide)) (fun τ => ?_)
  rw [bracket8]
  ring_nf

lemma bracket24_cusp (ℓ : LogLambdaData) (z : ℍ) : CuspBound (bracket24 ℓ z) 1 2 := by
  have hbp := Bprime_cusp ℓ z
  have hbpe : CuspBound (BprimeExp ℓ z) 1 2 :=
    CuspBound.congr hbp (fun τ => Bprimefun_eq ℓ z τ)
  have hp : CuspBound (fun τ => psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ) 1 2 :=
    CuspBound.congr
      (CuspBound.add (CuspBound.mul (L_cusp ℓ) X_cusp) (CuspBound.mul (LS_cusp ℓ) Y_cusp))
      (fun τ => (psi4E8_sub ℓ τ).symm)
  have h1 : CuspBound (fun τ => WFun z * BprimeExp ℓ z τ) 1 2 :=
    CuspBound.const_mul (WFun z) hbpe
  have h2 : CuspBound (fun τ => ((E10Fun z / DeltaFun z) * (UFun z ^ 2 - VFun z ^ 2))
        * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ)) 1 2 :=
    CuspBound.const_mul ((E10Fun z / DeltaFun z) * (UFun z ^ 2 - VFun z ^ 2)) hp
  have h3 : CuspBound (fun τ => ((-3456 * (E14Fun z / DeltaFun z)) * ℓ.L z) * DeltaFun τ) 0 2 :=
    CuspBound.const_mul ((-3456 * (E14Fun z / DeltaFun z)) * ℓ.L z) Delta_cusp
  refine CuspBound.congr (CuspBound.mono (CuspBound.add (CuspBound.add h1 h2) h3)
    (by decide) (by decide)) (fun τ => ?_)
  rw [bracket24]
  ring_nf

/-! ## The prefactor `kpre` -/

/-- The prefactor `2·1728·π·Δ(z)·(j(τ) − j(z))` of `Υ_-`. -/
def kpre (z τ : ℍ) : ℂ :=
  2 * c1728 * (Real.pi : ℂ) * DeltaFun z * (jInvariantFun τ - jInvariantFun z)

lemma kpre_inv_cusp (z : ℍ) : CuspBound (fun τ => (kpre z τ)⁻¹) 0 2 := by
  obtain ⟨H1, C1, hC1, h1⟩ := E4_sub_one_cusp
  obtain ⟨H2, C2, hC2, h2⟩ := Delta_cusp
  have hDz : DeltaFun z ≠ 0 := ClassicalFacts.DeltaFun_ne_zero z
  have hDzpos : 0 < ‖DeltaFun z‖ := norm_pos_iff.mpr hDz
  set M : ℝ := max ‖jInvariantFun z‖ 1 with hM
  have hM1 : (1 : ℝ) ≤ M := le_max_right _ _
  have hMz : ‖jInvariantFun z‖ ≤ M := le_max_left _ _
  set N : ℝ := max (max (2 * C1) (16 * C2 * M)) 1 with hN
  have hN2 : 2 * C1 ≤ N := le_trans (le_max_left _ _) (le_max_left _ _)
  have hN3 : 16 * C2 * M ≤ N := le_trans (le_max_right _ _) (le_max_left _ _)
  have hN1 : (1 : ℝ) ≤ N := le_max_right _ _
  have hNpos : 0 < N := lt_of_lt_of_le one_pos hN1
  refine ⟨max (max H1 H2) (max 1 ((N + 1) / Real.pi + 1)),
      8 * C2 / (1728 * Real.pi * ‖DeltaFun z‖) + 1, by positivity, fun τ hτ => ?_⟩
  obtain ⟨hτA, hτB⟩ := max_le_iff.mp hτ
  obtain ⟨hτ1, hτ2⟩ := max_le_iff.mp hτA
  obtain ⟨_hτ1', hτbig⟩ := max_le_iff.mp hτB
  have ha := h1 τ hτ1
  have hb := h2 τ hτ2
  simp only [pow_zero, mul_one] at hb
  have htpos : 0 < tpar τ := tpar_pos τ
  have ht0 : 0 ≤ tpar τ := tpar_nonneg τ
  have ht1 : tpar τ ≤ 1 := tpar_le_one τ
  have htsq : tpar τ ^ 2 ≤ tpar τ := by
    have := pow_le_pow_of_le_one ht0 ht1 (show 1 ≤ 2 by norm_num)
    simpa using this
  have htN : tpar τ ≤ 1 / N := by
    have h := tpar_le_inv_add_one (by linarith : (0 : ℝ) ≤ N) hτbig
    have h2' : 1 / (N + 1) ≤ 1 / N := by
      rw [one_div, one_div, inv_le_inv₀ (by linarith) hNpos]
      linarith
    linarith
  have hC1t : C1 * tpar τ ≤ 1 / 2 := by
    have h2' : C1 * tpar τ ≤ C1 * (1 / N) := mul_le_mul_of_nonneg_left htN hC1.le
    have h3' : C1 * (1 / N) ≤ 1 / 2 := by
      rw [mul_one_div, div_le_div_iff₀ hNpos (by norm_num : (0:ℝ) < 2)]
      linarith
    linarith
  have hC2t : 16 * C2 * M * tpar τ ≤ 1 := by
    have h2' : 16 * C2 * M * tpar τ ≤ 16 * C2 * M * (1 / N) :=
      mul_le_mul_of_nonneg_left htN (by positivity)
    have h3' : 16 * C2 * M * (1 / N) ≤ 1 := by
      rw [mul_one_div, div_le_one hNpos]
      linarith
    linarith
  have hE4sub : ‖E4Fun τ - 1‖ ≤ 1 / 2 := by
    calc ‖E4Fun τ - 1‖ ≤ C1 * tpar τ ^ 2 := ha
      _ ≤ C1 * tpar τ := mul_le_mul_of_nonneg_left htsq hC1.le
      _ ≤ 1 / 2 := hC1t
  have hE4low : (1 / 8 : ℝ) ≤ ‖E4Fun τ‖ ^ 3 := by
    have h2' : (1 / 2 : ℝ) ≤ ‖E4Fun τ‖ := half_le_norm_of_norm_sub_one_le hE4sub
    have h3' : ((1 : ℝ) / 2) ^ 3 ≤ ‖E4Fun τ‖ ^ 3 := pow_le_pow_left₀ (by norm_num) h2' 3
    norm_num at h3'
    exact h3'
  have hΔpos : 0 < ‖DeltaFun τ‖ := norm_pos_iff.mpr (ClassicalFacts.DeltaFun_ne_zero τ)
  have hDlow : 1 / (8 * C2 * tpar τ ^ 2) ≤ ‖jInvariantFun τ‖ := by
    rw [jInvariantFun, norm_div, norm_pow]
    have h_inv : 1 / (C2 * tpar τ ^ 2) ≤ 1 / ‖DeltaFun τ‖ :=
      one_div_le_one_div_of_le hΔpos hb
    have h8 : 1 / (8 * C2 * tpar τ ^ 2) = 1 / 8 * (1 / (C2 * tpar τ ^ 2)) := by field_simp
    rw [h8]
    have hcad : (0 : ℝ) ≤ 1 / ‖DeltaFun τ‖ := div_nonneg zero_le_one hΔpos.le
    have step1 : 1 / 8 * (1 / (C2 * tpar τ ^ 2)) ≤ 1 / 8 * (1 / ‖DeltaFun τ‖) :=
      mul_le_mul_of_nonneg_left h_inv (by norm_num)
    have step2 : (1 / 8 : ℝ) * (1 / ‖DeltaFun τ‖) ≤ ‖E4Fun τ‖ ^ 3 * (1 / ‖DeltaFun τ‖) :=
      mul_le_mul_of_nonneg_right hE4low hcad
    have step3 : ‖E4Fun τ‖ ^ 3 * (1 / ‖DeltaFun τ‖) = ‖E4Fun τ‖ ^ 3 / ‖DeltaFun τ‖ := by
      rw [div_eq_mul_inv]
      ring
    linarith [step1, step2, step3]
  have hbig : 2 * M ≤ 1 / (8 * C2 * tpar τ ^ 2) := by
    have h6' : 16 * C2 * M * tpar τ ^ 2 ≤ 1 := by
      have h7' : 16 * C2 * M * tpar τ ^ 2 ≤ 16 * C2 * M * tpar τ :=
        mul_le_mul_of_nonneg_left htsq (by positivity)
      linarith
    rw [show (8 : ℝ) * C2 * tpar τ ^ 2 = 8 * (C2 * tpar τ ^ 2) by ring]
    rw [le_div_iff₀ (mul_pos (by norm_num) (mul_pos hC2 (pow_pos htpos 2)))]
    nlinarith [h6']
  have hj : (1 / 2 : ℝ) * (1 / (8 * C2 * tpar τ ^ 2))
      ≤ ‖jInvariantFun τ - jInvariantFun z‖ := by
    have hsplit : ‖jInvariantFun τ‖ - ‖jInvariantFun z‖
        ≤ ‖jInvariantFun τ - jInvariantFun z‖ := by
      have h := abs_norm_sub_norm_le (jInvariantFun τ) (jInvariantFun z)
      linarith [(abs_le.mp h).2]
    have hMz' : M ≤ (1 / 2 : ℝ) * (1 / (8 * C2 * tpar τ ^ 2)) := by linarith [hbig]
    linarith
  have hkpre : ‖kpre z τ‖
      = 2 * 1728 * Real.pi * ‖DeltaFun z‖ * ‖jInvariantFun τ - jInvariantFun z‖ := by
    rw [kpre, show c1728 = (1728 : ℂ) from rfl]
    simp only [norm_mul, norm_div, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  have hcpos : (0 : ℝ) < 2 * 1728 * Real.pi * ‖DeltaFun z‖ := by positivity
  have ht2pos : (0 : ℝ) < tpar τ ^ 2 := by nlinarith [htpos]
  have hdenpos : (0 : ℝ) < 8 * C2 * tpar τ ^ 2 := by nlinarith [hC2, ht2pos]
  have hfacpos : (0 : ℝ) < 1 / 2 * (1 / (8 * C2 * tpar τ ^ 2)) := by
    have h1 : (0 : ℝ) < 1 / (8 * C2 * tpar τ ^ 2) := div_pos one_pos hdenpos
    nlinarith [h1]
  have hlow := mul_le_mul_of_nonneg_left hj hcpos.le
  have hjpos : 0 < ‖jInvariantFun τ - jInvariantFun z‖ := lt_of_lt_of_le hfacpos hj
  have hinv : (2 * 1728 * Real.pi * ‖DeltaFun z‖ * ‖jInvariantFun τ - jInvariantFun z‖)⁻¹
      ≤ (2 * 1728 * Real.pi * ‖DeltaFun z‖ * (1 / 2 * (1 / (8 * C2 * tpar τ ^ 2))))⁻¹ :=
    (inv_le_inv₀ (mul_pos hcpos hjpos) (mul_pos hcpos hfacpos)).mpr hlow
  have hval : (2 * 1728 * Real.pi * ‖DeltaFun z‖ * (1 / 2 * (1 / (8 * C2 * tpar τ ^ 2))))⁻¹
      = 8 * C2 / (1728 * Real.pi * ‖DeltaFun z‖) * tpar τ ^ 2 := by
    field_simp
  rw [norm_inv, hkpre]
  rw [hval] at hinv
  refine le_trans hinv ?_
  have := pow_nonneg ht0 2
  nlinarith [this]

end

end Work.Residues
