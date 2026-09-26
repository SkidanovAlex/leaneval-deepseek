/-
# Atoms for the weighted bound calculus `SBs`

This file collects the elementary `SBs`-atoms: conversions from `SB` (plain polynomial bounds)
and from `Work.Asymptotics.IsBigOq` / `Work.Residues.CuspBound` (polynomial times a power of
the cusp parameter), together with the two "exponentially weighted" atoms `Δ(ζ)⁻¹` and
`j(τ)` (exponent `-2`), and the bounded pairing factors `kph`, `kpre⁻¹`.
-/
import Mathlib
import Submission.Work.Asymptotics.SpikeCircle.SBs
import Submission.Work.Residues.KPlusAux

noncomputable section
open UpperHalfPlane
open scoped Topology

namespace Work.Asymptotics.SpikeCircle

set_option maxHeartbeats 1000000

open Work.Kernels

/-! ## Elementary auxiliary facts -/

lemma one_add_norm_le_scale (τ : ℍ) : 1 + ‖(τ : ℂ)‖ ≤ scale τ := by
  rw [scale_eq]
  have h := inv_nonneg.mpr τ.im_pos.le
  linarith

/-- `(tpar w)^{-2} = e^{2π Im w}`. -/
lemma tpar_neg_two (w : ℍ) :
    (Work.Residues.tpar w) ^ (-2 : ℝ) = Real.exp (2 * Real.pi * w.im) := by
  rw [Work.Residues.tpar]
  rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg (Real.exp_pos _).le,
    ← Real.exp_mul, ← Real.exp_neg]
  congr 1
  ring

/-- `tpar ζ^{-2} ≤ e^{2π·29/20} tpar τ^{-2}` on the spike circle. -/
lemma tpar_neg_two_le {τ ζ : ℍ} (hζ : ‖(ζ : ℂ) - (τ : ℂ)‖ = 29 / 20) :
    (Work.Residues.tpar ζ) ^ (-2 : ℝ)
      ≤ Real.exp (2 * Real.pi * (29 / 20)) * (Work.Residues.tpar τ) ^ (-2 : ℝ) := by
  rw [tpar_neg_two ζ, tpar_neg_two τ, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := Complex.abs_im_le_norm ((ζ : ℂ) - (τ : ℂ))
  rw [Complex.sub_im, UpperHalfPlane.coe_im, UpperHalfPlane.coe_im, hζ] at h
  have h2 := (abs_le.mp h).2
  nlinarith [Real.pi_pos]

/-! ## Conversions -/

/-- `IsBigOq f n` (i.e. `f = O(q^n)`) gives the `SBs`-bound with exponent `2n`. -/
lemma SBs.of_isBigOq {H : ℝ} (hH : 1 ≤ H) {f : ℍ → ℂ} {n : ℕ} (h : IsBigOq f n) :
    SBs H (2 * n) (fun τ _ => f τ) := by
  obtain ⟨C, hC, hb⟩ := h
  refine ⟨C, 0, hC, le_refl 0, fun τ ζ hτ hζ hH' => ?_⟩
  rw [Real.rpow_zero, mul_one]
  refine le_trans (hb τ (le_trans hH hH')) ?_
  have hq : ‖Work.Kernels.qParamFun τ‖ ^ n = (Work.Residues.tpar τ) ^ (2 * (n : ℝ)) := by
    rw [Work.Asymptotics.norm_qParamFun, ← Real.exp_nat_mul, Work.Residues.tpar]
    rw [show (2 : ℝ) * (n : ℝ) = ((2 * n : ℕ) : ℝ) by push_cast; ring, ← Real.exp_mul]
    congr 1
    push_cast
    ring
  rw [hq]

/-- A `CuspBound f m k` gives an `SBs`-bound with exponent `k`. -/
lemma SBs.of_cuspBound {H : ℝ} {f : ℍ → ℂ} {m k : ℕ} (h : Work.Residues.CuspBound f m k) :
    ∃ H' : ℝ, SBs H' (k : ℝ) (fun τ _ => f τ) := by
  obtain ⟨H0, C, hC, hb⟩ := h
  refine ⟨max H0 H, C, (m : ℝ), hC, Nat.cast_nonneg m, fun τ ζ hτ hζ hH' => ?_⟩
  have hb'' : ‖f τ‖ ≤ C * (1 + ‖(τ : ℂ)‖) ^ ((m : ℕ) : ℝ)
      * (Work.Residues.tpar τ) ^ ((k : ℕ) : ℝ) := by
    rw [Real.rpow_natCast (1 + ‖(τ : ℂ)‖) m, Real.rpow_natCast (Work.Residues.tpar τ) k]
    exact hb τ (le_trans (le_max_left _ _) hH')
  have h2 : (1 + ‖(τ : ℂ)‖) ^ ((m : ℕ) : ℝ) ≤ (scale τ) ^ (m : ℝ) :=
    Real.rpow_le_rpow (by positivity) (one_add_norm_le_scale τ) (Nat.cast_nonneg m)
  exact le_trans hb'' (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hC.le)
    (Real.rpow_nonneg (Work.Residues.tpar_nonneg τ) ((k : ℕ) : ℝ)))

/-! ## `ζ`-atoms -/

lemma SBs_zeta_sq {H : ℝ} (hH : 3 ≤ H) : SBs H 0 (fun _ ζ => (ζ : ℂ) ^ 2) :=
  SBs.of_SB SB_zeta_sq hH

lemma SBs_E4_zeta {H : ℝ} (hH : 3 ≤ H) : SBs H 0 (fun _ ζ => E4Fun ζ) :=
  SBs.of_SB SBz_E4 hH

lemma SBs_E6_zeta {H : ℝ} (hH : 3 ≤ H) : SBs H 0 (fun _ ζ => E6Fun ζ) :=
  SBs.of_SB SBz_E6 hH

lemma SBs_E8_zeta {H : ℝ} (hH : 3 ≤ H) : SBs H 0 (fun _ ζ => E8Fun ζ) :=
  SBs.of_SB SBz_E8 hH

lemma SBs_E10_zeta {H : ℝ} (hH : 3 ≤ H) : SBs H 0 (fun _ ζ => E10Fun ζ) :=
  SBs.of_SB SBz_E10 hH

lemma SBs_E14_zeta {H : ℝ} (hH : 3 ≤ H) : SBs H 0 (fun _ ζ => E14Fun ζ) :=
  SBs.of_SB SBz_E14 hH

lemma SBs_E2S_zeta {H : ℝ} (hH : 3 ≤ H) : SBs H 0 (fun _ ζ => E2S ζ) :=
  SBs.of_SB SBz_E2S hH

lemma SBs_U_zeta {H : ℝ} (hH : 3 ≤ H) : SBs H 0 (fun _ ζ => UFun ζ) :=
  SBs.of_SB SBz_U hH

lemma SBs_V_zeta {H : ℝ} (hH : 3 ≤ H) : SBs H 0 (fun _ ζ => VFun ζ) :=
  SBs.of_SB SBz_V hH

lemma SBs_W_zeta {H : ℝ} (hH : 3 ≤ H) : SBs H 0 (fun _ ζ => WFun ζ) :=
  SBs.of_SB SBz_W hH

lemma SBs_L_zeta (ℓ : LogLambdaData) {H : ℝ} (hH : 3 ≤ H) :
    SBs H 0 (fun _ ζ => ℓ.L ζ) :=
  SBs.of_SB (SB_L_zeta ℓ) hH

lemma SBs_phit0 {H : ℝ} (hH : 3 ≤ H) : SBs H 0 (fun _ ζ => phitVec ζ 0) :=
  SBs.congr (SBs_zeta_sq hH) (fun τ ζ => rfl)

lemma SBs_phit1 {H : ℝ} (hH : 3 ≤ H) : SBs H 0 (fun _ ζ => phitVec ζ 1) :=
  SBs.congr ((SBs.mul (SBs_zeta_sq hH) (SBs_E2S_zeta hH)).mono (by norm_num))
    (fun τ ζ => rfl)

lemma SBs_phit2 {H : ℝ} (hH : 3 ≤ H) : SBs H 0 (fun _ ζ => phitVec ζ 2) := by
  refine SBs.congr ((SBs.mul (SBs_zeta_sq hH)
    (SBs.mul (SBs_E2S_zeta hH) (SBs_E2S_zeta hH))).mono (by norm_num)) (fun τ ζ => ?_)
  show (ζ : ℂ) ^ 2 * (E2S ζ * E2S ζ) = phitVec ζ 2
  rw [phitVec]
  simp only [Matrix.cons_val_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.tail_cons, Pi.mul_apply, Pi.pow_apply]
  ring

/-! ## `τ`-atoms -/

lemma SBs_tau_at {H : ℝ} (hH : 3 ≤ H) : SBs H 0 (fun τ _ => (τ : ℂ)) :=
  SBs.of_SB SB_tau hH

lemma SBs_E2_tau {H : ℝ} (hH : 3 ≤ H) : SBs H 0 (fun τ _ => E2Fun τ) :=
  SBs.of_SB SB_E2_tau hH

lemma SBs_E4_tau {H : ℝ} (hH : 3 ≤ H) : SBs H 0 (fun τ _ => E4Fun τ) :=
  SBs.of_SB SB_E4_tau hH

lemma SBs_E6_tau {H : ℝ} (hH : 3 ≤ H) : SBs H 0 (fun τ _ => E6Fun τ) :=
  SBs.of_SB SB_E6_tau hH

lemma SBs_E10_tau {H : ℝ} (hH : 3 ≤ H) : SBs H 0 (fun τ _ => E10Fun τ) :=
  SBs.of_SB SB_E10_tau hH

lemma SBs_E14_tau {H : ℝ} (hH : 3 ≤ H) : SBs H 0 (fun τ _ => E14Fun τ) :=
  SBs.of_SB SB_E14_tau hH

lemma SBs_phi0_tau {H : ℝ} (hH : 3 ≤ H) : SBs H 0 (fun τ _ => phi0 τ) :=
  SBs.of_SB SB_phi0_tau hH

lemma SBs_psi2_tau (ℓ : LogLambdaData) {H : ℝ} (hH : 3 ≤ H) :
    SBs H 0 (fun τ _ => psi2 ℓ τ) :=
  SBs.of_SB (SB_psi2_tau ℓ) hH

lemma SBs_psi4_tau (ℓ : LogLambdaData) {H : ℝ} (hH : 3 ≤ H) :
    SBs H 0 (fun τ _ => psi4 ℓ τ) :=
  SBs.of_SB (SB_psi4_tau ℓ) hH

lemma SBs_E4_tau_sq {H : ℝ} (hH : 3 ≤ H) : SBs H 0 (fun τ _ => E4Fun τ ^ 2) :=
  SBs.congr ((SBs.mul (SBs_E4_tau hH) (SBs_E4_tau hH)).mono (by norm_num))
    (fun τ ζ => by ring)

lemma SBs_E4_tau_cube {H : ℝ} (hH : 3 ≤ H) : SBs H 0 (fun τ _ => E4Fun τ ^ 3) :=
  SBs.congr ((SBs.mul (SBs_E4_tau_sq hH) (SBs_E4_tau hH)).mono (by norm_num))
    (fun τ ζ => by ring)

/-! ## Smallness of `E₄ - E₂²` and `E₄² - E₆E₂` -/

lemma SBs_delta1 {H : ℝ} (hH : 1 ≤ H) :
    SBs H 2 (fun τ _ => E4Fun τ - E2Fun τ ^ 2) :=
  (SBs.of_isBigOq hH Work.Asymptotics.delta1_isBigOq).mono (by norm_num)

lemma SBs_eps {H : ℝ} (hH : 1 ≤ H) :
    SBs H 2 (fun τ _ => E4Fun τ ^ 2 - E6Fun τ * E2Fun τ) :=
  (SBs.of_isBigOq hH Work.Asymptotics.eps_isBigOq).mono (by norm_num)

lemma SBs_Delta_tau {H : ℝ} (hH : 1 ≤ H) : SBs H 2 (fun τ _ => DeltaFun τ) :=
  (SBs.of_isBigOq hH Work.Asymptotics.DeltaFun_isBigOq_one).mono (by norm_num)

/-- `Qf (E₄ τ) (E₆ τ) = 1728 Δ τ`. -/
lemma SBs_Qf {H : ℝ} (hH : 1 ≤ H) :
    SBs H 2 (fun τ _ => Work.Residues.KPlusAux.Qf (E4Fun τ) (E6Fun τ)) := by
  refine SBs.congr (SBs.const_mul (1728 : ℂ) (SBs_Delta_tau hH)) (fun τ ζ => ?_)
  rw [Work.Residues.KPlusAux.Qf]
  exact Work.Residues.KPlusAux.DeltaFun_eq_E4_cube_sub_E6_sq τ

/-! ## The exponentially weighted atoms -/

lemma SBs_inv_Delta_zeta {H : ℝ} (hH : 3 ≤ H) :
    SBs H (-2) (fun _ ζ => (DeltaFun ζ)⁻¹) := by
  obtain ⟨c, _C, hc, _hC, hΔ⟩ := DeltaFunBoundsHalf
  refine ⟨(1 / c) * Real.exp (2 * Real.pi * (29 / 20)) + 1, 0, by positivity, le_refl 0,
    fun τ ζ hτ hζ hH' => ?_⟩
  rw [Real.rpow_zero, mul_one]
  have hzim : 1 / 2 ≤ ζ.im := by
    have := one_le_zeta_im hζ (le_trans hH hH'); linarith
  have h1 : c * Real.exp (-(2 * Real.pi * ζ.im)) ≤ ‖DeltaFun ζ‖ := (hΔ ζ hzim).1
  have hpos : 0 < c * Real.exp (-(2 * Real.pi * ζ.im)) := by positivity
  have h4 : (‖DeltaFun ζ‖)⁻¹ ≤ (c * Real.exp (-(2 * Real.pi * ζ.im)))⁻¹ :=
    (inv_le_inv₀ (lt_of_lt_of_le hpos h1) hpos).mpr h1
  have hexp : (c * Real.exp (-(2 * Real.pi * ζ.im)))⁻¹
      = (1 / c) * (Work.Residues.tpar ζ) ^ (-2 : ℝ) := by
    rw [tpar_neg_two ζ, mul_inv, one_div, Real.exp_neg, inv_inv]
  have ht := tpar_neg_two_le hζ
  have h0 : (0 : ℝ) ≤ (Work.Residues.tpar τ) ^ (-2 : ℝ) :=
    Real.rpow_nonneg (Work.Residues.tpar_nonneg τ) _
  calc ‖(DeltaFun ζ)⁻¹‖ = (‖DeltaFun ζ‖)⁻¹ := norm_inv _
    _ ≤ (c * Real.exp (-(2 * Real.pi * ζ.im)))⁻¹ := h4
    _ = (1 / c) * (Work.Residues.tpar ζ) ^ (-2 : ℝ) := hexp
    _ ≤ (1 / c) * (Real.exp (2 * Real.pi * (29 / 20))
          * (Work.Residues.tpar τ) ^ (-2 : ℝ)) :=
        mul_le_mul_of_nonneg_left ht (by positivity)
    _ = (1 / c) * Real.exp (2 * Real.pi * (29 / 20)) * (Work.Residues.tpar τ) ^ (-2 : ℝ) := by
        ring
    _ ≤ ((1 / c) * Real.exp (2 * Real.pi * (29 / 20)) + 1)
          * (Work.Residues.tpar τ) ^ (-2 : ℝ) :=
        mul_le_mul_of_nonneg_right (by linarith) h0

lemma SBs_j_tau {H : ℝ} (hH : 1 ≤ H) : SBs H (-2) (fun τ _ => jInvariantFun τ) := by
  obtain ⟨C, hC, hb⟩ := jInvariantFun_strip_bound
  refine ⟨C, 0, hC, le_refl 0, fun τ ζ hτ hζ hH' => ?_⟩
  rw [Real.rpow_zero, mul_one]
  refine le_trans (hb τ (le_trans (by norm_num) (le_trans hH hH'))) ?_
  rw [tpar_neg_two τ]

lemma SBs_kph {H : ℝ} (hH : 3 ≤ H) :
    SBs H 0 (fun τ ζ => Work.Residues.KPlusAux.kph τ ζ) :=
  SBs.of_SB SB_inv_DeltaTauJ hH

lemma SBs_inv_kpre (ℓ : LogLambdaData) {H : ℝ} (hH : 3 ≤ H) :
    SBs H 0 (fun τ ζ => (Work.Residues.kpre ζ τ)⁻¹) := by
  refine SBs.of_SB ?_ hH
  refine SB.congr (SB.const_mul ((2 * (1728 : ℂ) * (Real.pi : ℂ))⁻¹) SB_inv_DeltaZetaJ)
    (fun τ ζ => ?_)
  simp only [Work.Residues.kpre, c1728, mul_inv]
  ring

end Work.Asymptotics.SpikeCircle
