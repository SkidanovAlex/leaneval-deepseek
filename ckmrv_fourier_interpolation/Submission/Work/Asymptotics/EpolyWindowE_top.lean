/-
# The polynomial window on the cusp-`0` tile `E`: the top regime

`Work.Asymptotics.EpolyWindowE_top` is the regime `Im (S • w) + 1 ≤ t ≤ scale w` of the
polynomial window bound on the cusp-`0` tile `E = KEpsilon` of the CKMRV paper.

The proof splits

  `‖K(w,it)‖ ≤ ‖K(w,it) - Aexp (Gcusp ℓ d) w t‖ + ‖Aexp (Gcusp ℓ d) w t‖`.

* The first term is controlled by the (sorry-free) cusp-`i∞` expansion
  `Work.Asymptotics.E_deviation_sharp`, whose exponential factor `e^{-π(t - Im (S•w))}` is `≤ 1`
  on this regime.
* The second term is polynomial because the `e^{2πt}` row of the cusp coefficients is
  exponentially small on `E`:
  `‖Gcusp ℓ d 1 j w‖ ≤ C (scale w)^N e^{-2π Im (S • w)}` (a consequence of the *funnel*
  sharpness `Work.Asymptotics.Gcusp_one_exp_small_funnel` transported by the Fricke laws
  `Work.Asymptotics.Gcusp24_10_S_smul` / `Gcusp24_11_S_smul`), while
  `t ≤ scale w ≤ Im (S • w) + 2` (`Work.Asymptotics.E_scale_le_im_S_add_two`).
-/
import Mathlib
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Asymptotics.EBase
import Submission.Work.Asymptotics.EWindowAux
import Submission.Work.Asymptotics.Gcusp_one_exp_small_funnel
import Submission.Work.Asymptotics.Gcusp24_S_smul
import Submission.Work.Asymptotics.Funnel24Aux
import Submission.Work.Asymptotics.DeltaFun_upper_sharp
import Submission.Work.Asymptotics.DeltaFun_funnel_lower_sharp
import Submission.Work.Asymptotics.E_aux

noncomputable section

open UpperHalfPlane ModularGroup
open scoped MatrixGroups UpperHalfPlane

namespace Work.Asymptotics

/-! ## Elementary arithmetic -/

private lemma mul_rpow_add_one {s : ℝ} (hs : 0 < s) (b : ℝ) :
    s * s ^ b = s ^ (b + 1) := by
  have h := Real.rpow_add hs (1 : ℝ) b
  rw [Real.rpow_one] at h
  rw [← h, show (1 : ℝ) + b = b + 1 by ring]

private lemma coe_pow_le_scale_pow (σ : ℍ) (n : ℕ) :
    ‖(σ : ℂ)‖ ^ n ≤ (Work.Kernels.scale σ) ^ n :=
  pow_le_pow_left₀ (norm_nonneg _) (Work.Kernels.coe_norm_le_scale σ) n

/-- `scale (S • w) ≤ 3 * scale w` on the cusp-`0` tile `E`. -/
lemma scale_S_smul_le_of_mem_KEpsilon {w : UpperHalfPlane} (hw : w ∈ KEpsilon) :
    Work.Kernels.scale (ModularGroup.S • w) ≤ 3 * Work.Kernels.scale w := by
  have him : 2 * ‖(w : ℂ)‖ ^ 2 ≤ w.im := by
    have hS : 2 ≤ (ModularGroup.S • w).im := hw.2
    rw [E_S_im] at hS
    have hn : 0 < ‖(w : ℂ)‖ ^ 2 := pow_pos (E_norm_pos w) 2
    rw [le_div_iff₀ hn] at hS
    linarith
  have h1 : Work.Kernels.scale (ModularGroup.S • w)
      = 1 + ‖(w : ℂ)‖ ^ 2 / w.im + (‖(w : ℂ)‖)⁻¹ := by
    rw [Work.Kernels.scale, E_S_im, inv_div, Epoly_norm_S_smul]
  have h2 : ‖(w : ℂ)‖ ^ 2 / w.im ≤ 1 / 2 := by
    rw [div_le_iff₀ w.im_pos]; linarith
  have h3 : (‖(w : ℂ)‖)⁻¹ ≤ w.im⁻¹ :=
    inv_anti₀ w.im_pos (Work.Kernels.im_le_coe_norm w)
  have h4 : w.im⁻¹ ≤ Work.Kernels.scale w := Work.Kernels.inv_im_le_scale w
  have h5 : (1 : ℝ) ≤ Work.Kernels.scale w := Work.Kernels.one_le_scale w
  rw [h1]
  linarith

/-! ## Sharpness of the `e^{2πt}` row of the cusp coefficients on `E` -/

/-- The `(i,j) = (1,1)` row of the `d = 24` cusp coefficients after `S`-transport. -/
private lemma Gcusp24_row11_S_decay (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ σ : ℍ, Funnel σ →
      ‖Gcusp24 ℓ 1 1 (ModularGroup.S • σ)‖
        ≤ C * (Work.Kernels.scale σ) ^ N * Real.exp (-(2 * Real.pi * σ.im)) := by
  obtain ⟨CG, NG, hCG, hNG, hG⟩ := Gcusp_one_exp_small_funnel ℓ 24 (Or.inr rfl)
  have hG24 : ∀ (τ : ℍ), Funnel τ → ‖Gcusp24 ℓ 1 1 τ‖
      ≤ CG * (Work.Kernels.scale τ) ^ NG * Real.exp (-(2 * Real.pi * τ.im)) := by
    intro τ hτ
    have h := hG τ 1 hτ
    rwa [show Gcusp ℓ 24 = Gcusp24 ℓ from by
      ext i j τ
      simp only [Gcusp, if_neg (by norm_num : (24 : ℕ) ≠ 8)]] at h
  refine ⟨CG + 2, NG + 12, by linarith, by linarith, fun σ hσ => ?_⟩
  have hs1 : (1 : ℝ) ≤ Work.Kernels.scale σ := Work.Kernels.one_le_scale σ
  have hs0 : (0 : ℝ) ≤ Work.Kernels.scale σ := le_trans zero_le_one hs1
  have hspos : 0 < Work.Kernels.scale σ := Work.Kernels.scale_pos σ
  have he0 : (0 : ℝ) ≤ Real.exp (-(2 * Real.pi * σ.im)) := (Real.exp_pos _).le
  have hDb : ‖Work.Kernels.DeltaFun σ‖ ≤ 2 * Real.exp (-(2 * Real.pi * σ.im)) := by
    have h := DeltaFun_funnel_le σ hσ
    rwa [norm_qParamFun] at h
  have hbr : ‖Gcusp24 ℓ 1 1 σ - Complex.I * Work.Kernels.DeltaFun σ‖
      ≤ CG * (Work.Kernels.scale σ) ^ NG * Real.exp (-(2 * Real.pi * σ.im))
        + 2 * Real.exp (-(2 * Real.pi * σ.im)) := by
    refine le_trans (norm_sub_le _ _) ?_
    rw [norm_mul, Complex.norm_I, one_mul]
    exact add_le_add (hG24 σ hσ) hDb
  have hspow : (Work.Kernels.scale σ) ^ 12 * (Work.Kernels.scale σ) ^ NG
      = (Work.Kernels.scale σ) ^ (NG + 12) := by
    rw [← Real.rpow_natCast (Work.Kernels.scale σ) 12, ← Real.rpow_add hspos]
    congr 1
    ring
  have hle12 : (Work.Kernels.scale σ) ^ 12 ≤ (Work.Kernels.scale σ) ^ (NG + 12) := by
    rw [← Real.rpow_natCast (Work.Kernels.scale σ) 12]
    exact Real.rpow_le_rpow_of_exponent_le hs1 (by linarith : ((12 : ℝ)) ≤ NG + 12)
  have hstep : 2 * ((Work.Kernels.scale σ) ^ 12 * Real.exp (-(2 * Real.pi * σ.im)))
      ≤ 2 * ((Work.Kernels.scale σ) ^ (NG + 12) * Real.exp (-(2 * Real.pi * σ.im))) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hle12 he0) (by norm_num)
  have hmain : ‖(σ : ℂ)‖ ^ 12 * ‖Gcusp24 ℓ 1 1 σ - Complex.I * Work.Kernels.DeltaFun σ‖
      ≤ (CG + 2) * (Work.Kernels.scale σ) ^ (NG + 12)
          * Real.exp (-(2 * Real.pi * σ.im)) := by
    refine le_trans (mul_le_mul (coe_pow_le_scale_pow σ 12) hbr (norm_nonneg _)
      (pow_nonneg hs0 12)) ?_
    calc (Work.Kernels.scale σ) ^ 12
          * (CG * (Work.Kernels.scale σ) ^ NG * Real.exp (-(2 * Real.pi * σ.im))
              + 2 * Real.exp (-(2 * Real.pi * σ.im)))
        = CG * ((Work.Kernels.scale σ) ^ 12 * (Work.Kernels.scale σ) ^ NG)
            * Real.exp (-(2 * Real.pi * σ.im))
          + 2 * ((Work.Kernels.scale σ) ^ 12 * Real.exp (-(2 * Real.pi * σ.im))) := by ring
      _ = CG * (Work.Kernels.scale σ) ^ (NG + 12) * Real.exp (-(2 * Real.pi * σ.im))
          + 2 * ((Work.Kernels.scale σ) ^ 12 * Real.exp (-(2 * Real.pi * σ.im))) := by
            rw [hspow]
      _ ≤ CG * (Work.Kernels.scale σ) ^ (NG + 12) * Real.exp (-(2 * Real.pi * σ.im))
          + 2 * ((Work.Kernels.scale σ) ^ (NG + 12) * Real.exp (-(2 * Real.pi * σ.im))) := by
            linarith [hstep]
      _ = (CG + 2) * (Work.Kernels.scale σ) ^ (NG + 12)
            * Real.exp (-(2 * Real.pi * σ.im)) := by ring
  rw [Gcusp24_11_S_smul ℓ σ, norm_mul, norm_neg, norm_pow]
  exact hmain

/-- The `(i,j) = (1,0)` row of the `d = 24` cusp coefficients after `S`-transport. -/
private lemma Gcusp24_row10_S_decay (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ σ : ℍ, Funnel σ →
      ‖Gcusp24 ℓ 1 0 (ModularGroup.S • σ)‖
        ≤ C * (Work.Kernels.scale σ) ^ N * Real.exp (-(2 * Real.pi * σ.im)) := by
  obtain ⟨CG, NG, hCG, hNG, hG⟩ := Gcusp_one_exp_small_funnel ℓ 24 (Or.inr rfl)
  obtain ⟨CP, NP, hCP, hNP, hP⟩ := psi4E8_sub_psi2E10_funnel ℓ
  have hG24 : ∀ (τ : ℍ), Funnel τ → ‖Gcusp24 ℓ 1 0 τ‖
      ≤ CG * (Work.Kernels.scale τ) ^ NG * Real.exp (-(2 * Real.pi * τ.im)) := by
    intro τ hτ
    have h := hG τ 0 hτ
    rwa [show Gcusp ℓ 24 = Gcusp24 ℓ from by
      ext i j τ
      simp only [Gcusp, if_neg (by norm_num : (24 : ℕ) ≠ 8)]] at h
  have hCpos : 0 < CG + CP + 2 * ‖cuspL ℓ - 1‖ / Real.pi := by
    have h2 : 0 ≤ 2 * ‖cuspL ℓ - 1‖ / Real.pi := by positivity
    linarith
  have hN0 : 0 ≤ max NG NP + 12 := by
    have h1 : 0 ≤ max NG NP := le_trans hNG (le_max_left _ _)
    linarith
  refine ⟨CG + CP + 2 * ‖cuspL ℓ - 1‖ / Real.pi, max NG NP + 12, hCpos, hN0,
    fun σ hσ => ?_⟩
  have hs1 : (1 : ℝ) ≤ Work.Kernels.scale σ := Work.Kernels.one_le_scale σ
  have hs0 : (0 : ℝ) ≤ Work.Kernels.scale σ := le_trans zero_le_one hs1
  have hN0' : 0 ≤ max NG NP := le_trans hNG (le_max_left _ _)
  have hNGle : NG ≤ max NG NP := le_max_left _ _
  have hNPle : NP ≤ max NG NP := le_max_right _ _
  have hsNG : (Work.Kernels.scale σ) ^ NG ≤ (Work.Kernels.scale σ) ^ (max NG NP) :=
    Real.rpow_le_rpow_of_exponent_le hs1 hNGle
  have hsNP : (Work.Kernels.scale σ) ^ NP ≤ (Work.Kernels.scale σ) ^ (max NG NP) :=
    Real.rpow_le_rpow_of_exponent_le hs1 hNPle
  have hone : (1 : ℝ) ≤ (Work.Kernels.scale σ) ^ (max NG NP) := Real.one_le_rpow hs1 hN0'
  have he0 : (0 : ℝ) ≤ Real.exp (-(2 * Real.pi * σ.im)) := (Real.exp_pos _).le
  have hGb : ‖Gcusp24 ℓ 1 0 σ‖
      ≤ CG * (Work.Kernels.scale σ) ^ NG * Real.exp (-(2 * Real.pi * σ.im)) := hG24 σ hσ
  have hPb : ‖Work.Kernels.psi2 ℓ σ * Work.Kernels.E10Fun σ
      - Work.Kernels.psi4 ℓ σ * Work.Kernels.E8Fun σ‖
      ≤ CP * (Work.Kernels.scale σ) ^ NP * Real.exp (-(2 * Real.pi * σ.im)) := by
    have h := hP σ hσ
    rw [norm_qParamFun] at h
    rwa [norm_sub_rev] at h
  have hDb : ‖Work.Kernels.DeltaFun σ‖ ≤ 2 * Real.exp (-(2 * Real.pi * σ.im)) := by
    have h := DeltaFun_funnel_le σ hσ
    rwa [norm_qParamFun] at h
  -- the bracket
  have hb1 : ‖-(Gcusp24 ℓ 1 0 σ)‖
      ≤ CG * (Work.Kernels.scale σ) ^ (max NG NP) * Real.exp (-(2 * Real.pi * σ.im)) := by
    rw [norm_neg]
    exact le_trans hGb (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsNG hCG.le) he0)
  have hb2 : ‖(Work.Kernels.psi2 ℓ σ * Work.Kernels.E10Fun σ
        - Work.Kernels.psi4 ℓ σ * Work.Kernels.E8Fun σ) / (1152 * (Real.pi : ℂ))‖
      ≤ CP * (Work.Kernels.scale σ) ^ (max NG NP) * Real.exp (-(2 * Real.pi * σ.im)) := by
    have hD : (1 : ℝ) ≤ ‖((1152 : ℂ) * (Real.pi : ℂ))‖ := by
      rw [norm_mul]
      have h1152 : ‖(1152 : ℂ)‖ = 1152 := by norm_num
      rw [h1152, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      nlinarith [Real.pi_gt_three]
    rw [norm_div]
    refine le_trans (div_le_div_of_nonneg_left (norm_nonneg _) zero_lt_one hD) ?_
    rw [div_one]
    exact le_trans hPb (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsNP hCP.le) he0)
  have hb3 : ‖(cuspL ℓ - 1) * Work.Kernels.DeltaFun σ / (Real.pi : ℂ)‖
      ≤ (2 * ‖cuspL ℓ - 1‖ / Real.pi) * (Work.Kernels.scale σ) ^ (max NG NP)
          * Real.exp (-(2 * Real.pi * σ.im)) := by
    have hπ : ‖(Real.pi : ℂ)‖ = Real.pi := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    have hnum : ‖(cuspL ℓ - 1) * Work.Kernels.DeltaFun σ‖
        ≤ 2 * ‖cuspL ℓ - 1‖ * Real.exp (-(2 * Real.pi * σ.im)) := by
      rw [norm_mul]
      calc ‖cuspL ℓ - 1‖ * ‖Work.Kernels.DeltaFun σ‖
          ≤ ‖cuspL ℓ - 1‖ * (2 * Real.exp (-(2 * Real.pi * σ.im))) :=
            mul_le_mul_of_nonneg_left hDb (norm_nonneg _)
        _ = 2 * ‖cuspL ℓ - 1‖ * Real.exp (-(2 * Real.pi * σ.im)) := by ring
    have hcoef : (0 : ℝ) ≤ 2 * ‖cuspL ℓ - 1‖ / Real.pi := by positivity
    have step1 : ‖(cuspL ℓ - 1) * Work.Kernels.DeltaFun σ / (Real.pi : ℂ)‖
        ≤ (2 * ‖cuspL ℓ - 1‖ / Real.pi) * Real.exp (-(2 * Real.pi * σ.im)) := by
      calc ‖(cuspL ℓ - 1) * Work.Kernels.DeltaFun σ / (Real.pi : ℂ)‖
          = ‖(cuspL ℓ - 1) * Work.Kernels.DeltaFun σ‖ / Real.pi := by rw [norm_div, hπ]
        _ ≤ (2 * ‖cuspL ℓ - 1‖ * Real.exp (-(2 * Real.pi * σ.im))) / Real.pi :=
            div_le_div_of_nonneg_right hnum Real.pi_pos.le
        _ = (2 * ‖cuspL ℓ - 1‖ / Real.pi) * Real.exp (-(2 * Real.pi * σ.im)) := by ring
    refine le_trans step1 ?_
    calc (2 * ‖cuspL ℓ - 1‖ / Real.pi) * Real.exp (-(2 * Real.pi * σ.im))
        = (2 * ‖cuspL ℓ - 1‖ / Real.pi) * 1 * Real.exp (-(2 * Real.pi * σ.im)) := by ring
      _ ≤ (2 * ‖cuspL ℓ - 1‖ / Real.pi) * (Work.Kernels.scale σ) ^ (max NG NP)
            * Real.exp (-(2 * Real.pi * σ.im)) := by
          refine mul_le_mul_of_nonneg_right ?_ he0
          exact mul_le_mul_of_nonneg_left hone hcoef
  have hbr : ‖-(Gcusp24 ℓ 1 0 σ)
        + (Work.Kernels.psi2 ℓ σ * Work.Kernels.E10Fun σ
              - Work.Kernels.psi4 ℓ σ * Work.Kernels.E8Fun σ) / (1152 * (Real.pi : ℂ))
        + (cuspL ℓ - 1) * Work.Kernels.DeltaFun σ / (Real.pi : ℂ)‖
      ≤ (CG + CP + 2 * ‖cuspL ℓ - 1‖ / Real.pi) * (Work.Kernels.scale σ) ^ (max NG NP)
          * Real.exp (-(2 * Real.pi * σ.im)) := by
    refine le_trans (norm_add_le _ _) ?_
    refine le_trans (add_le_add (norm_add_le _ _) (le_refl _)) ?_
    exact le_trans (add_le_add (add_le_add hb1 hb2) hb3) (le_of_eq (by ring))
  -- multiply by `σ^12`
  have hpow : (Work.Kernels.scale σ) ^ 12 * (Work.Kernels.scale σ) ^ (max NG NP)
      = (Work.Kernels.scale σ) ^ (max NG NP + 12) := by
    rw [← Real.rpow_natCast (Work.Kernels.scale σ) 12, ← Real.rpow_add (Work.Kernels.scale_pos σ)]
    congr 1
    ring
  have hmain : ‖(σ : ℂ)‖ ^ 12
        * ‖-(Gcusp24 ℓ 1 0 σ)
            + (Work.Kernels.psi2 ℓ σ * Work.Kernels.E10Fun σ
                  - Work.Kernels.psi4 ℓ σ * Work.Kernels.E8Fun σ) / (1152 * (Real.pi : ℂ))
            + (cuspL ℓ - 1) * Work.Kernels.DeltaFun σ / (Real.pi : ℂ)‖
      ≤ (CG + CP + 2 * ‖cuspL ℓ - 1‖ / Real.pi) * (Work.Kernels.scale σ) ^ (max NG NP + 12)
          * Real.exp (-(2 * Real.pi * σ.im)) := by
    refine le_trans (mul_le_mul (coe_pow_le_scale_pow σ 12) hbr (norm_nonneg _)
      (pow_nonneg hs0 12)) ?_
    have heq : (Work.Kernels.scale σ) ^ 12
          * ((CG + CP + 2 * ‖cuspL ℓ - 1‖ / Real.pi)
              * (Work.Kernels.scale σ) ^ (max NG NP) * Real.exp (-(2 * Real.pi * σ.im)))
        = (CG + CP + 2 * ‖cuspL ℓ - 1‖ / Real.pi)
            * (Work.Kernels.scale σ) ^ (max NG NP + 12) * Real.exp (-(2 * Real.pi * σ.im)) := by
      rw [← hpow]
      ring
    exact le_of_eq heq
  rw [Gcusp24_10_S_smul ℓ σ, norm_mul, norm_pow]
  exact hmain

/-- **The `e^{2πt}`-row of the cusp coefficients is exponentially small on `E`.** -/
theorem Gcusp_row_one_small_E (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧
      ∀ (w : UpperHalfPlane), w ∈ KEpsilon → ∀ j : Fin 2,
        ‖Gcusp ℓ d 1 j w‖
          ≤ C * (Work.Kernels.scale w) ^ N
              * Real.exp (-(2 * Real.pi * (ModularGroup.S • w).im)) := by
  rcases hd with rfl | rfl
  · refine ⟨1, 0, one_pos, le_refl 0, fun w _ j => ?_⟩
    have hzero : Gcusp ℓ 8 1 j w = 0 := by simp [Gcusp, Gcusp8]
    rw [hzero, norm_zero, Real.rpow_zero]
    have : (0 : ℝ) ≤ 1 * 1 * Real.exp (-(2 * Real.pi * (ModularGroup.S • w).im)) := by positivity
    linarith
  · obtain ⟨C0, N0, hC0, hN0, hb0⟩ := Gcusp24_row10_S_decay ℓ
    obtain ⟨C1, N1, hC1, hN1, hb1⟩ := Gcusp24_row11_S_decay ℓ
    refine ⟨max C0 C1 * 3 ^ (max N0 N1), max N0 N1,
      mul_pos (lt_of_lt_of_le hC0 (le_max_left _ _)) (Real.rpow_pos_of_pos (by norm_num) _),
      le_trans hN0 (le_max_left _ _), fun w hw j => ?_⟩
    have hFN : Funnel (ModularGroup.S • w) := S_smul_mem_funnel hw
    have hσw : ModularGroup.S • (ModularGroup.S • w) = w := S_smul_S_smul w
    have hsw : Work.Kernels.scale (ModularGroup.S • w) ≤ 3 * Work.Kernels.scale w :=
      scale_S_smul_le_of_mem_KEpsilon hw
    have hs0 : (0 : ℝ) ≤ Work.Kernels.scale w :=
      le_trans zero_le_one (Work.Kernels.one_le_scale w)
    have hss1 : (1 : ℝ) ≤ Work.Kernels.scale (ModularGroup.S • w) :=
      Work.Kernels.one_le_scale _
    have hN0le : N0 ≤ max N0 N1 := le_max_left _ _
    have hN1le : N1 ≤ max N0 N1 := le_max_right _ _
    have hscale : (Work.Kernels.scale (ModularGroup.S • w)) ^ (max N0 N1)
        ≤ 3 ^ (max N0 N1) * (Work.Kernels.scale w) ^ (max N0 N1) := by
      calc (Work.Kernels.scale (ModularGroup.S • w)) ^ (max N0 N1)
          ≤ (3 * Work.Kernels.scale w) ^ (max N0 N1) :=
            Real.rpow_le_rpow (Work.Kernels.scale_pos _).le hsw
              (le_trans hN0 (le_max_left _ _))
        _ = 3 ^ (max N0 N1) * (Work.Kernels.scale w) ^ (max N0 N1) :=
            Real.mul_rpow (by norm_num) hs0
    have hssN : (Work.Kernels.scale (ModularGroup.S • w)) ^ N0
        ≤ 3 ^ (max N0 N1) * (Work.Kernels.scale w) ^ (max N0 N1) :=
      le_trans (Real.rpow_le_rpow_of_exponent_le hss1 hN0le) hscale
    have hssN1 : (Work.Kernels.scale (ModularGroup.S • w)) ^ N1
        ≤ 3 ^ (max N0 N1) * (Work.Kernels.scale w) ^ (max N0 N1) :=
      le_trans (Real.rpow_le_rpow_of_exponent_le hss1 hN1le) hscale
    have hE0 : (0 : ℝ) ≤ Real.exp (-(2 * Real.pi * (ModularGroup.S • w).im)) :=
      (Real.exp_pos _).le
    have hpre0 : C0 * (Work.Kernels.scale (ModularGroup.S • w)) ^ N0
        ≤ max C0 C1 * 3 ^ (max N0 N1) * (Work.Kernels.scale w) ^ (max N0 N1) := by
      calc C0 * (Work.Kernels.scale (ModularGroup.S • w)) ^ N0
          ≤ C0 * (3 ^ (max N0 N1) * (Work.Kernels.scale w) ^ (max N0 N1)) :=
            mul_le_mul_of_nonneg_left hssN hC0.le
        _ ≤ max C0 C1 * 3 ^ (max N0 N1) * (Work.Kernels.scale w) ^ (max N0 N1) := by
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_right (le_max_left _ _)
              (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hs0 _))
    have hpre1 : C1 * (Work.Kernels.scale (ModularGroup.S • w)) ^ N1
        ≤ max C0 C1 * 3 ^ (max N0 N1) * (Work.Kernels.scale w) ^ (max N0 N1) := by
      calc C1 * (Work.Kernels.scale (ModularGroup.S • w)) ^ N1
          ≤ C1 * (3 ^ (max N0 N1) * (Work.Kernels.scale w) ^ (max N0 N1)) :=
            mul_le_mul_of_nonneg_left hssN1 hC1.le
        _ ≤ max C0 C1 * 3 ^ (max N0 N1) * (Work.Kernels.scale w) ^ (max N0 N1) := by
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_right (le_max_right _ _)
              (mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hs0 _))
    have hmain0 : ‖Gcusp ℓ 24 1 0 w‖
        ≤ max C0 C1 * 3 ^ (max N0 N1) * (Work.Kernels.scale w) ^ (max N0 N1)
            * Real.exp (-(2 * Real.pi * (ModularGroup.S • w).im)) := by
      have hb := hb0 (ModularGroup.S • w) hFN
      rw [hσw] at hb
      rw [show Gcusp ℓ 24 = Gcusp24 ℓ from by
        ext i j τ
        simp only [Gcusp, if_neg (by norm_num : (24 : ℕ) ≠ 8)]]
      exact le_trans hb (mul_le_mul_of_nonneg_right hpre0 hE0)
    have hmain1 : ‖Gcusp ℓ 24 1 1 w‖
        ≤ max C0 C1 * 3 ^ (max N0 N1) * (Work.Kernels.scale w) ^ (max N0 N1)
            * Real.exp (-(2 * Real.pi * (ModularGroup.S • w).im)) := by
      have hb := hb1 (ModularGroup.S • w) hFN
      rw [hσw] at hb
      rw [show Gcusp ℓ 24 = Gcusp24 ℓ from by
        ext i j τ
        simp only [Gcusp, if_neg (by norm_num : (24 : ℕ) ≠ 8)]]
      exact le_trans hb (mul_le_mul_of_nonneg_right hpre1 hE0)
    fin_cases j
    · exact hmain0
    · exact hmain1

/-! ## Polynomial bound on the cusp model `Aexp` in the regime `t ≤ scale w` -/

/-- **`Aexp (Gcusp ℓ d) w t` is polynomially bounded in `scale w` on the top regime.**

The `e^{2πt}` factor is cancelled by the sharp smallness of the `i = 1` row of `Gcusp` on `E`
(`Work.Asymptotics.Gcusp_row_one_small_E`), while `t ≤ scale w ≤ Im (S•w) + 2`. -/
theorem Aexp_poly_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧
      ∀ (w : ℍ) (t : ℝ), w ∈ KEpsilon → (ModularGroup.S • w).im + 1 ≤ t →
        t ≤ Work.Kernels.scale w →
        ‖Aexp (Gcusp ℓ d) w t‖ ≤ C * (Work.Kernels.scale w) ^ N := by
  obtain ⟨A, NA, hA, hNA, hgb⟩ := gcusp_bound_E ℓ d hd
  obtain ⟨Cg, Ng, hCg, hNg, hrow⟩ := Gcusp_row_one_small_E ℓ d hd
  have hE4 : 0 < Real.exp (4 * Real.pi) := Real.exp_pos _
  refine ⟨4 * A + 4 * Cg * Real.exp (4 * Real.pi) + 1, NA + Ng + 1,
    by nlinarith [hA, hCg.le, hE4], by linarith, fun w t hw ht htle => ?_⟩
  have hT2 : (2 : ℝ) ≤ (ModularGroup.S • w).im := hw.2
  have ht0 : (0 : ℝ) < t := by linarith
  have ht0le : (0 : ℝ) ≤ t := ht0.le
  have hs1 : (1 : ℝ) ≤ Work.Kernels.scale w := Work.Kernels.one_le_scale w
  have hs0 : (0 : ℝ) ≤ Work.Kernels.scale w := le_trans zero_le_one hs1
  have htle' : t ≤ Work.Kernels.scale w := htle
  have hsT : Work.Kernels.scale w ≤ (ModularGroup.S • w).im + 2 := E_scale_le_im_S_add_two hw
  have htT : t - (ModularGroup.S • w).im ≤ 2 := by linarith
  have hTt : (ModularGroup.S • w).im ≤ t := by linarith
  have hNA_le : NA ≤ NA + Ng + 1 := by linarith
  have hNg_le : Ng ≤ NA + Ng + 1 := by linarith
  have hNA1_le : NA + 1 ≤ NA + Ng + 1 := by linarith
  have hNg1_le : Ng + 1 ≤ NA + Ng + 1 := by linarith
  have hpNA : (Work.Kernels.scale w) ^ NA ≤ (Work.Kernels.scale w) ^ (NA + Ng + 1) :=
    Real.rpow_le_rpow_of_exponent_le hs1 hNA_le
  have hpNg : (Work.Kernels.scale w) ^ Ng ≤ (Work.Kernels.scale w) ^ (NA + Ng + 1) :=
    Real.rpow_le_rpow_of_exponent_le hs1 hNg_le
  have hpNA1 : (Work.Kernels.scale w) ^ (NA + 1) ≤ (Work.Kernels.scale w) ^ (NA + Ng + 1) :=
    Real.rpow_le_rpow_of_exponent_le hs1 hNA1_le
  have hpNg1 : (Work.Kernels.scale w) ^ (Ng + 1) ≤ (Work.Kernels.scale w) ^ (NA + Ng + 1) :=
    Real.rpow_le_rpow_of_exponent_le hs1 hNg1_le
  have hsN0 : (0 : ℝ) ≤ (Work.Kernels.scale w) ^ (NA + Ng + 1) := Real.rpow_nonneg hs0 _
  have hEE0 : (0 : ℝ) ≤ Real.exp (-(2 * Real.pi * (ModularGroup.S • w).im)) := (Real.exp_pos _).le
  have hexpEE : Real.exp (2 * Real.pi * t) * Real.exp (-(2 * Real.pi * (ModularGroup.S • w).im))
      ≤ Real.exp (4 * Real.pi) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, htT])
  have hG00 : ‖Gcusp ℓ d 0 0 w‖ ≤ A * (Work.Kernels.scale w) ^ NA := hgb w hw 0 0
  have hG01 : ‖Gcusp ℓ d 0 1 w‖ ≤ A * (Work.Kernels.scale w) ^ NA := hgb w hw 0 1
  have hG10 : ‖Gcusp ℓ d 1 0 w‖ ≤ Cg * (Work.Kernels.scale w) ^ Ng
      * Real.exp (-(2 * Real.pi * (ModularGroup.S • w).im)) := hrow w hw 0
  have hG11 : ‖Gcusp ℓ d 1 1 w‖ ≤ Cg * (Work.Kernels.scale w) ^ Ng
      * Real.exp (-(2 * Real.pi * (ModularGroup.S • w).im)) := hrow w hw 1
  have htI : ‖((t : ℂ) * Complex.I)‖ = t := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0le]
  have hExp : ‖Complex.exp (2 * Real.pi * t)‖ = Real.exp (2 * Real.pi * t) := by
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  have h01I : ‖((t : ℂ) * Complex.I) * Gcusp ℓ d 0 1 w‖ = t * ‖Gcusp ℓ d 0 1 w‖ := by
    rw [norm_mul, htI]
  have h11I : ‖((t : ℂ) * Complex.I) * Gcusp ℓ d 1 1 w‖ = t * ‖Gcusp ℓ d 1 1 w‖ := by
    rw [norm_mul, htI]
  -- step 1: split the norm
  have hfirst : ‖Gcusp ℓ d 0 0 w + ((t : ℂ) * Complex.I) * Gcusp ℓ d 0 1 w‖
      ≤ ‖Gcusp ℓ d 0 0 w‖ + t * ‖Gcusp ℓ d 0 1 w‖ := by
    calc ‖Gcusp ℓ d 0 0 w + ((t : ℂ) * Complex.I) * Gcusp ℓ d 0 1 w‖
        ≤ ‖Gcusp ℓ d 0 0 w‖ + ‖((t : ℂ) * Complex.I) * Gcusp ℓ d 0 1 w‖ := norm_add_le _ _
      _ = ‖Gcusp ℓ d 0 0 w‖ + t * ‖Gcusp ℓ d 0 1 w‖ := by rw [h01I]
  have hsecond : ‖Complex.exp (2 * Real.pi * t)
        * (Gcusp ℓ d 1 0 w + ((t : ℂ) * Complex.I) * Gcusp ℓ d 1 1 w)‖
      ≤ Real.exp (2 * Real.pi * t) * ‖Gcusp ℓ d 1 0 w‖
        + Real.exp (2 * Real.pi * t) * (t * ‖Gcusp ℓ d 1 1 w‖) := by
    rw [norm_mul, hExp]
    calc Real.exp (2 * Real.pi * t)
          * ‖Gcusp ℓ d 1 0 w + ((t : ℂ) * Complex.I) * Gcusp ℓ d 1 1 w‖
        ≤ Real.exp (2 * Real.pi * t)
          * (‖Gcusp ℓ d 1 0 w‖ + ‖((t : ℂ) * Complex.I) * Gcusp ℓ d 1 1 w‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) (Real.exp_pos _).le
      _ = Real.exp (2 * Real.pi * t) * (‖Gcusp ℓ d 1 0 w‖ + t * ‖Gcusp ℓ d 1 1 w‖) := by
          rw [h11I]
      _ = Real.exp (2 * Real.pi * t) * ‖Gcusp ℓ d 1 0 w‖
          + Real.exp (2 * Real.pi * t) * (t * ‖Gcusp ℓ d 1 1 w‖) := by rw [mul_add]
  have step1 : ‖Aexp (Gcusp ℓ d) w t‖
      ≤ (‖Gcusp ℓ d 0 0 w‖ + t * ‖Gcusp ℓ d 0 1 w‖)
        + (Real.exp (2 * Real.pi * t) * ‖Gcusp ℓ d 1 0 w‖
            + Real.exp (2 * Real.pi * t) * (t * ‖Gcusp ℓ d 1 1 w‖)) := by
    rw [Aexp]
    calc ‖Gcusp ℓ d 0 0 w + ((t : ℂ) * Complex.I) * Gcusp ℓ d 0 1 w
          + Complex.exp (2 * Real.pi * t)
            * (Gcusp ℓ d 1 0 w + ((t : ℂ) * Complex.I) * Gcusp ℓ d 1 1 w)‖
        ≤ ‖Gcusp ℓ d 0 0 w + ((t : ℂ) * Complex.I) * Gcusp ℓ d 0 1 w‖
          + ‖Complex.exp (2 * Real.pi * t)
            * (Gcusp ℓ d 1 0 w + ((t : ℂ) * Complex.I) * Gcusp ℓ d 1 1 w)‖ := norm_add_le _ _
      _ ≤ (‖Gcusp ℓ d 0 0 w‖ + t * ‖Gcusp ℓ d 0 1 w‖)
          + (Real.exp (2 * Real.pi * t) * ‖Gcusp ℓ d 1 0 w‖
              + Real.exp (2 * Real.pi * t) * (t * ‖Gcusp ℓ d 1 1 w‖)) :=
          add_le_add hfirst hsecond
  -- step 2: bound the four pieces
  have h00N : ‖Gcusp ℓ d 0 0 w‖ ≤ A * (Work.Kernels.scale w) ^ (NA + Ng + 1) :=
    le_trans hG00 (mul_le_mul_of_nonneg_left hpNA hA)
  have h01N : t * ‖Gcusp ℓ d 0 1 w‖ ≤ A * (Work.Kernels.scale w) ^ (NA + Ng + 1) := by
    have h1 : t * ‖Gcusp ℓ d 0 1 w‖ ≤ t * (A * (Work.Kernels.scale w) ^ NA) :=
      mul_le_mul_of_nonneg_left hG01 ht0le
    have h2 : t * (A * (Work.Kernels.scale w) ^ NA)
        ≤ (Work.Kernels.scale w) * (A * (Work.Kernels.scale w) ^ NA) :=
      mul_le_mul_of_nonneg_right htle' (mul_nonneg hA (Real.rpow_nonneg hs0 _))
    have h3 : (Work.Kernels.scale w) * (A * (Work.Kernels.scale w) ^ NA)
        = A * (Work.Kernels.scale w) ^ (NA + 1) := by
      have hsNA : (Work.Kernels.scale w) * (Work.Kernels.scale w) ^ NA
          = (Work.Kernels.scale w) ^ (NA + 1) :=
        mul_rpow_add_one (Work.Kernels.scale_pos w) NA
      rw [show A * (Work.Kernels.scale w) ^ (NA + 1)
            = A * ((Work.Kernels.scale w) * (Work.Kernels.scale w) ^ NA) by rw [hsNA]]
      ring
    have h4 : A * (Work.Kernels.scale w) ^ (NA + 1)
        ≤ A * (Work.Kernels.scale w) ^ (NA + Ng + 1) :=
      mul_le_mul_of_nonneg_left hpNA1 hA
    exact le_trans h1 (le_trans h2 (le_trans (le_of_eq h3) h4))
  have h10N : Real.exp (2 * Real.pi * t) * ‖Gcusp ℓ d 1 0 w‖
      ≤ Cg * Real.exp (4 * Real.pi) * (Work.Kernels.scale w) ^ (NA + Ng + 1) := by
    have h1 : Real.exp (2 * Real.pi * t) * ‖Gcusp ℓ d 1 0 w‖
        ≤ Real.exp (2 * Real.pi * t)
            * (Cg * (Work.Kernels.scale w) ^ Ng
                * Real.exp (-(2 * Real.pi * (ModularGroup.S • w).im))) :=
      mul_le_mul_of_nonneg_left hG10 (Real.exp_pos _).le
    have h2 : Real.exp (2 * Real.pi * t)
            * (Cg * (Work.Kernels.scale w) ^ Ng
                * Real.exp (-(2 * Real.pi * (ModularGroup.S • w).im)))
        ≤ Cg * Real.exp (4 * Real.pi) * (Work.Kernels.scale w) ^ (NA + Ng + 1) := by
      have hstep : Real.exp (2 * Real.pi * t)
            * (Cg * (Work.Kernels.scale w) ^ Ng
                * Real.exp (-(2 * Real.pi * (ModularGroup.S • w).im)))
          = Cg * (Real.exp (2 * Real.pi * t)
                * Real.exp (-(2 * Real.pi * (ModularGroup.S • w).im)))
              * (Work.Kernels.scale w) ^ Ng := by ring
      rw [hstep]
      refine le_trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hexpEE hCg.le) (Real.rpow_nonneg hs0 _)) ?_
      exact mul_le_mul_of_nonneg_left hpNg (mul_nonneg hCg.le (Real.exp_pos _).le)
    exact le_trans h1 h2
  have h11N : Real.exp (2 * Real.pi * t) * (t * ‖Gcusp ℓ d 1 1 w‖)
      ≤ Cg * Real.exp (4 * Real.pi) * (Work.Kernels.scale w) ^ (NA + Ng + 1) := by
    have h1 : t * ‖Gcusp ℓ d 1 1 w‖
        ≤ t * (Cg * (Work.Kernels.scale w) ^ Ng
            * Real.exp (-(2 * Real.pi * (ModularGroup.S • w).im))) :=
      mul_le_mul_of_nonneg_left hG11 ht0le
    have h1' : Real.exp (2 * Real.pi * t) * (t * ‖Gcusp ℓ d 1 1 w‖)
        ≤ Real.exp (2 * Real.pi * t)
            * (t * (Cg * (Work.Kernels.scale w) ^ Ng
                * Real.exp (-(2 * Real.pi * (ModularGroup.S • w).im)))) :=
      mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    have h2 : Real.exp (2 * Real.pi * t)
            * (t * (Cg * (Work.Kernels.scale w) ^ Ng
                * Real.exp (-(2 * Real.pi * (ModularGroup.S • w).im))))
        ≤ Cg * Real.exp (4 * Real.pi) * (Work.Kernels.scale w) ^ (NA + Ng + 1) := by
      have hstep : Real.exp (2 * Real.pi * t)
            * (t * (Cg * (Work.Kernels.scale w) ^ Ng
                * Real.exp (-(2 * Real.pi * (ModularGroup.S • w).im))))
          = t * Cg * (Real.exp (2 * Real.pi * t)
                * Real.exp (-(2 * Real.pi * (ModularGroup.S • w).im)))
              * (Work.Kernels.scale w) ^ Ng := by ring
      rw [hstep]
      have h3 : t * Cg * (Real.exp (2 * Real.pi * t)
              * Real.exp (-(2 * Real.pi * (ModularGroup.S • w).im)))
            * (Work.Kernels.scale w) ^ Ng
          ≤ (Work.Kernels.scale w) * Cg * Real.exp (4 * Real.pi)
              * (Work.Kernels.scale w) ^ Ng := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hs0 _)
        exact mul_le_mul (mul_le_mul_of_nonneg_right htle' hCg.le) hexpEE
          (mul_nonneg (Real.exp_pos _).le hEE0) (mul_nonneg hs0 hCg.le)
      refine le_trans h3 ?_
      have hsNg : (Work.Kernels.scale w) * (Work.Kernels.scale w) ^ Ng
          = (Work.Kernels.scale w) ^ (Ng + 1) :=
        mul_rpow_add_one (Work.Kernels.scale_pos w) Ng
      have h4 : (Work.Kernels.scale w) * Cg * Real.exp (4 * Real.pi)
            * (Work.Kernels.scale w) ^ Ng
          = Cg * Real.exp (4 * Real.pi)
              * ((Work.Kernels.scale w) * (Work.Kernels.scale w) ^ Ng) := by ring
      rw [h4, hsNg]
      exact mul_le_mul_of_nonneg_left hpNg1 (mul_nonneg hCg.le (Real.exp_pos _).le)
    exact le_trans h1' h2
  -- assemble
  have hsum : ‖Aexp (Gcusp ℓ d) w t‖
      ≤ (2 * A + 2 * Cg * Real.exp (4 * Real.pi)) * (Work.Kernels.scale w) ^ (NA + Ng + 1) := by
    refine le_trans step1 ?_
    have h := add_le_add (add_le_add h00N h01N) (add_le_add h10N h11N)
    refine le_trans h (le_of_eq ?_)
    ring
  refine le_trans hsum ?_
  refine mul_le_mul_of_nonneg_right ?_ hsN0
  nlinarith [hA, hCg.le, hE4]

/-! ## The target -/

theorem EpolyWindowE_top (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (w : UpperHalfPlane) (t : ℝ), w ∈ Work.Asymptotics.KEpsilon →
        (ModularGroup.S • w).im + 1 ≤ t → t ≤ Work.Kernels.scale w →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t‖
          ≤ C * (Work.Kernels.scale w) ^ N * (1 + t) ^ M := by
  obtain ⟨C₁, N₁, M₁, hC₁, hN₁, hM₁, hdev⟩ := E_deviation_sharp ℓ d hd
  obtain ⟨Ch, Nh, hCh, hNh, hAh⟩ := Aexp_poly_bound ℓ d hd
  refine ⟨2 * max C₁ Ch + 1, max N₁ Nh, M₁, ?_, le_trans hN₁ (le_max_left _ _), hM₁,
    fun w t hw h1 h2 => ?_⟩
  · have h := lt_of_lt_of_le hC₁ (le_max_left (C₁ : ℝ) Ch); linarith
  · have hs1 : (1 : ℝ) ≤ Work.Kernels.scale w := Work.Kernels.one_le_scale w
    have hs0 : (0 : ℝ) ≤ Work.Kernels.scale w := le_trans zero_le_one hs1
    have hu0 : (0 : ℝ) ≤ 1 + t := by
      have : (2 : ℝ) ≤ (ModularGroup.S • w).im := hw.2
      linarith
    have hu1 : (1 : ℝ) ≤ 1 + t := by
      have : (2 : ℝ) ≤ (ModularGroup.S • w).im := hw.2
      linarith
    have hTt : (ModularGroup.S • w).im ≤ t := by linarith
    have hexp1 : Real.exp (-(Real.pi * (t - (ModularGroup.S • w).im))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [Real.pi_pos, hTt]
    have hdev' : ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t
          - Aexp (Gcusp ℓ d) w t‖ ≤ C₁ * (Work.Kernels.scale w) ^ N₁ * (1 + t) ^ M₁ := by
      refine le_trans (hdev w t hw h1) ?_
      have h0 : (0 : ℝ) ≤ C₁ * (Work.Kernels.scale w) ^ N₁ * (1 + t) ^ M₁ :=
        mul_nonneg (mul_nonneg hC₁.le (Real.rpow_nonneg hs0 _)) (Real.rpow_nonneg hu0 _)
      calc C₁ * (Work.Kernels.scale w) ^ N₁ * (1 + t) ^ M₁
            * Real.exp (-(Real.pi * (t - (ModularGroup.S • w).im)))
          ≤ C₁ * (Work.Kernels.scale w) ^ N₁ * (1 + t) ^ M₁ * 1 :=
            mul_le_mul_of_nonneg_left hexp1 h0
        _ = C₁ * (Work.Kernels.scale w) ^ N₁ * (1 + t) ^ M₁ := by ring
    have hAh' : ‖Aexp (Gcusp ℓ d) w t‖ ≤ Ch * (Work.Kernels.scale w) ^ Nh := hAh w t hw h1 h2
    have hsN₁ : (Work.Kernels.scale w) ^ N₁ ≤ (Work.Kernels.scale w) ^ (max N₁ Nh) :=
      Real.rpow_le_rpow_of_exponent_le hs1 (le_max_left _ _)
    have hsNh : (Work.Kernels.scale w) ^ Nh ≤ (Work.Kernels.scale w) ^ (max N₁ Nh) :=
      Real.rpow_le_rpow_of_exponent_le hs1 (le_max_right _ _)
    have hP0 : (0 : ℝ) ≤ (Work.Kernels.scale w) ^ (max N₁ Nh) := Real.rpow_nonneg hs0 _
    have huM0 : (0 : ℝ) ≤ (1 + t) ^ M₁ := Real.rpow_nonneg hu0 _
    have huM1 : (1 : ℝ) ≤ (1 + t) ^ M₁ := Real.one_le_rpow hu1 hM₁
    have t1 : C₁ * (Work.Kernels.scale w) ^ N₁ * (1 + t) ^ M₁
        ≤ C₁ * (Work.Kernels.scale w) ^ (max N₁ Nh) * (1 + t) ^ M₁ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsN₁ hC₁.le) huM0
    have t2 : Ch * (Work.Kernels.scale w) ^ Nh
        ≤ Ch * (Work.Kernels.scale w) ^ (max N₁ Nh) * (1 + t) ^ M₁ := by
      have ha : Ch * (Work.Kernels.scale w) ^ Nh
          ≤ Ch * (Work.Kernels.scale w) ^ (max N₁ Nh) :=
        mul_le_mul_of_nonneg_left hsNh hCh.le
      have hb : Ch * (Work.Kernels.scale w) ^ (max N₁ Nh)
          ≤ Ch * (Work.Kernels.scale w) ^ (max N₁ Nh) * (1 + t) ^ M₁ := by
        calc Ch * (Work.Kernels.scale w) ^ (max N₁ Nh)
            = Ch * (Work.Kernels.scale w) ^ (max N₁ Nh) * 1 := by ring
          _ ≤ Ch * (Work.Kernels.scale w) ^ (max N₁ Nh) * (1 + t) ^ M₁ :=
              mul_le_mul_of_nonneg_left huM1 (mul_nonneg hCh.le hP0)
      exact le_trans ha hb
    have hsum : C₁ * (Work.Kernels.scale w) ^ N₁ * (1 + t) ^ M₁
          + Ch * (Work.Kernels.scale w) ^ Nh
        ≤ (2 * max C₁ Ch + 1) * (Work.Kernels.scale w) ^ (max N₁ Nh) * (1 + t) ^ M₁ := by
      have h := add_le_add t1 t2
      refine le_trans h ?_
      have hcoef : C₁ + Ch ≤ 2 * max C₁ Ch + 1 := by
        have h1 := le_max_left (C₁ : ℝ) Ch
        have h2 := le_max_right (C₁ : ℝ) Ch
        linarith
      refine le_trans (le_of_eq (by ring : C₁ * (Work.Kernels.scale w) ^ (max N₁ Nh)
                * (1 + t) ^ M₁ + Ch * (Work.Kernels.scale w) ^ (max N₁ Nh) * (1 + t) ^ M₁
              = (C₁ + Ch) * (Work.Kernels.scale w) ^ (max N₁ Nh) * (1 + t) ^ M₁)) ?_
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef hP0) huM0
    calc ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t‖
        = ‖(Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t - Aexp (Gcusp ℓ d) w t)
            + Aexp (Gcusp ℓ d) w t‖ := by rw [sub_add_cancel]
      _ ≤ ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) w t - Aexp (Gcusp ℓ d) w t‖
            + ‖Aexp (Gcusp ℓ d) w t‖ := norm_add_le _ _
      _ ≤ C₁ * (Work.Kernels.scale w) ^ N₁ * (1 + t) ^ M₁
            + Ch * (Work.Kernels.scale w) ^ Nh := add_le_add hdev' hAh'
      _ ≤ (2 * max C₁ Ch + 1) * (Work.Kernels.scale w) ^ (max N₁ Nh) * (1 + t) ^ M₁ := hsum

end Work.Asymptotics
