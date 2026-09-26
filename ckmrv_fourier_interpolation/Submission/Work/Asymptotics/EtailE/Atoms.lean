/-
# The `τ`-atoms on the cusp-`0` tile `E`

For `w ∈ E = KEpsilon` the `τ`-atoms of the CKMRV kernels have the following `Bdd`-shapes
(see `Shapes.lean`):

* `Bdd 0` (moderate): `E₄, E₆, E₂, φ_i, ψ₂, ψ₄, Lamb, E₈, E₁₀, E₁₄`;
* `Bdd (2π)` (large): `j(w), Δ(w)⁻¹, E₁₄(w)/Δ(w), E₁₀(w)/Δ(w)`;
* `Bdd (-2π)` (small): `Δ(w)`, `ψ₄E₈ - ψ₂E₁₀`.
-/
import Mathlib
import Submission.Work.Asymptotics.EtailE.Shapes

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm

namespace Work.Asymptotics.EtailE

open Work.Kernels

/-! ## Pointwise `S`-transformation laws -/

lemma E4Fun_S (τ : ℍ) : E4Fun (ModularGroup.S • τ) = (τ : ℂ) ^ 4 * E4Fun τ :=
  KernelFacts.smul_of_slash_inv KernelFacts.E4Fun_S_slash τ

lemma E6Fun_S (τ : ℍ) : E6Fun (ModularGroup.S • τ) = (τ : ℂ) ^ 6 * E6Fun τ :=
  KernelFacts.smul_of_slash_inv KernelFacts.E6Fun_S_slash τ

lemma DeltaFun_Ssmul (τ : ℍ) : DeltaFun (ModularGroup.S • τ) = (τ : ℂ) ^ 12 * DeltaFun τ :=
  KernelFacts.smul_of_slash_inv KernelFacts.DeltaFun_S_slash τ

lemma jInvariantFun_Ssmul (τ : ℍ) : jInvariantFun (ModularGroup.S • τ) = jInvariantFun τ :=
  KernelFacts.jInvariantFun_S_smul τ

lemma psi2_S (ℓ : LogLambdaData) (τ : ℍ) :
    psi2 ℓ (ModularGroup.S • τ) = (τ : ℂ) ^ 2 * psi2 ℓ τ :=
  KernelFacts.smul_of_sopm (KernelFacts.psi2_Sopm ℓ) τ

lemma psi4_S (ℓ : LogLambdaData) (τ : ℍ) :
    psi4 ℓ (ModularGroup.S • τ) = (τ : ℂ) ^ 4 * psi4 ℓ τ :=
  KernelFacts.smul_of_sopm (KernelFacts.psi4_Sopm ℓ) τ

lemma E2Fun_S' (w : ℍ) :
    E2Fun w = (((ModularGroup.S • w : ℍ)) : ℂ) ^ 2 * E2Fun (ModularGroup.S • w)
      - 6 * Complex.I * (((ModularGroup.S • w : ℍ)) : ℂ) / (Real.pi : ℂ) := by
  have h := Work.Kernels.E2Fun_S_smul (ModularGroup.S • w)
  rw [E_S_smul_S_smul] at h
  exact h

lemma E8_eq (τ : ℍ) : E8Fun τ = E4Fun τ ^ 2 := rfl
lemma E10_eq (τ : ℍ) : E10Fun τ = E4Fun τ * E6Fun τ := rfl
lemma E14_eq (τ : ℍ) : E14Fun τ = E4Fun τ ^ 2 * E6Fun τ := rfl

lemma exp_zero_im (w : ℍ) : Real.exp (0 * (ModularGroup.S • w).im) = 1 := by
  rw [zero_mul, Real.exp_zero]

lemma E_mul_rpow (w : ℍ) (N : ℝ) : scale w * (scale w) ^ N = (scale w) ^ (N + 1) := by
  have hpow1 : (scale w) ^ (N + 1) = (scale w) ^ N * (scale w) ^ (1:ℝ) :=
    Real.rpow_add (E_scale_pos w) N 1
  have hone : (scale w) ^ (1:ℝ) = scale w := Real.rpow_one _
  rw [hpow1, hone, mul_comm]

/-- Extract the plain bound `C (scale w)^N` from a `Bdd 0` statement. -/
lemma Bdd.exists_bound_zero {F : ℍ → ℂ} (h : Bdd 0 F) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ w : ℍ, w ∈ KEpsilon → ‖F w‖ ≤ C * (scale w) ^ N := by
  obtain ⟨C, N, hC, hN, hb⟩ := h
  exact ⟨C, N, hC, hN, fun w hw => by
    have h1 := hb w hw
    rw [exp_zero_im, mul_one] at h1
    simpa only [] using h1⟩

/-! ## Moderate atoms (`Bdd 0`) -/

lemma E_bdd_E4 : Bdd 0 (fun w : ℍ => E4Fun w) := by
  obtain ⟨C, hC, hb⟩ := exists_E4_Funnel_bound
  refine ⟨C, ((4:ℕ):ℝ), hC, by norm_num, fun w hw => ?_⟩
  dsimp only
  have hσ : E4Fun w = (((ModularGroup.S • w : ℍ)) : ℂ) ^ 4 * E4Fun (ModularGroup.S • w) := by
    have h := E4Fun_S (ModularGroup.S • w)
    rw [E_S_smul_S_smul] at h
    exact h
  have h1 : ‖((ModularGroup.S • w : ℍ) : ℂ)‖ ≤ scale w := E_norm_S_le_scale w
  have h2 : ‖E4Fun (ModularGroup.S • w)‖ ≤ C := hb _ (E_S_mem_Funnel hw)
  rw [hσ, norm_mul, norm_pow, exp_zero_im, mul_one, Real.rpow_natCast]
  calc ‖((ModularGroup.S • w : ℍ) : ℂ)‖ ^ 4 * ‖E4Fun (ModularGroup.S • w)‖
      ≤ (scale w) ^ 4 * C :=
        mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) h1 4) h2 (norm_nonneg _) (by positivity)
    _ = C * (scale w) ^ 4 := by ring

lemma E_bdd_E6 : Bdd 0 (fun w : ℍ => E6Fun w) := by
  obtain ⟨C, hC, hb⟩ := exists_E6_Funnel_bound
  refine ⟨C, ((6:ℕ):ℝ), hC, by norm_num, fun w hw => ?_⟩
  dsimp only
  have hσ : E6Fun w = (((ModularGroup.S • w : ℍ)) : ℂ) ^ 6 * E6Fun (ModularGroup.S • w) := by
    have h := E6Fun_S (ModularGroup.S • w)
    rw [E_S_smul_S_smul] at h
    exact h
  have h1 : ‖((ModularGroup.S • w : ℍ) : ℂ)‖ ≤ scale w := E_norm_S_le_scale w
  have h2 : ‖E6Fun (ModularGroup.S • w)‖ ≤ C := hb _ (E_S_mem_Funnel hw)
  rw [hσ, norm_mul, norm_pow, exp_zero_im, mul_one, Real.rpow_natCast]
  calc ‖((ModularGroup.S • w : ℍ) : ℂ)‖ ^ 6 * ‖E6Fun (ModularGroup.S • w)‖
      ≤ (scale w) ^ 6 * C :=
        mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) h1 6) h2 (norm_nonneg _) (by positivity)
    _ = C * (scale w) ^ 6 := by ring

lemma norm_pi : ‖(Real.pi : ℂ)‖ = Real.pi := by
  rw [Complex.norm_def, Complex.normSq_ofReal]
  exact Real.sqrt_mul_self Real.pi_pos.le

lemma E_bdd_E2 : Bdd 0 (fun w : ℍ => E2Fun w) := by
  obtain ⟨C, hC, hb⟩ := exists_E2_Funnel_bound
  have h6 : (6:ℝ)/Real.pi ≤ 6 := by
    rw [div_le_iff₀ Real.pi_pos]; nlinarith [Real.pi_gt_three]
  refine ⟨C + 6 + 1, ((2:ℕ):ℝ), by positivity, by norm_num, fun w hw => ?_⟩
  dsimp only
  have hσ := E2Fun_S' w
  have h1 : ‖E2Fun (ModularGroup.S • w)‖ ≤ C := hb _ (E_S_mem_Funnel hw)
  have h2 : ‖((ModularGroup.S • w : ℍ) : ℂ)‖ ≤ scale w := E_norm_S_le_scale w
  have h6n : ‖(6 : ℂ) * Complex.I * (((ModularGroup.S • w : ℍ)) : ℂ) / (Real.pi : ℂ)‖
      = 6 / Real.pi * ‖(((ModularGroup.S • w : ℍ)) : ℂ)‖ := by
    rw [norm_div, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat, norm_pi]
    ring
  have hs1 : (1:ℝ) ≤ scale w := Work.Kernels.one_le_scale w
  rw [hσ, exp_zero_im, mul_one, Real.rpow_natCast]
  refine le_trans (norm_sub_le _ _) ?_
  rw [norm_mul, norm_pow, h6n]
  have h2' : ‖((ModularGroup.S • w : ℍ) : ℂ)‖ ^ 2 ≤ (scale w) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h2 2
  have h3' : 6 / Real.pi * ‖(((ModularGroup.S • w : ℍ)) : ℂ)‖ ≤ 6 * scale w := by
    have h := mul_le_mul_of_nonneg_right h6 (norm_nonneg (((ModularGroup.S • w : ℍ)) : ℂ))
    linarith [h, h2]
  have hgoal : (scale w) ^ 2 * C + 6 * scale w ≤ (C + 6 + 1) * (scale w) ^ 2 := by
    nlinarith [hC.le, hs1, E_rpow_nonneg w 2, sq_nonneg (scale w), (E_scale_pos w).le]
  calc ‖((ModularGroup.S • w : ℍ) : ℂ)‖ ^ 2 * ‖E2Fun (ModularGroup.S • w)‖
        + 6 / Real.pi * ‖(((ModularGroup.S • w : ℍ)) : ℂ)‖
      ≤ (scale w) ^ 2 * C + 6 * scale w :=
        add_le_add (mul_le_mul h2' h1 (norm_nonneg _) (by positivity)) h3'
    _ ≤ (C + 6 + 1) * (scale w) ^ 2 := hgoal

lemma E_bdd_phi0 : Bdd 0 (fun w : ℍ => phiVec w 0) := by
  refine ⟨1, ((1:ℕ):ℝ), one_pos, by norm_num, fun w _ => ?_⟩
  dsimp only
  have h : phiVec w 0 = (w : ℂ) := rfl
  rw [h, Real.rpow_natCast, pow_one, exp_zero_im, mul_one, one_mul]
  exact Work.Kernels.coe_norm_le_scale w

lemma E_bdd_phi1 : Bdd 0 (fun w : ℍ => phiVec w 1) := by
  obtain ⟨C, N, hC, hN, hb⟩ := E_bdd_E2.exists_bound_zero
  have h3le : 3 / Real.pi ≤ 3 := by
    rw [div_le_iff₀ Real.pi_pos]; nlinarith [Real.pi_gt_three]
  refine ⟨C + 3 + 1, ((N + 1 : ℝ)), by positivity, by linarith, fun w hw => ?_⟩
  dsimp only
  have h : phiVec w 1 = (w : ℂ) * E2Fun w - 3 * Complex.I / (Real.pi : ℂ) := rfl
  have h3 : ‖(3 : ℂ) * Complex.I / (Real.pi : ℂ)‖ = 3 / Real.pi := by
    rw [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat, norm_pi]
  have h1 : ‖(w : ℂ) * E2Fun w‖ ≤ scale w * (C * (scale w) ^ N) := by
    rw [norm_mul]
    exact mul_le_mul (Work.Kernels.coe_norm_le_scale w) (hb w hw) (norm_nonneg _)
      (E_scale_pos w).le
  have key : scale w * (C * (scale w) ^ N) = C * (scale w) ^ (N + 1) := by
    rw [show scale w * (C * (scale w) ^ N) = C * (scale w * (scale w) ^ N) from by ring,
      E_mul_rpow]
  have h2 : C * (scale w) ^ (N + 1) + 3 / Real.pi
      ≤ (C + 3 + 1) * (scale w) ^ (N + 1) := by
    have h1' : (1:ℝ) ≤ (scale w) ^ (N + 1) := E_one_le_rpow w (by linarith)
    have h2' : (0:ℝ) < (scale w) ^ (N + 1) := lt_of_lt_of_le one_pos h1'
    nlinarith [hC.le, h3le, h1', h2']
  rw [h, exp_zero_im, mul_one]
  calc ‖(w : ℂ) * E2Fun w - 3 * Complex.I / (Real.pi : ℂ)‖
      ≤ ‖(w : ℂ) * E2Fun w‖ + ‖3 * Complex.I / (Real.pi : ℂ)‖ := norm_sub_le _ _
    _ ≤ scale w * (C * (scale w) ^ N) + 3 / Real.pi := add_le_add h1 (le_of_eq h3)
    _ ≤ (C + 3 + 1) * (scale w) ^ (N + 1) := by rw [key]; exact h2

lemma E_bdd_phi2 : Bdd 0 (fun w : ℍ => phiVec w 2) := by
  obtain ⟨C, N, hC, hN, hb⟩ := E_bdd_E2.exists_bound_zero
  have h6 : (6:ℝ)/Real.pi ≤ 6 := by
    rw [div_le_iff₀ Real.pi_pos]; nlinarith [Real.pi_gt_three]
  refine ⟨C * C + 6 * C + 1, 2 * N + 1, by positivity, by linarith, fun w hw => ?_⟩
  dsimp only
  have h : phiVec w 2 = (w : ℂ) * E2Fun w ^ 2
      - (6 * Complex.I / (Real.pi : ℂ)) * E2Fun w := rfl
  have h6n : ‖(6 * Complex.I / (Real.pi : ℂ)) * E2Fun w‖ = 6 / Real.pi * ‖E2Fun w‖ := by
    rw [norm_mul, norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat, norm_pi]
    first | ring | skip
  have hs : (1:ℝ) ≤ scale w := Work.Kernels.one_le_scale w
  have hE := hb w hw
  have h1 : ‖(w : ℂ) * E2Fun w ^ 2‖ ≤ C ^ 2 * (scale w) ^ (2 * N + 1) := by
    rw [norm_mul, norm_pow]
    have hE2 : ‖E2Fun w‖ ^ 2 ≤ (C * (scale w) ^ N) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hE 2
    have hC2 : (C * (scale w) ^ N) ^ 2 = C ^ 2 * (scale w) ^ (2 * N) := by
      have hpow : ((scale w) ^ N) ^ (2:ℕ) = (scale w) ^ (2 * N) := by
        rw [pow_two, ← Real.rpow_add (E_scale_pos w), show N + N = 2 * N by ring]
      calc (C * (scale w) ^ N) ^ 2 = C ^ 2 * ((scale w) ^ N) ^ 2 := by rw [mul_pow]
        _ = C ^ 2 * (scale w) ^ (2 * N) := by rw [hpow]
    have h1' : ‖(w : ℂ)‖ * ‖E2Fun w‖ ^ 2 ≤ scale w * (C ^ 2 * (scale w) ^ (2 * N)) := by
      calc ‖(w : ℂ)‖ * ‖E2Fun w‖ ^ 2 ≤ scale w * (C * (scale w) ^ N) ^ 2 :=
            mul_le_mul (Work.Kernels.coe_norm_le_scale w) hE2 (by positivity) (E_scale_pos w).le
        _ = scale w * (C ^ 2 * (scale w) ^ (2 * N)) := by rw [hC2]
    calc ‖(w : ℂ)‖ * ‖E2Fun w‖ ^ 2 ≤ scale w * (C ^ 2 * (scale w) ^ (2 * N)) := h1'
      _ = C ^ 2 * (scale w * (scale w) ^ (2 * N)) := by ring
      _ = C ^ 2 * (scale w) ^ (2 * N + 1) := by rw [E_mul_rpow]
  have h2 : 6 / Real.pi * ‖E2Fun w‖ ≤ 6 * C * (scale w) ^ (2 * N + 1) := by
    have h1' : 6 / Real.pi * ‖E2Fun w‖ ≤ 6 / Real.pi * (C * (scale w) ^ N) :=
      mul_le_mul_of_nonneg_left hE (by positivity)
    have hNle : (scale w) ^ N ≤ (scale w) ^ (2 * N + 1) := E_rpow_mono w (by linarith)
    have hA : 6 / Real.pi * (C * (scale w) ^ N) ≤ 6 / Real.pi * (C * (scale w) ^ (2 * N + 1)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hNle hC.le) (by positivity)
    have hB : 6 / Real.pi * (C * (scale w) ^ (2 * N + 1)) ≤ 6 * C * (scale w) ^ (2 * N + 1) := by
      have h6' : 6 / Real.pi * C ≤ 6 * C :=
        mul_le_mul_of_nonneg_right h6 hC.le
      calc 6 / Real.pi * (C * (scale w) ^ (2 * N + 1))
          = (6 / Real.pi * C) * (scale w) ^ (2 * N + 1) := by ring
        _ ≤ (6 * C) * (scale w) ^ (2 * N + 1) :=
            mul_le_mul_of_nonneg_right h6' (E_rpow_nonneg w (2 * N + 1))
        _ = 6 * C * (scale w) ^ (2 * N + 1) := by ring
    linarith [h1', hA, hB]
  have h3 : C ^ 2 * (scale w) ^ (2 * N + 1) + 6 * C * (scale w) ^ (2 * N + 1)
      ≤ (C * C + 6 * C + 1) * (scale w) ^ (2 * N + 1) := by
    have h1' : (1:ℝ) ≤ (scale w) ^ (2 * N + 1) := E_one_le_rpow w (by linarith)
    have h2' : (0:ℝ) < (scale w) ^ (2 * N + 1) := lt_of_lt_of_le one_pos h1'
    nlinarith [hC.le, h1', h2']
  rw [h, exp_zero_im, mul_one]
  calc ‖(w : ℂ) * E2Fun w ^ 2 - (6 * Complex.I / (Real.pi : ℂ)) * E2Fun w‖
      ≤ ‖(w : ℂ) * E2Fun w ^ 2‖ + ‖(6 * Complex.I / (Real.pi : ℂ)) * E2Fun w‖ :=
        norm_sub_le _ _
    _ = ‖(w : ℂ) * E2Fun w ^ 2‖ + 6 / Real.pi * ‖E2Fun w‖ := by rw [h6n]
    _ ≤ C ^ 2 * (scale w) ^ (2 * N + 1) + 6 * C * (scale w) ^ (2 * N + 1) :=
        add_le_add h1 h2
    _ ≤ (C * C + 6 * C + 1) * (scale w) ^ (2 * N + 1) := h3

lemma E_bdd_psi2 (ℓ : LogLambdaData) : Bdd 0 (fun w : ℍ => psi2 ℓ w) := by
  obtain ⟨α, N, hα, hN, h⟩ := (Work.Kernels.moderateGrowthOn_iff_scale Set.univ
    (psi2 ℓ)).mp (psi_InP ℓ).1.2
  refine ⟨α + 1, N, by positivity, hN, fun w _ => ?_⟩
  dsimp only
  have h1 := h w (Set.mem_univ w)
  rw [exp_zero_im, mul_one]
  nlinarith [h1, hα, E_rpow_nonneg w N]

lemma E_bdd_psi4 (ℓ : LogLambdaData) : Bdd 0 (fun w : ℍ => psi4 ℓ w) := by
  obtain ⟨α, N, hα, hN, h⟩ := (Work.Kernels.moderateGrowthOn_iff_scale Set.univ
    (psi4 ℓ)).mp (psi_InP ℓ).2.2
  refine ⟨α + 1, N, by positivity, hN, fun w _ => ?_⟩
  dsimp only
  have h1 := h w (Set.mem_univ w)
  rw [exp_zero_im, mul_one]
  nlinarith [h1, hα, E_rpow_nonneg w N]

lemma E_bdd_E8 : Bdd 0 (fun w : ℍ => E8Fun w) := by
  have h := Bdd.mul_zero E_bdd_E4 E_bdd_E4
  refine Bdd.congr (funext fun w => ?_) h
  simp only [E8_eq, pow_two]

lemma E_bdd_E10 : Bdd 0 (fun w : ℍ => E10Fun w) := by
  have h := Bdd.mul_zero E_bdd_E4 E_bdd_E6
  refine Bdd.congr (funext fun w => ?_) h
  simp only [E10_eq]

lemma E_bdd_E14 : Bdd 0 (fun w : ℍ => E14Fun w) := by
  have h := Bdd.mul_zero (Bdd.mul_zero E_bdd_E4 E_bdd_E4) E_bdd_E6
  refine Bdd.congr (funext fun w => ?_) h
  simp only [E14_eq, pow_two]

/-! ## Large atoms (`Bdd (2π)`) -/

lemma three_le_scale (w : ℍ) : 3 ≤ scale w := by
  have h1 : 0 < w.im := w.im_pos
  have h2 : w.im ≤ ‖(w : ℂ)‖ := Work.Kernels.im_le_coe_norm w
  have h3 : w.im + (w.im)⁻¹ ≤ ‖(w : ℂ)‖ + (w.im)⁻¹ := by linarith
  have h4 : (2:ℝ) ≤ w.im + (w.im)⁻¹ := by
    rw [← sub_nonneg]
    have : w.im + (w.im)⁻¹ - 2 = (w.im - 1) ^ 2 / w.im := by
      field_simp
      ring
    rw [this]
    positivity
  unfold Work.Kernels.scale
  linarith

lemma E_bdd_j : Bdd (2 * Real.pi) (fun w : ℍ => jInvariantFun w) := by
  obtain ⟨C, hC, hb⟩ := exists_jInvariantFun_Funnel_bound
  refine ⟨C, 0, hC, le_rfl, fun w hw => ?_⟩
  dsimp only
  have h : jInvariantFun w = jInvariantFun (ModularGroup.S • w) := (jInvariantFun_Ssmul w).symm
  have hmain := hb _ (E_S_mem_Funnel hw)
  rw [h]
  calc ‖jInvariantFun (ModularGroup.S • w)‖
      ≤ C * Real.exp (2 * Real.pi * (ModularGroup.S • w).im) := hmain
    _ = C * (scale w) ^ (0:ℝ) * Real.exp ((2 * Real.pi) * (ModularGroup.S • w).im) := by
        rw [Real.rpow_zero, mul_one]

lemma E_bdd_invDelta : Bdd (2 * Real.pi) (fun w : ℍ => (DeltaFun w)⁻¹) := by
  obtain ⟨c, hc, hb⟩ := exists_Delta_Funnel_lower
  refine ⟨c⁻¹ + 1, 0, by positivity, le_rfl, fun w hw => ?_⟩
  dsimp only
  have hσ : DeltaFun w = (((ModularGroup.S • w : ℍ)) : ℂ) ^ 12 * DeltaFun (ModularGroup.S • w) := by
    have h := DeltaFun_Ssmul (ModularGroup.S • w)
    rw [E_S_smul_S_smul] at h
    exact h
  have hlow : c * Real.exp (-(2 * Real.pi * (ModularGroup.S • w).im))
      ≤ ‖DeltaFun (ModularGroup.S • w)‖ := hb _ (E_S_mem_Funnel hw)
  have hnorm : (2:ℝ) ≤ ‖(((ModularGroup.S • w : ℍ)) : ℂ)‖ := by
    rw [E_norm_S]
    have h3 : ‖(w : ℂ)‖ ≤ 1 / 2 := E_norm_le_half hw
    have h4 : 0 < ‖(w : ℂ)‖ := norm_pos_iff.mpr w.ne_zero
    rw [show (2:ℝ) = ((1/2:ℝ))⁻¹ by norm_num]
    exact inv_anti₀ h4 h3
  have hone : (1:ℝ) ≤ ‖(((ModularGroup.S • w : ℍ)) : ℂ)‖ ^ 12 :=
    one_le_pow₀ (by linarith : (1:ℝ) ≤ ‖(((ModularGroup.S • w : ℍ)) : ℂ)‖)
  have hprod : c * Real.exp (-(2 * Real.pi * (ModularGroup.S • w).im)) ≤ ‖DeltaFun w‖ := by
    rw [hσ, norm_mul, norm_pow]
    calc c * Real.exp (-(2 * Real.pi * (ModularGroup.S • w).im))
        ≤ ‖DeltaFun (ModularGroup.S • w)‖ := hlow
      _ = 1 * ‖DeltaFun (ModularGroup.S • w)‖ := (one_mul _).symm
      _ ≤ ‖(((ModularGroup.S • w : ℍ)) : ℂ)‖ ^ 12 * ‖DeltaFun (ModularGroup.S • w)‖ :=
          mul_le_mul_of_nonneg_right hone (norm_nonneg _)
  have hpos : 0 < c * Real.exp (-(2 * Real.pi * (ModularGroup.S • w).im)) :=
    mul_pos hc (Real.exp_pos _)
  have hΔpos : 0 < ‖DeltaFun w‖ := lt_of_lt_of_le hpos hprod
  have hinv := (inv_le_inv₀ hΔpos hpos).mpr hprod
  rw [norm_inv]
  calc (‖DeltaFun w‖)⁻¹
      ≤ (c * Real.exp (-(2 * Real.pi * (ModularGroup.S • w).im)))⁻¹ := hinv
    _ = c⁻¹ * Real.exp (2 * Real.pi * (ModularGroup.S • w).im) := by
        rw [mul_inv, ← Real.exp_neg]
        congr 1
        ring
    _ ≤ (c⁻¹ + 1) * (scale w) ^ (0:ℝ) * Real.exp ((2 * Real.pi) * (ModularGroup.S • w).im) := by
        rw [Real.rpow_zero, mul_one]
        have h1 : (0:ℝ) < Real.exp ((2 * Real.pi) * (ModularGroup.S • w).im) := Real.exp_pos _
        have h2 : (0:ℝ) ≤ c⁻¹ := inv_nonneg.mpr hc.le
        have h3 : Real.exp (2 * Real.pi * (ModularGroup.S • w).im)
            = Real.exp ((2 * Real.pi) * (ModularGroup.S • w).im) := rfl
        rw [h3]
        nlinarith

lemma E_bdd_E14_div_Delta (ℓ : LogLambdaData) :
    Bdd (2 * Real.pi) (fun w : ℍ => E14Fun w / DeltaFun w) := by
  have h := E_bdd_E14.mul E_bdd_invDelta
  have h' : Bdd (2 * Real.pi) (fun w => E14Fun w * (DeltaFun w)⁻¹) := by simpa using h
  exact Bdd.congr (funext fun w => by rw [div_eq_mul_inv]) h'

lemma E_bdd_E10_div_Delta :
    Bdd (2 * Real.pi) (fun w : ℍ => E10Fun w / DeltaFun w) := by
  have h := E_bdd_E10.mul E_bdd_invDelta
  have h' : Bdd (2 * Real.pi) (fun w => E10Fun w * (DeltaFun w)⁻¹) := by simpa using h
  exact Bdd.congr (funext fun w => by rw [div_eq_mul_inv]) h'

/-! ## Small atoms (`Bdd (-2π)`) -/

lemma E_bdd_Delta : Bdd (-(2 * Real.pi)) (fun w : ℍ => DeltaFun w) := by
  obtain ⟨C, hC, hb⟩ := MFix.DeltaFun_upper
  refine ⟨C, ((12:ℕ):ℝ), hC, by norm_num, fun w hw => ?_⟩
  dsimp only
  have hσ : DeltaFun w = (((ModularGroup.S • w : ℍ)) : ℂ) ^ 12 * DeltaFun (ModularGroup.S • w) := by
    have h := DeltaFun_Ssmul (ModularGroup.S • w)
    rw [E_S_smul_S_smul] at h
    exact h
  have h1 : ‖(((ModularGroup.S • w : ℍ)) : ℂ)‖ ≤ scale w := E_norm_S_le_scale w
  have h2 : ‖DeltaFun (ModularGroup.S • w)‖ ≤ C * ‖qParamFun (ModularGroup.S • w)‖ :=
    hb _ (by linarith [hw.2])
  have h3 : ‖qParamFun (ModularGroup.S • w)‖
      = Real.exp (-(2 * Real.pi * (ModularGroup.S • w).im)) := MFix.norm_qParamFun _
  have hneg : Real.exp (-(2 * Real.pi * (ModularGroup.S • w).im))
      = Real.exp ((-(2 * Real.pi)) * (ModularGroup.S • w).im) := by rw [neg_mul]
  rw [hσ, Real.rpow_natCast, norm_mul, norm_pow]
  calc ‖(((ModularGroup.S • w : ℍ)) : ℂ)‖ ^ 12 * ‖DeltaFun (ModularGroup.S • w)‖
      ≤ (scale w) ^ 12 * (C * ‖qParamFun (ModularGroup.S • w)‖) :=
        mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) h1 12) h2 (norm_nonneg _) (by positivity)
    _ = (scale w) ^ 12 * (C * Real.exp (-(2 * Real.pi * (ModularGroup.S • w).im))) := by rw [h3]
    _ = (scale w) ^ 12 * (C * Real.exp ((-(2 * Real.pi)) * (ModularGroup.S • w).im)) := by rw [hneg]
    _ = C * (scale w) ^ 12 * Real.exp ((-(2 * Real.pi)) * (ModularGroup.S • w).im) := by ring

lemma psi4E8_sub_psi2E10_S (ℓ : LogLambdaData) (τ : ℍ) :
    (psi4 ℓ (ModularGroup.S • τ) * E8Fun (ModularGroup.S • τ)
        - psi2 ℓ (ModularGroup.S • τ) * E10Fun (ModularGroup.S • τ))
      = (τ : ℂ) ^ 12 * (psi4 ℓ τ * E8Fun τ - psi2 ℓ τ * E10Fun τ) := by
  rw [psi4_S ℓ τ, psi2_S ℓ τ, E8_eq, E10_eq, E4Fun_S τ, E6Fun_S τ]
  ring

lemma E_bdd_psi4E8_sub (ℓ : LogLambdaData) :
    Bdd (-(2 * Real.pi)) (fun w : ℍ => psi4 ℓ w * E8Fun w - psi2 ℓ w * E10Fun w) := by
  obtain ⟨C, N, hC, hN, hb⟩ := psi4E8_sub_psi2E10_funnel ℓ
  refine ⟨C, 12 + (2 * N + 12), hC, by positivity, fun w hw => ?_⟩
  dsimp only
  have hσ : psi4 ℓ w * E8Fun w - psi2 ℓ w * E10Fun w
      = (((ModularGroup.S • w : ℍ)) : ℂ) ^ 12
        * (psi4 ℓ (ModularGroup.S • w) * E8Fun (ModularGroup.S • w)
            - psi2 ℓ (ModularGroup.S • w) * E10Fun (ModularGroup.S • w)) := by
    have h := psi4E8_sub_psi2E10_S ℓ (ModularGroup.S • w)
    rw [E_S_smul_S_smul] at h
    exact h
  have h1 : ‖(((ModularGroup.S • w : ℍ)) : ℂ)‖ ≤ scale w := E_norm_S_le_scale w
  have h2 : ‖psi4 ℓ (ModularGroup.S • w) * E8Fun (ModularGroup.S • w)
      - psi2 ℓ (ModularGroup.S • w) * E10Fun (ModularGroup.S • w)‖
      ≤ C * (scale (ModularGroup.S • w)) ^ N * ‖qParamFun (ModularGroup.S • w)‖ :=
    hb _ (E_S_mem_Funnel hw)
  have h3 : ‖qParamFun (ModularGroup.S • w)‖
      = Real.exp (-(2 * Real.pi * (ModularGroup.S • w).im)) := MFix.norm_qParamFun _
  have hneg : Real.exp (-(2 * Real.pi * (ModularGroup.S • w).im))
      = Real.exp ((-(2 * Real.pi)) * (ModularGroup.S • w).im) := by rw [neg_mul]
  have hscaleS : (scale (ModularGroup.S • w)) ^ N ≤ (scale w) ^ (2 * N) := by
    have hle : scale (ModularGroup.S • w) ≤ 3 * scale w := E_scale_S_le hw
    have h4 : (scale (ModularGroup.S • w)) ^ N ≤ (3 * scale w) ^ N :=
      Real.rpow_le_rpow (E_scale_pos _).le hle hN
    have h5 : (3 * scale w) ^ N = 3 ^ N * (scale w) ^ N :=
      Real.mul_rpow (by norm_num) (E_scale_pos w).le
    have h6 : 3 ^ N ≤ (scale w) ^ N :=
      Real.rpow_le_rpow (by norm_num) (three_le_scale w) hN
    have h7 : (scale w) ^ N * 3 ^ N ≤ (scale w) ^ N * (scale w) ^ N :=
      mul_le_mul_of_nonneg_left h6 (E_rpow_nonneg w N)
    calc (scale (ModularGroup.S • w)) ^ N ≤ (3 * scale w) ^ N := h4
      _ = 3 ^ N * (scale w) ^ N := h5
      _ = (scale w) ^ N * 3 ^ N := by ring
      _ ≤ (scale w) ^ N * (scale w) ^ N := h7
      _ = (scale w) ^ (2 * N) := by rw [E_rpow_mul]; ring_nf
  have h2' : ‖psi4 ℓ (ModularGroup.S • w) * E8Fun (ModularGroup.S • w)
      - psi2 ℓ (ModularGroup.S • w) * E10Fun (ModularGroup.S • w)‖
      ≤ C * (scale w) ^ (2 * N) * Real.exp ((-(2 * Real.pi)) * (ModularGroup.S • w).im) := by
    calc ‖psi4 ℓ (ModularGroup.S • w) * E8Fun (ModularGroup.S • w)
        - psi2 ℓ (ModularGroup.S • w) * E10Fun (ModularGroup.S • w)‖
        ≤ C * (scale (ModularGroup.S • w)) ^ N * ‖qParamFun (ModularGroup.S • w)‖ := h2
      _ = C * (scale (ModularGroup.S • w)) ^ N
            * Real.exp ((-(2 * Real.pi)) * (ModularGroup.S • w).im) := by rw [h3, hneg]
      _ ≤ C * (scale w) ^ (2 * N) * Real.exp ((-(2 * Real.pi)) * (ModularGroup.S • w).im) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hscaleS hC.le)
            (Real.exp_pos _).le
  have key : C * (scale w) ^ (2 * N) ≤ C * (scale w) ^ (2 * N + 12) := by
    refine mul_le_mul_of_nonneg_left (E_rpow_mono w ?_) hC.le
    linarith
  rw [hσ, norm_mul, norm_pow]
  calc ‖(((ModularGroup.S • w : ℍ)) : ℂ)‖ ^ 12
        * ‖psi4 ℓ (ModularGroup.S • w) * E8Fun (ModularGroup.S • w)
            - psi2 ℓ (ModularGroup.S • w) * E10Fun (ModularGroup.S • w)‖
      ≤ (scale w) ^ 12 * (C * (scale w) ^ (2 * N + 12)
          * Real.exp ((-(2 * Real.pi)) * (ModularGroup.S • w).im)) := by
        have h2'' : ‖psi4 ℓ (ModularGroup.S • w) * E8Fun (ModularGroup.S • w)
            - psi2 ℓ (ModularGroup.S • w) * E10Fun (ModularGroup.S • w)‖
            ≤ C * (scale w) ^ (2 * N + 12)
              * Real.exp ((-(2 * Real.pi)) * (ModularGroup.S • w).im) :=
          le_trans h2' (mul_le_mul_of_nonneg_right key (Real.exp_pos _).le)
        exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) h1 12) h2''
          (norm_nonneg _) (by positivity)
    _ = C * (scale w) ^ (12 + (2 * N + 12))
          * Real.exp ((-(2 * Real.pi)) * (ModularGroup.S • w).im) := by
        rw [show (scale w) ^ 12 = (scale w) ^ (((12:ℕ)):ℝ) from (Real.rpow_natCast _ 12).symm,
          show (scale w) ^ (((12:ℕ)):ℝ) * (C * (scale w) ^ (2 * N + 12)
            * Real.exp ((-(2 * Real.pi)) * (ModularGroup.S • w).im))
            = C * ((scale w) ^ (((12:ℕ)):ℝ) * (scale w) ^ (2 * N + 12))
              * Real.exp ((-(2 * Real.pi)) * (ModularGroup.S • w).im) from by ring,
          E_rpow_mul]
        ring

end Work.Asymptotics.EtailE

end
