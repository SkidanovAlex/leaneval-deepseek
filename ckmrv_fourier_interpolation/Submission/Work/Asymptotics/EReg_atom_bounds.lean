import Mathlib
import Submission.Work.Asymptotics.ERegDefs
import Submission.Work.Residues.ThetaDecay
import Submission.Work.Residues.LamSExpBound
import Submission.Work.Asymptotics.KPlusXiDefs
import Submission.Work.Asymptotics.DeltaFun_upper_sharp
import Submission.Work.Asymptotics.E_atom_poly

/-!
# Polynomial bounds for the cusp atoms on the CKMRV `E`-tile

On the cusp-`0` tile `E = {τ : ℍ | 3/2 ≤ (S • τ).im}` (`Work.Asymptotics.EReg`) the atoms out
of which the CKMRV kernels are built — the theta powers `U = θ₀₀⁴, V = θ₁₀⁴, W = θ₀₁⁴`, the
Eisenstein series `E₄, E₆`, the discriminant `Δ`, the normalised logarithms `𝓛, 𝓛_S` and the
modular `j`-invariant — are bounded by a power of the scale `scale τ = 1 + (Im τ)⁻¹ + ‖τ‖`,
with the exponential factor `tpar (S • τ) = e^{-π Im (S • τ)}` attached where the cusp-`0`
vanishing requires it (`W`, `Δ`, `𝓛`, `j`).

The transport is by the `S`-involution: with `w = S • τ` (so `S • w = τ`, `Im w ≥ 3/2`) one has
`U(τ) = -w²U(w)`, `V(τ) = -w²W(w)`, `W(τ) = -w²V(w)`, `E₄(τ) = w⁴E₄(w)`, `E₆(τ) = w⁶E₆(w)`,
`Δ(τ) = w¹²Δ(w)`, `j(τ) = j(w)`, `𝓛(τ) = 𝓛_S(w)`, `𝓛_S(τ) = 𝓛(w)`, and the cusp asymptotics
`U(w) = 1 + O(tpar w)`, `W(w) = 1 + O(tpar w)`, `V(w) = O(tpar w)`, `Δ(w) ≍ tpar(w)²`,
`E₄(w) = 1 + O(tpar w)²`, `E₆(w) = 1 + O(tpar w)²`, `𝓛_S(w) = O(tpar w)` supply the bounds.
-/

set_option maxHeartbeats 2000000

noncomputable section

open UpperHalfPlane ModularGroup
open Work.Kernels (scale)

namespace Work.Asymptotics

/-- The cusp-`0` cusp parameter `tpar (S • τ)`. -/
abbrev tS (τ : ℍ) : ℝ := Work.Residues.tpar (ModularGroup.S • τ)

/-- `S` is an involution on `ℍ`. -/
lemma EReg_S_S (τ : ℍ) : ModularGroup.S • (ModularGroup.S • τ) = τ := by
  apply UpperHalfPlane.ext
  rw [Work.Kernels.S_smul_coe, Work.Kernels.S_smul_coe]
  simp

/-- `‖S • τ‖ = 1 / ‖τ‖ ≤ scale τ`. -/
lemma EReg_norm_coe_S_le_scale (τ : ℍ) :
    ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖ ≤ scale τ := by
  rw [EReg_norm_S]
  exact EReg_inv_norm_le_scale τ

lemma tS_pos (τ : ℍ) : 0 < tS τ := Work.Residues.tpar_pos _
lemma tS_nonneg (τ : ℍ) : 0 ≤ tS τ := (tS_pos τ).le
lemma tS_le_one (τ : ℍ) : tS τ ≤ 1 := Work.Residues.tpar_le_one _

/-- `(↑(tS τ) : ℂ)` has norm `tS τ`. -/
lemma norm_tS_coe (τ : ℍ) : ‖((tS τ : ℝ) : ℂ)‖ = tS τ := Complex.norm_of_nonneg (tS_nonneg τ)

/-- The `tS`-form of `e^{-2π Im (S • τ)}`. -/
lemma exptS (τ : ℍ) : Real.exp (-(2 * Real.pi * (ModularGroup.S • τ).im)) = tS τ ^ 2 := by
  rw [tS, Work.Residues.tpar, sq, ← Real.exp_add]
  congr 1
  ring

/-! ## The `S`-transformation laws in the direction used below -/

lemma EReg_U_S (τ : ℍ) :
    Work.Kernels.UFun τ
      = -(((ModularGroup.S • τ : ℍ)) : ℂ) ^ 2 * Work.Kernels.UFun (ModularGroup.S • τ) := by
  have h := Work.Kernels.KernelFacts.UFun_S_smul (ModularGroup.S • τ)
  rwa [EReg_S_S τ] at h

lemma EReg_V_S (τ : ℍ) :
    Work.Kernels.VFun τ
      = -(((ModularGroup.S • τ : ℍ)) : ℂ) ^ 2 * Work.Kernels.WFun (ModularGroup.S • τ) := by
  have h := Work.Kernels.KernelFacts.VFun_S_smul (ModularGroup.S • τ)
  rwa [EReg_S_S τ] at h

lemma EReg_W_S (τ : ℍ) :
    Work.Kernels.WFun τ
      = -(((ModularGroup.S • τ : ℍ)) : ℂ) ^ 2 * Work.Kernels.VFun (ModularGroup.S • τ) := by
  have h := Work.Kernels.KernelFacts.WFun_S_smul (ModularGroup.S • τ)
  rwa [EReg_S_S τ] at h

lemma EReg_E4_S (τ : ℍ) :
    Work.Kernels.E4Fun τ
      = (((ModularGroup.S • τ : ℍ)) : ℂ) ^ 4 * Work.Kernels.E4Fun (ModularGroup.S • τ) := by
  have h := Work.Kernels.KernelFacts.smul_of_slash_inv
    (F := Work.Kernels.E4Fun) Work.Kernels.KernelFacts.E4Fun_S_slash (ModularGroup.S • τ)
  rwa [EReg_S_S τ] at h

lemma EReg_E6_S (τ : ℍ) :
    Work.Kernels.E6Fun τ
      = (((ModularGroup.S • τ : ℍ)) : ℂ) ^ 6 * Work.Kernels.E6Fun (ModularGroup.S • τ) := by
  have h := Work.Kernels.KernelFacts.smul_of_slash_inv
    (F := Work.Kernels.E6Fun) Work.Kernels.KernelFacts.E6Fun_S_slash (ModularGroup.S • τ)
  rwa [EReg_S_S τ] at h

lemma EReg_Delta_S (τ : ℍ) :
    Work.Kernels.DeltaFun τ
      = (((ModularGroup.S • τ : ℍ)) : ℂ) ^ 12 * Work.Kernels.DeltaFun (ModularGroup.S • τ) := by
  have h := Work.Kernels.KernelFacts.smul_of_slash_inv
    (F := Work.Kernels.DeltaFun) Work.Kernels.KernelFacts.DeltaFun_S_slash (ModularGroup.S • τ)
  rwa [EReg_S_S τ] at h

lemma EReg_L_S (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    ℓ.L τ = ℓ.L_S (ModularGroup.S • τ) := by
  have h := congr_fun ℓ.slash_S (ModularGroup.S • τ)
  rw [Work.Kernels.KernelFacts.kpc_slash_S_apply] at h
  simp only [mul_one, EReg_S_S, neg_zero, zpow_zero] at h
  exact h

lemma EReg_LS_S (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) :
    ℓ.L_S τ = ℓ.L (ModularGroup.S • τ) := by
  have h := congr_fun ℓ.slash_S_S (ModularGroup.S • τ)
  rw [Work.Kernels.KernelFacts.kpc_slash_S_apply] at h
  simp only [mul_one, EReg_S_S, neg_zero, zpow_zero] at h
  exact h

/-! ## Small calculus of `scale` powers -/

private lemma scale_nat_pow_le {n m : ℕ} (h : n ≤ m) (τ : ℍ) :
    (scale τ) ^ n ≤ (scale τ) ^ m :=
  pow_le_pow_right₀ (Work.Kernels.one_le_scale τ) h

private lemma scale_nat_le_rpow {n : ℕ} {N : ℝ} (h : (n : ℝ) ≤ N) (τ : ℍ) :
    (scale τ) ^ n ≤ (scale τ) ^ N := by
  rw [← Real.rpow_natCast (scale τ) n]
  exact Real.rpow_le_rpow_of_exponent_le (Work.Kernels.one_le_scale τ) h

private lemma rpow_nonneg' (τ : ℍ) (N : ℝ) : 0 ≤ (scale τ) ^ N :=
  Real.rpow_nonneg (Work.Kernels.scale_pos τ).le N

/-- Monotonicity of the `scale`-power bounds, from a natural to a real exponent. -/
private lemma atom_mono_nat {c C : ℝ} {n : ℕ} {N : ℝ} {τ : ℍ}
    (hc : c ≤ C) (hn : (n : ℝ) ≤ N) (hC : 0 ≤ C) :
    c * (scale τ) ^ n ≤ C * (scale τ) ^ N := by
  have h1 : (0 : ℝ) ≤ (scale τ) ^ n := pow_nonneg (Work.Kernels.scale_pos τ).le n
  calc c * (scale τ) ^ n ≤ C * (scale τ) ^ n := mul_le_mul_of_nonneg_right hc h1
    _ ≤ C * (scale τ) ^ N := mul_le_mul_of_nonneg_left (scale_nat_le_rpow hn τ) hC

private lemma atom_mono_rpow {c C n m : ℝ} {τ : ℍ}
    (hc : c ≤ C) (hn : n ≤ m) (hC : 0 ≤ C) :
    c * (scale τ) ^ n ≤ C * (scale τ) ^ m := by
  calc c * (scale τ) ^ n ≤ C * (scale τ) ^ n :=
        mul_le_mul_of_nonneg_right hc (rpow_nonneg' τ n)
    _ ≤ C * (scale τ) ^ m :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le (Work.Kernels.one_le_scale τ) hn) hC

/-! ## The individual atom bounds -/

private theorem EReg_U_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, τ ∈ EReg → ‖Work.Kernels.UFun τ‖ ≤ C * (scale τ) ^ 12 := by
  obtain ⟨C₁, hC₁, h1⟩ := Work.Residues.ThetaDecay.1
  refine ⟨C₁ + 1, by linarith, fun τ hτ => ?_⟩
  have hw1 : (1 : ℝ) ≤ (ModularGroup.S • τ).im := le_trans (by norm_num) hτ
  have hb : ‖Work.Kernels.UFun (ModularGroup.S • τ)‖ ≤ 1 + C₁ * tS τ := by
    have h := h1 _ hw1
    calc ‖Work.Kernels.UFun (ModularGroup.S • τ)‖
        = ‖(Work.Kernels.UFun (ModularGroup.S • τ) - 1) + 1‖ := by ring_nf
      _ ≤ ‖Work.Kernels.UFun (ModularGroup.S • τ) - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ C₁ * tS τ + 1 := by rw [norm_one]; exact add_le_add h le_rfl
      _ = 1 + C₁ * tS τ := by ring
  have hn : ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖ ≤ scale τ := EReg_norm_coe_S_le_scale τ
  rw [EReg_U_S τ, norm_mul, norm_neg, norm_pow]
  have h2 : ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖ ^ 2 ≤ (scale τ) ^ 12 :=
    le_trans (pow_le_pow_left₀ (norm_nonneg _) hn 2) (scale_nat_pow_le (by norm_num) τ)
  have h3 : ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖ ^ 2 * (1 + C₁ * tS τ)
      ≤ (scale τ) ^ 12 * (1 + C₁) := by
    have hb2 : (0 : ℝ) ≤ (scale τ) ^ 12 := by positivity
    have hb3 : (0 : ℝ) ≤ 1 + C₁ * tS τ := by
      exact add_nonneg zero_le_one (mul_nonneg hC₁.le (tS_nonneg τ))
    have h5 : 1 + C₁ * tS τ ≤ 1 + C₁ := by
      linarith [mul_le_of_le_one_right hC₁.le (tS_le_one τ)]
    exact mul_le_mul h2 h5 hb3 hb2
  calc ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖ ^ 2 * ‖Work.Kernels.UFun (ModularGroup.S • τ)‖
      ≤ ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖ ^ 2 * (1 + C₁ * tS τ) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ (scale τ) ^ 12 * (1 + C₁) := h3
    _ = (C₁ + 1) * (scale τ) ^ 12 := by ring

private theorem EReg_V_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, τ ∈ EReg → ‖Work.Kernels.VFun τ‖ ≤ C * (scale τ) ^ 12 := by
  obtain ⟨C₂, hC₂, h2⟩ := Work.Residues.ThetaDecay.2.1
  refine ⟨C₂ + 1, by linarith, fun τ hτ => ?_⟩
  have hw1 : (1 : ℝ) ≤ (ModularGroup.S • τ).im := le_trans (by norm_num) hτ
  have hb : ‖Work.Kernels.WFun (ModularGroup.S • τ)‖ ≤ 1 + C₂ * tS τ := by
    have h := h2 _ hw1
    calc ‖Work.Kernels.WFun (ModularGroup.S • τ)‖
        = ‖(Work.Kernels.WFun (ModularGroup.S • τ) - 1) + 1‖ := by ring_nf
      _ ≤ ‖Work.Kernels.WFun (ModularGroup.S • τ) - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ C₂ * tS τ + 1 := by rw [norm_one]; exact add_le_add h le_rfl
      _ = 1 + C₂ * tS τ := by ring
  have hn : ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖ ≤ scale τ := EReg_norm_coe_S_le_scale τ
  rw [EReg_V_S τ, norm_mul, norm_neg, norm_pow]
  have h3 : ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖ ^ 2 ≤ (scale τ) ^ 12 :=
    le_trans (pow_le_pow_left₀ (norm_nonneg _) hn 2) (scale_nat_pow_le (by norm_num) τ)
  have h4 : ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖ ^ 2 * (1 + C₂ * tS τ)
      ≤ (scale τ) ^ 12 * (1 + C₂) := by
    have hb2 : (0 : ℝ) ≤ (scale τ) ^ 12 := by positivity
    have hb3 : (0 : ℝ) ≤ 1 + C₂ * tS τ := by
      exact add_nonneg zero_le_one (mul_nonneg hC₂.le (tS_nonneg τ))
    have h5 : 1 + C₂ * tS τ ≤ 1 + C₂ := by
      linarith [mul_le_of_le_one_right hC₂.le (tS_le_one τ)]
    exact mul_le_mul h3 h5 hb3 hb2
  calc ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖ ^ 2 * ‖Work.Kernels.WFun (ModularGroup.S • τ)‖
      ≤ ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖ ^ 2 * (1 + C₂ * tS τ) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ (scale τ) ^ 12 * (1 + C₂) := h4
    _ = (C₂ + 1) * (scale τ) ^ 12 := by ring

private theorem EReg_W_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, τ ∈ EReg →
      ‖Work.Kernels.WFun τ‖ ≤ C * (scale τ) ^ 12 * tS τ := by
  obtain ⟨C₃, hC₃, h3⟩ := Work.Residues.ThetaDecay.2.2.1
  refine ⟨C₃, hC₃, fun τ hτ => ?_⟩
  have hw1 : (1 : ℝ) ≤ (ModularGroup.S • τ).im := le_trans (by norm_num) hτ
  have hb : ‖Work.Kernels.VFun (ModularGroup.S • τ)‖ ≤ C₃ * tS τ := h3 _ hw1
  have hn : ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖ ≤ scale τ := EReg_norm_coe_S_le_scale τ
  rw [EReg_W_S τ, norm_mul, norm_neg, norm_pow]
  have h2 : ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖ ^ 2 ≤ (scale τ) ^ 12 :=
    le_trans (pow_le_pow_left₀ (norm_nonneg _) hn 2) (scale_nat_pow_le (by norm_num) τ)
  calc ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖ ^ 2 * ‖Work.Kernels.VFun (ModularGroup.S • τ)‖
      ≤ ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖ ^ 2 * (C₃ * tS τ) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ (scale τ) ^ 12 * (C₃ * tS τ) :=
        mul_le_mul_of_nonneg_right h2 (mul_nonneg hC₃.le (tS_nonneg τ))
    _ = C₃ * (scale τ) ^ 12 * tS τ := by ring

private theorem EReg_E4_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, τ ∈ EReg → ‖Work.Kernels.E4Fun τ‖ ≤ C * (scale τ) ^ 12 := by
  obtain ⟨C₅, hC₅, h5⟩ := Work.Residues.ThetaDecay.2.2.2.2.1
  refine ⟨C₅ + 1, by linarith, fun τ hτ => ?_⟩
  have hw1 : (1 : ℝ) ≤ (ModularGroup.S • τ).im := le_trans (by norm_num) hτ
  have hb : ‖Work.Kernels.E4Fun (ModularGroup.S • τ)‖ ≤ 1 + C₅ * tS τ ^ 2 := by
    have h := h5 _ hw1
    rw [exptS] at h
    calc ‖Work.Kernels.E4Fun (ModularGroup.S • τ)‖
        = ‖(Work.Kernels.E4Fun (ModularGroup.S • τ) - 1) + 1‖ := by ring_nf
      _ ≤ ‖Work.Kernels.E4Fun (ModularGroup.S • τ) - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ C₅ * tS τ ^ 2 + 1 := by rw [norm_one]; exact add_le_add h le_rfl
      _ = 1 + C₅ * tS τ ^ 2 := by ring
  have hn : ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖ ≤ scale τ := EReg_norm_coe_S_le_scale τ
  rw [EReg_E4_S τ]
  have h2 : ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖ ^ 4 ≤ (scale τ) ^ 12 :=
    le_trans (pow_le_pow_left₀ (norm_nonneg _) hn 4) (scale_nat_pow_le (by norm_num) τ)
  have ht2 : tS τ ^ 2 ≤ 1 := by nlinarith [tS_nonneg τ, tS_le_one τ]
  have h3 : (1 : ℝ) + C₅ * tS τ ^ 2 ≤ 1 + C₅ := by linarith [mul_le_of_le_one_right hC₅.le ht2]
  calc ‖(((ModularGroup.S • τ : ℍ)) : ℂ) ^ 4 * Work.Kernels.E4Fun (ModularGroup.S • τ)‖
      = ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖ ^ 4 * ‖Work.Kernels.E4Fun (ModularGroup.S • τ)‖ := by
        rw [norm_mul, norm_pow]
    _ ≤ ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖ ^ 4 * (1 + C₅ * tS τ ^ 2) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ (scale τ) ^ 12 * (1 + C₅) :=
        mul_le_mul h2 h3 (by positivity) (by positivity)
    _ = (C₅ + 1) * (scale τ) ^ 12 := by ring

private theorem EReg_E6_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, τ ∈ EReg → ‖Work.Kernels.E6Fun τ‖ ≤ C * (scale τ) ^ 12 := by
  obtain ⟨C₆, hC₆, h6⟩ := Work.Residues.ThetaDecay.2.2.2.2.2
  refine ⟨C₆ + 1, by linarith, fun τ hτ => ?_⟩
  have hw1 : (1 : ℝ) ≤ (ModularGroup.S • τ).im := le_trans (by norm_num) hτ
  have hb : ‖Work.Kernels.E6Fun (ModularGroup.S • τ)‖ ≤ 1 + C₆ * tS τ ^ 2 := by
    have h := h6 _ hw1
    rw [exptS] at h
    calc ‖Work.Kernels.E6Fun (ModularGroup.S • τ)‖
        = ‖(Work.Kernels.E6Fun (ModularGroup.S • τ) - 1) + 1‖ := by ring_nf
      _ ≤ ‖Work.Kernels.E6Fun (ModularGroup.S • τ) - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ C₆ * tS τ ^ 2 + 1 := by rw [norm_one]; exact add_le_add h le_rfl
      _ = 1 + C₆ * tS τ ^ 2 := by ring
  have hn : ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖ ≤ scale τ := EReg_norm_coe_S_le_scale τ
  rw [EReg_E6_S τ]
  have h2 : ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖ ^ 6 ≤ (scale τ) ^ 12 :=
    le_trans (pow_le_pow_left₀ (norm_nonneg _) hn 6) (scale_nat_pow_le (by norm_num) τ)
  have ht2 : tS τ ^ 2 ≤ 1 := by nlinarith [tS_nonneg τ, tS_le_one τ]
  have h3 : (1 : ℝ) + C₆ * tS τ ^ 2 ≤ 1 + C₆ := by linarith [mul_le_of_le_one_right hC₆.le ht2]
  calc ‖(((ModularGroup.S • τ : ℍ)) : ℂ) ^ 6 * Work.Kernels.E6Fun (ModularGroup.S • τ)‖
      = ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖ ^ 6 * ‖Work.Kernels.E6Fun (ModularGroup.S • τ)‖ := by
        rw [norm_mul, norm_pow]
    _ ≤ ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖ ^ 6 * (1 + C₆ * tS τ ^ 2) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ (scale τ) ^ 12 * (1 + C₆) :=
        mul_le_mul h2 h3 (by positivity) (by positivity)
    _ = (C₆ + 1) * (scale τ) ^ 12 := by ring

private theorem EReg_Delta_upper :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, τ ∈ EReg →
      ‖Work.Kernels.DeltaFun τ‖ ≤ C * (scale τ) ^ 12 * tS τ ^ 2 := by
  refine ⟨2, by norm_num, fun τ hτ => ?_⟩
  have hw1 : (1 : ℝ) ≤ (ModularGroup.S • τ).im := le_trans (by norm_num) hτ
  have hb : ‖Work.Kernels.DeltaFun (ModularGroup.S • τ)‖ ≤ 2 * tS τ ^ 2 := by
    have h := DeltaFun_upper_sharp _ hw1
    rwa [exptS] at h
  have hn : ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖ ≤ scale τ := EReg_norm_coe_S_le_scale τ
  rw [EReg_Delta_S τ, norm_mul, norm_pow]
  have h2 : ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖ ^ 12 ≤ (scale τ) ^ 12 :=
    pow_le_pow_left₀ (norm_nonneg _) hn 12
  calc ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖ ^ 12
        * ‖Work.Kernels.DeltaFun (ModularGroup.S • τ)‖
      ≤ ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖ ^ 12 * (2 * tS τ ^ 2) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ (scale τ) ^ 12 * (2 * tS τ ^ 2) :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = 2 * (scale τ) ^ 12 * tS τ ^ 2 := by ring

private theorem EReg_Delta_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ τ : ℍ, τ ∈ EReg →
      c * tS τ ^ 2 ≤ ‖Work.Kernels.DeltaFun τ‖ := by
  obtain ⟨cΔ, hcΔ, hΔ⟩ := Work.Asymptotics.DeltaFun_lower
  refine ⟨(3 / 2 : ℝ) ^ 12 * cΔ, by positivity, fun τ hτ => ?_⟩
  have hw1 : (1 : ℝ) ≤ (ModularGroup.S • τ).im := le_trans (by norm_num) hτ
  have hb : cΔ * tS τ ^ 2 ≤ ‖Work.Kernels.DeltaFun (ModularGroup.S • τ)‖ := by
    have h := hΔ _ hw1
    rw [show ‖Work.Kernels.qParamFun (ModularGroup.S • τ)‖ = tS τ ^ 2 from
      (EReg_tpar_S_sq_eq τ).symm] at h
    exact h
  have hn : (3 / 2 : ℝ) ≤ ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖ := EReg_norm_S_ge τ hτ
  have h12 : (3 / 2 : ℝ) ^ 12 ≤ ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖ ^ 12 :=
    pow_le_pow_left₀ (by norm_num) hn 12
  rw [EReg_Delta_S τ, norm_mul, norm_pow]
  calc (3 / 2 : ℝ) ^ 12 * cΔ * tS τ ^ 2
      = (3 / 2 : ℝ) ^ 12 * (cΔ * tS τ ^ 2) := by ring
    _ ≤ ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖ ^ 12
          * ‖Work.Kernels.DeltaFun (ModularGroup.S • τ)‖ :=
        mul_le_mul h12 hb (by positivity) (by positivity)

private theorem EReg_L_bound (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, τ ∈ EReg →
      ‖ℓ.L τ‖ ≤ C * (scale τ) ^ 12 * tS τ := by
  obtain ⟨CΛ, hCΛ, hΛ⟩ := Work.Residues.LamSExpBound
  refine ⟨CΛ, hCΛ, fun τ hτ => ?_⟩
  have hw1 : (1 : ℝ) ≤ (ModularGroup.S • τ).im := le_trans (by norm_num) hτ
  have hwhalf : (1 / 2 : ℝ) < (ModularGroup.S • τ).im := by linarith
  have hLS : ℓ.L_S (ModularGroup.S • τ)
      = Work.Kernels.LogLambda.LamS (((ModularGroup.S • τ : ℍ)) : ℂ) :=
    Work.Residues.LogLambdaData_LS_eq_LamS ℓ _ hwhalf
  have hmem : (((ModularGroup.S • τ : ℍ)) : ℂ) ∈ Work.Kernels.LogLambda.W := hwhalf
  have hb := hΛ _ hmem (by simpa using hw1)
  rw [EReg_L_S ℓ τ, hLS]
  have hb' : ‖Work.Kernels.LogLambda.LamS (((ModularGroup.S • τ : ℍ)) : ℂ)‖ ≤ CΛ * tS τ := hb
  refine le_trans hb' ?_
  have h1 : (1 : ℝ) ≤ (scale τ) ^ 12 := one_le_pow₀ (Work.Kernels.one_le_scale τ)
  calc CΛ * tS τ = CΛ * 1 * tS τ := by ring
    _ ≤ CΛ * (scale τ) ^ 12 * tS τ := by
        refine mul_le_mul_of_nonneg_right ?_ (tS_nonneg τ)
        exact mul_le_mul_of_nonneg_left h1 hCΛ.le

private theorem EReg_LS_bound (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : ℍ, τ ∈ EReg →
      ‖ℓ.L_S τ‖ ≤ C * (scale τ) ^ N := by
  obtain ⟨α, N, hα, hN, hb⟩ :=
    (Work.Kernels.moderateGrowthOn_iff_scale Set.univ ℓ.L_S).mp ℓ.memP_S
  refine ⟨α + 1, N, by linarith, hN, fun τ _ => ?_⟩
  have h := hb τ (Set.mem_univ τ)
  have h2 : (0 : ℝ) ≤ (scale τ) ^ N := rpow_nonneg' τ N
  linarith [h, h2]

private theorem EReg_j_mul_tpar_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, τ ∈ EReg →
      ‖Work.Kernels.jInvariantFun τ‖ * tS τ ^ 2 ≤ C * (scale τ) ^ 0 := by
  obtain ⟨C₅, hC₅, h5⟩ := Work.Residues.ThetaDecay.2.2.2.2.1
  obtain ⟨cΔ, hcΔ, hΔ⟩ := Work.Asymptotics.DeltaFun_lower
  refine ⟨(1 + C₅) ^ 3 / cΔ + 1, by positivity, fun τ hτ => ?_⟩
  have hw1 : (1 : ℝ) ≤ (ModularGroup.S • τ).im := le_trans (by norm_num) hτ
  have hj : Work.Kernels.jInvariantFun τ = Work.Kernels.jInvariantFun (ModularGroup.S • τ) :=
    (Work.Kernels.KernelFacts.jInvariantFun_S_smul τ).symm
  have hE4b : ‖Work.Kernels.E4Fun (ModularGroup.S • τ)‖ ≤ 1 + C₅ * tS τ ^ 2 := by
    have h := h5 _ hw1
    rw [exptS] at h
    calc ‖Work.Kernels.E4Fun (ModularGroup.S • τ)‖
        = ‖(Work.Kernels.E4Fun (ModularGroup.S • τ) - 1) + 1‖ := by ring_nf
      _ ≤ ‖Work.Kernels.E4Fun (ModularGroup.S • τ) - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ C₅ * tS τ ^ 2 + 1 := by rw [norm_one]; exact add_le_add h le_rfl
      _ = 1 + C₅ * tS τ ^ 2 := by ring
  have ht2 : tS τ ^ 2 ≤ 1 := by nlinarith [tS_nonneg τ, tS_le_one τ]
  have hE4b' : ‖Work.Kernels.E4Fun (ModularGroup.S • τ)‖ ≤ 1 + C₅ := by
    linarith [mul_le_of_le_one_right hC₅.le ht2]
  have hΔb : cΔ * tS τ ^ 2 ≤ ‖Work.Kernels.DeltaFun (ModularGroup.S • τ)‖ := by
    have h := hΔ _ hw1
    rw [show ‖Work.Kernels.qParamFun (ModularGroup.S • τ)‖ = tS τ ^ 2 from
      (EReg_tpar_S_sq_eq τ).symm] at h
    exact h
  have hcden : 0 < cΔ * tS τ ^ 2 := mul_pos hcΔ (pow_pos (tS_pos τ) 2)
  have hden : 0 < ‖Work.Kernels.DeltaFun (ModularGroup.S • τ)‖ := lt_of_lt_of_le hcden hΔb
  have hstep : ‖Work.Kernels.jInvariantFun (ModularGroup.S • τ)‖
      ≤ (1 + C₅) ^ 3 / (cΔ * tS τ ^ 2) := by
    rw [show Work.Kernels.jInvariantFun (ModularGroup.S • τ)
        = Work.Kernels.E4Fun (ModularGroup.S • τ) ^ 3
          / Work.Kernels.DeltaFun (ModularGroup.S • τ) from rfl, norm_div, norm_pow]
    rw [div_le_iff₀ hden]
    calc ‖Work.Kernels.E4Fun (ModularGroup.S • τ)‖ ^ 3 ≤ (1 + C₅) ^ 3 :=
          pow_le_pow_left₀ (norm_nonneg _) hE4b' 3
      _ = (1 + C₅) ^ 3 / (cΔ * tS τ ^ 2) * (cΔ * tS τ ^ 2) :=
          (div_mul_cancel₀ _ (ne_of_gt hcden)).symm
      _ ≤ (1 + C₅) ^ 3 / (cΔ * tS τ ^ 2) * ‖Work.Kernels.DeltaFun (ModularGroup.S • τ)‖ :=
          mul_le_mul_of_nonneg_left hΔb (by positivity)
  have hfinal : ‖Work.Kernels.jInvariantFun (ModularGroup.S • τ)‖ * tS τ ^ 2
      ≤ (1 + C₅) ^ 3 / cΔ := by
    calc ‖Work.Kernels.jInvariantFun (ModularGroup.S • τ)‖ * tS τ ^ 2
        ≤ (1 + C₅) ^ 3 / (cΔ * tS τ ^ 2) * tS τ ^ 2 :=
          mul_le_mul_of_nonneg_right hstep (by positivity)
      _ = (1 + C₅) ^ 3 / cΔ := by
          rw [div_mul_eq_mul_div,
            mul_div_mul_right _ _ (ne_of_gt (pow_pos (tS_pos τ) 2))]
  have h2 : (0 : ℝ) < (1 + C₅) ^ 3 / cΔ := by positivity
  rw [pow_zero, mul_one, hj]
  linarith [hfinal, h2]

private theorem EReg_jDelta_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ τ : ℍ, τ ∈ EReg →
      ‖Work.Kernels.jInvariantFun τ * Work.Kernels.DeltaFun τ‖ ≤ C * (scale τ) ^ 36 := by
  obtain ⟨C, hC, hE4⟩ := EReg_E4_bound
  refine ⟨C ^ 3 + 1, by positivity, fun τ hτ => ?_⟩
  have h1 : ‖Work.Kernels.E4Fun τ‖ ^ 3 ≤ C ^ 3 * (scale τ) ^ 36 := by
    calc ‖Work.Kernels.E4Fun τ‖ ^ 3 ≤ (C * (scale τ) ^ 12) ^ 3 :=
          pow_le_pow_left₀ (norm_nonneg _) (hE4 τ hτ) 3
      _ = C ^ 3 * ((scale τ) ^ 12) ^ 3 := by rw [mul_pow]
      _ = C ^ 3 * (scale τ) ^ 36 := by rw [← pow_mul]
  calc ‖Work.Kernels.jInvariantFun τ * Work.Kernels.DeltaFun τ‖ = ‖Work.Kernels.E4Fun τ‖ ^ 3 := by
        rw [mul_comm (Work.Kernels.jInvariantFun τ) (Work.Kernels.DeltaFun τ),
          Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun τ, norm_pow]
    _ ≤ C ^ 3 * (scale τ) ^ 36 := h1
    _ ≤ (C ^ 3 + 1) * (scale τ) ^ 36 := by
        have h4 : (0 : ℝ) ≤ (scale τ) ^ 36 := by positivity
        nlinarith [h4, hC]

theorem EReg_atom_bounds (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ τ : UpperHalfPlane, τ ∈ Work.Asymptotics.EReg →
      ‖Work.Kernels.UFun τ‖ ≤ C * (Work.Kernels.scale τ) ^ N ∧
      ‖Work.Kernels.VFun τ‖ ≤ C * (Work.Kernels.scale τ) ^ N ∧
      ‖Work.Kernels.WFun τ‖
        ≤ C * (Work.Kernels.scale τ) ^ N * Work.Residues.tpar (ModularGroup.S • τ) ∧
      ‖Work.Kernels.E4Fun τ‖ ≤ C * (Work.Kernels.scale τ) ^ N ∧
      ‖Work.Kernels.E6Fun τ‖ ≤ C * (Work.Kernels.scale τ) ^ N ∧
      ‖Work.Kernels.DeltaFun τ‖
        ≤ C * (Work.Kernels.scale τ) ^ N * Work.Residues.tpar (ModularGroup.S • τ) ^ 2 ∧
      C⁻¹ * (Work.Kernels.scale τ) ^ (-N) * Work.Residues.tpar (ModularGroup.S • τ) ^ 2
        ≤ ‖Work.Kernels.DeltaFun τ‖ ∧
      ‖ℓ.L τ‖ ≤ C * (Work.Kernels.scale τ) ^ N * Work.Residues.tpar (ModularGroup.S • τ) ∧
      ‖ℓ.L_S τ‖ ≤ C * (Work.Kernels.scale τ) ^ N ∧
      ‖Work.Kernels.jInvariantFun τ‖ * Work.Residues.tpar (ModularGroup.S • τ) ^ 2
        ≤ C * (Work.Kernels.scale τ) ^ N ∧
      ‖Work.Kernels.jInvariantFun τ * Work.Kernels.DeltaFun τ‖ ≤ C * (Work.Kernels.scale τ) ^ N := by
  obtain ⟨c1, hc1, hU⟩ := EReg_U_bound
  obtain ⟨c2, hc2, hV⟩ := EReg_V_bound
  obtain ⟨c3, hc3, hW⟩ := EReg_W_bound
  obtain ⟨c4, hc4, hE4⟩ := EReg_E4_bound
  obtain ⟨c5, hc5, hE6⟩ := EReg_E6_bound
  obtain ⟨c6, hc6, hΔu⟩ := EReg_Delta_upper
  obtain ⟨c7, hc7, hΔl⟩ := EReg_Delta_lower
  obtain ⟨c8, hc8, hL⟩ := EReg_L_bound ℓ
  obtain ⟨c9, η, hc9, hη, hLS⟩ := EReg_LS_bound ℓ
  obtain ⟨c10, hc10, hj⟩ := EReg_j_mul_tpar_bound
  obtain ⟨c11, hc11, hjΔ⟩ := EReg_jDelta_bound
  set C : ℝ := c1 + c2 + c3 + c4 + c5 + c6 + c7⁻¹ + c8 + c9 + c10 + c11 + 1 with hC
  set N : ℝ := η + 40 with hN
  have hCpos : 0 < C := by rw [hC]; positivity
  have hNnonneg : 0 ≤ N := by rw [hN]; linarith
  have hN12 : (12 : ℝ) ≤ N := by rw [hN]; linarith
  have hN36 : (36 : ℝ) ≤ N := by rw [hN]; linarith
  have hNη : η ≤ N := by rw [hN]; linarith
  have hc7inv : (0 : ℝ) ≤ c7⁻¹ := inv_nonneg.mpr hc7.le
  have hc1C : c1 ≤ C := by rw [hC]; nlinarith [hc2.le, hc3.le, hc4.le, hc5.le, hc6.le,
    hc7inv, hc8.le, hc9.le, hc10.le, hc11.le]
  have hc2C : c2 ≤ C := by rw [hC]; nlinarith [hc1.le, hc3.le, hc4.le, hc5.le, hc6.le,
    hc7inv, hc8.le, hc9.le, hc10.le, hc11.le]
  have hc3C : c3 ≤ C := by rw [hC]; nlinarith [hc1.le, hc2.le, hc4.le, hc5.le, hc6.le,
    hc7inv, hc8.le, hc9.le, hc10.le, hc11.le]
  have hc4C : c4 ≤ C := by rw [hC]; nlinarith [hc1.le, hc2.le, hc3.le, hc5.le, hc6.le,
    hc7inv, hc8.le, hc9.le, hc10.le, hc11.le]
  have hc5C : c5 ≤ C := by rw [hC]; nlinarith [hc1.le, hc2.le, hc3.le, hc4.le, hc6.le,
    hc7inv, hc8.le, hc9.le, hc10.le, hc11.le]
  have hc6C : c6 ≤ C := by rw [hC]; nlinarith [hc1.le, hc2.le, hc3.le, hc4.le, hc5.le,
    hc7inv, hc8.le, hc9.le, hc10.le, hc11.le]
  have hc8C : c8 ≤ C := by rw [hC]; nlinarith [hc1.le, hc2.le, hc3.le, hc4.le, hc5.le,
    hc6.le, hc7inv, hc9.le, hc10.le, hc11.le]
  have hc9C : c9 ≤ C := by rw [hC]; nlinarith [hc1.le, hc2.le, hc3.le, hc4.le, hc5.le,
    hc6.le, hc7inv, hc8.le, hc10.le, hc11.le]
  have hc10C : c10 ≤ C := by rw [hC]; nlinarith [hc1.le, hc2.le, hc3.le, hc4.le, hc5.le,
    hc6.le, hc7inv, hc8.le, hc9.le, hc11.le]
  have hc11C : c11 ≤ C := by rw [hC]; nlinarith [hc1.le, hc2.le, hc3.le, hc4.le, hc5.le,
    hc6.le, hc7inv, hc8.le, hc9.le, hc10.le]
  have hCinv : C⁻¹ ≤ c7 := by
    rw [inv_le_iff_one_le_mul₀ hCpos]
    have h1 : c7⁻¹ ≤ C := by rw [hC]; nlinarith [hc1.le, hc2.le, hc3.le, hc4.le, hc5.le,
      hc6.le, hc8.le, hc9.le, hc10.le, hc11.le]
    have h2 : c7⁻¹ * c7 = 1 := inv_mul_cancel₀ (ne_of_gt hc7)
    nlinarith [mul_le_mul_of_nonneg_right h1 hc7.le, h2]
  refine ⟨C, N, hCpos, hNnonneg, fun τ hτ => ?_⟩
  have ht0 : 0 < tS τ := tS_pos τ
  have hNneg : (Work.Kernels.scale τ) ^ (-N) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (Work.Kernels.one_le_scale τ) (by linarith)
  have hNpos : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ (-N) := rpow_nonneg' τ (-N)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact le_trans (hU τ hτ) (atom_mono_nat hc1C hN12 hCpos.le)
  · exact le_trans (hV τ hτ) (atom_mono_nat hc2C hN12 hCpos.le)
  · have h := hW τ hτ
    calc ‖Work.Kernels.WFun τ‖ ≤ c3 * (scale τ) ^ 12 * tS τ := h
      _ = (c3 * (scale τ) ^ 12) * tS τ := by ring
      _ ≤ (C * (scale τ) ^ N) * tS τ :=
          mul_le_mul_of_nonneg_right (atom_mono_nat hc3C hN12 hCpos.le) ht0.le
      _ = C * (scale τ) ^ N * tS τ := by ring
  · exact le_trans (hE4 τ hτ) (atom_mono_nat hc4C hN12 hCpos.le)
  · exact le_trans (hE6 τ hτ) (atom_mono_nat hc5C hN12 hCpos.le)
  · have h := hΔu τ hτ
    calc ‖Work.Kernels.DeltaFun τ‖ ≤ c6 * (scale τ) ^ 12 * tS τ ^ 2 := h
      _ = (c6 * (scale τ) ^ 12) * tS τ ^ 2 := by ring
      _ ≤ (C * (scale τ) ^ N) * tS τ ^ 2 :=
          mul_le_mul_of_nonneg_right (atom_mono_nat hc6C hN12 hCpos.le) (by positivity)
      _ = C * (scale τ) ^ N * tS τ ^ 2 := by ring
  · have h := hΔl τ hτ
    have h1 : C⁻¹ * (scale τ) ^ (-N) ≤ c7 := by
      have h := mul_le_mul hCinv hNneg hNpos hc7.le
      rwa [mul_one] at h
    calc C⁻¹ * (Work.Kernels.scale τ) ^ (-N) * tS τ ^ 2
        = (C⁻¹ * (scale τ) ^ (-N)) * tS τ ^ 2 := by ring
      _ ≤ c7 * tS τ ^ 2 := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ ‖Work.Kernels.DeltaFun τ‖ := h
  · have h := hL τ hτ
    calc ‖ℓ.L τ‖ ≤ c8 * (scale τ) ^ 12 * tS τ := h
      _ = (c8 * (scale τ) ^ 12) * tS τ := by ring
      _ ≤ (C * (scale τ) ^ N) * tS τ :=
          mul_le_mul_of_nonneg_right (atom_mono_nat hc8C hN12 hCpos.le) ht0.le
      _ = C * (scale τ) ^ N * tS τ := by ring
  · exact le_trans (hLS τ hτ) (atom_mono_rpow hc9C hNη hCpos.le)
  · have h := hj τ hτ
    rw [pow_zero, mul_one] at h
    calc ‖Work.Kernels.jInvariantFun τ‖ * tS τ ^ 2 ≤ c10 := h
      _ = c10 * 1 := by ring
      _ ≤ C * (scale τ) ^ N :=
          mul_le_mul hc10C (Real.one_le_rpow (Work.Kernels.one_le_scale τ) hNnonneg)
            zero_le_one hCpos.le
  · exact le_trans (hjΔ τ hτ) (atom_mono_nat hc11C hN36 hCpos.le)

end Work.Asymptotics
