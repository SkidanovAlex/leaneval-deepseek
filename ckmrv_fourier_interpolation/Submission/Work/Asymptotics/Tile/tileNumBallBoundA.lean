import Mathlib
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.Compact.tailDefs
import Submission.Work.Asymptotics.Compact.kminus_tail_core
import Submission.Work.Asymptotics.Compact.gfun_eq
import Submission.Work.Asymptotics.EBase
import Submission.Work.Asymptotics.TileDevBall.kplusDev8Ball
import Submission.Work.Asymptotics.TileDevBall.kplusDev24Ball
import Submission.Work.Asymptotics.TileDevBall.bracket8Ball
import Submission.Work.Asymptotics.TileDevBall.bracket24Ball
import Submission.Work.Asymptotics.TileDevBall.tileNumBallSmallA

namespace Work.Asymptotics.Tile

open UpperHalfPlane ModularGroup
open scoped MatrixGroups UpperHalfPlane

/-! ## Geometry of the ball `‖ζ - S • w‖ ≤ 29/20` on `E = KEpsilon` -/

/-- `(S • w).im = w.im / ‖w‖²`. -/
private lemma im_S_smul (w : ℍ) :
    (ModularGroup.S • w).im = w.im / ‖(w : ℂ)‖ ^ 2 := by
  have hcoe : ((ModularGroup.S • w : ℍ) : ℂ) = -((w : ℂ))⁻¹ := Work.Kernels.S_smul_coe w
  rw [← UpperHalfPlane.coe_im, hcoe, Complex.neg_im, Complex.inv_im,
    Complex.normSq_eq_norm_sq, UpperHalfPlane.coe_im]
  ring

/-- `|w.re| < ‖w‖²` on `𝒟`. -/
private lemma abs_re_lt_normSq {w : ℍ} (hw : w ∈ Work.Asymptotics.DomainD) :
    |w.re| < ‖(w : ℂ)‖ ^ 2 := by
  obtain ⟨hre1, hre2, hc1, hc2⟩ := hw
  have hs : ‖(w : ℂ)‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp; ring
  have h1 : (1 / 2 : ℝ) ^ 2 < (w.re - 1 / 2) ^ 2 + w.im ^ 2 := by
    have hsq : (1 / 2 : ℝ) ^ 2 < Complex.normSq ((w : ℂ) - (1 / 2 : ℂ)) := by
      rw [Complex.normSq_eq_norm_sq]
      nlinarith [norm_nonneg ((w : ℂ) - (1 / 2 : ℂ)), hc1]
    rw [Complex.normSq_apply] at hsq
    simp at hsq
    nlinarith [hsq]
  have h2 : (1 / 2 : ℝ) ^ 2 < (w.re + 1 / 2) ^ 2 + w.im ^ 2 := by
    have hsq : (1 / 2 : ℝ) ^ 2 < Complex.normSq ((w : ℂ) + (1 / 2 : ℂ)) := by
      rw [Complex.normSq_eq_norm_sq]
      nlinarith [norm_nonneg ((w : ℂ) + (1 / 2 : ℂ)), hc2]
    rw [Complex.normSq_apply] at hsq
    simp at hsq
    nlinarith [hsq]
  rw [abs_lt, hs]
  constructor <;> nlinarith [h1, h2]


/-- **`Im ζ < 3` forces `scale w ≤ 8`** on the tile ball. -/
private lemma scale_le_eight_of_im_lt (w ζ : ℍ) (hw : w ∈ Work.Asymptotics.KEpsilon)
    (hζ : ‖(ζ : ℂ) - (((ModularGroup.S • w : ℍ)) : ℂ)‖ ≤ 29 / 20) (h3 : ζ.im < 3) :
    Work.Kernels.scale w ≤ 8 := by
  have hwD : w ∈ Work.Asymptotics.DomainD := Work.Asymptotics.KEpsilon_subset_DomainD hw
  have him : |ζ.im - (ModularGroup.S • w).im| ≤ 29 / 20 := by
    have h := Complex.abs_im_le_norm ((ζ : ℂ) - (((ModularGroup.S • w : ℍ)) : ℂ))
    have h2 : ((ζ : ℂ) - (((ModularGroup.S • w : ℍ)) : ℂ)).im =
        ζ.im - (ModularGroup.S • w).im := by
      rw [Complex.sub_im, UpperHalfPlane.coe_im, UpperHalfPlane.coe_im]
    rw [h2] at h
    exact le_trans h hζ
  have hσlt : (ModularGroup.S • w).im < 4.45 := by
    have h := (abs_le.mp him).1
    nlinarith [h, h3]
  have hs : ‖(w : ℂ)‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp; ring
  have hre : |w.re| < ‖(w : ℂ)‖ ^ 2 := abs_re_lt_normSq hwD
  have hsq0 : (0 : ℝ) < ‖(w : ℂ)‖ ^ 2 := lt_of_le_of_lt (abs_nonneg w.re) hre
  have hnorm_le : ‖(w : ℂ)‖ ≤ 1 / 2 := Work.Asymptotics.E_norm_le_half hw
  have hkey : w.im ^ 2 > ‖(w : ℂ)‖ ^ 2 * (3 / 4) := by
    have h1 : w.re ^ 2 < (‖(w : ℂ)‖ ^ 2) ^ 2 := by
      have h2 : |w.re| < ‖(w : ℂ)‖ ^ 2 := hre
      nlinarith [sq_abs w.re, hsq0, h2, abs_nonneg w.re]
    have h4 : ‖(w : ℂ)‖ ^ 2 ≤ 1 / 4 := by nlinarith [norm_nonneg (w : ℂ)]
    rw [hs] at h1 h4 ⊢
    nlinarith [h1, h4]
  have hσeq : (ModularGroup.S • w).im = w.im / ‖(w : ℂ)‖ ^ 2 := im_S_smul w
  have h2 : w.im < 4.45 * ‖(w : ℂ)‖ ^ 2 := by
    have h1 : w.im / ‖(w : ℂ)‖ ^ 2 < 4.45 := by rw [← hσeq]; exact hσlt
    have h := mul_lt_mul_of_pos_right h1 hsq0
    rw [div_mul_cancel₀ _ (ne_of_gt hsq0)] at h
    linarith [h]
  have hwi : (3 : ℝ) < w.im * (4 * 4.45) := by nlinarith [h2, hkey, w.im_pos, hsq0]
  have hinv : (w.im)⁻¹ ≤ 4 * 4.45 / 3 := by
    rw [inv_le_iff_one_le_mul₀ w.im_pos]
    nlinarith [hwi]
  rw [Work.Kernels.scale]
  linarith [hnorm_le, hinv]


/-! ## The algebraic splitting of the target -/

/-- `2 · Sh · (Kfun − Gfun) = Sh · (K⁺ − 𝒢⁺) + Sh · (K⁻ − 𝒢⁻)`. -/
private lemma two_Sh_mul (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ ζ : UpperHalfPlane) :
    2 * (Work.Asymptotics.Compact.Sh τ ζ
          * (Work.Kernels.Kfun ℓ d τ ζ - Work.Asymptotics.Compact.Gfun d ℓ τ ζ))
      = Work.Asymptotics.Compact.Sh τ ζ
          * (Work.Kernels.KPlus d τ ζ - Work.Asymptotics.Compact.Gplus d τ ζ)
        + Work.Asymptotics.Compact.Sh τ ζ
          * (Work.Kernels.KMinus ℓ d τ ζ - Work.Asymptotics.Compact.Gminus d ℓ τ ζ) := by
  have h := Work.Asymptotics.Compact.gfun_eq ℓ d hd τ ζ
  have hG : Work.Asymptotics.Compact.Gfun d ℓ τ ζ
      = (Work.Asymptotics.Compact.Gplus d τ ζ + Work.Asymptotics.Compact.Gminus d ℓ τ ζ) / 2 := by
    rw [eq_div_iff (by norm_num : (2 : ℂ) ≠ 0), mul_comm]
    exact h.symm
  rw [Work.Kernels.Kfun, hG]
  ring

/-- `‖Sh · (K⁻ − 𝒢⁻)‖ ≤ ‖brMinus + Sh · br0‖ / (3456π)`. -/
private lemma norm_Sh_KMinus_le (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ ζ : UpperHalfPlane) :
    ‖Work.Asymptotics.Compact.Sh τ ζ
        * (Work.Kernels.KMinus ℓ d τ ζ - Work.Asymptotics.Compact.Gminus d ℓ τ ζ)‖
      ≤ (1 / (3456 * Real.pi)) *
          ‖Work.Asymptotics.Compact.brMinus ℓ d τ ζ
            + Work.Asymptotics.Compact.Sh τ ζ * Work.Asymptotics.Compact.br0 d ℓ τ ζ‖ := by
  by_cases hS : Work.Asymptotics.Compact.Sh τ ζ = 0
  · rw [hS, zero_mul, norm_zero]
    positivity
  · have hid := Work.Asymptotics.Compact.tail_identity ℓ d hd τ ζ hS
    have hC : ‖((3456 : ℂ) * (Real.pi : ℂ))‖ = 3456 * Real.pi := by
      rw [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
    have h2 : ((3456 : ℂ) * (Real.pi : ℂ))
        * (Work.Asymptotics.Compact.Sh τ ζ
            * (Work.Kernels.KMinus ℓ d τ ζ - Work.Asymptotics.Compact.Gminus d ℓ τ ζ))
        = -((Work.Asymptotics.Compact.brMinus ℓ d τ ζ
            + Work.Asymptotics.Compact.Sh τ ζ * Work.Asymptotics.Compact.br0 d ℓ τ ζ)) := by
      calc ((3456 : ℂ) * (Real.pi : ℂ))
            * (Work.Asymptotics.Compact.Sh τ ζ
              * (Work.Kernels.KMinus ℓ d τ ζ - Work.Asymptotics.Compact.Gminus d ℓ τ ζ))
          = Work.Asymptotics.Compact.Sh τ ζ * (((3456 : ℂ) * (Real.pi : ℂ))
              * (Work.Kernels.KMinus ℓ d τ ζ - Work.Asymptotics.Compact.Gminus d ℓ τ ζ)) := by
              ring
        _ = Work.Asymptotics.Compact.Sh τ ζ
              * (-((Work.Asymptotics.Compact.Sh τ ζ)⁻¹
                  * (Work.Asymptotics.Compact.brMinus ℓ d τ ζ
                    + Work.Asymptotics.Compact.Sh τ ζ * Work.Asymptotics.Compact.br0 d ℓ τ ζ))) := by
              rw [hid]
        _ = -((Work.Asymptotics.Compact.brMinus ℓ d τ ζ
              + Work.Asymptotics.Compact.Sh τ ζ * Work.Asymptotics.Compact.br0 d ℓ τ ζ)) := by
              rw [mul_neg, ← mul_assoc, mul_inv_cancel₀ hS, one_mul]
    have hZnorm : ‖Work.Asymptotics.Compact.Sh τ ζ
        * (Work.Kernels.KMinus ℓ d τ ζ - Work.Asymptotics.Compact.Gminus d ℓ τ ζ)‖
        = ‖Work.Asymptotics.Compact.brMinus ℓ d τ ζ
            + Work.Asymptotics.Compact.Sh τ ζ * Work.Asymptotics.Compact.br0 d ℓ τ ζ‖
          / (3456 * Real.pi) := by
      have h : (3456 * Real.pi) * ‖Work.Asymptotics.Compact.Sh τ ζ
          * (Work.Kernels.KMinus ℓ d τ ζ - Work.Asymptotics.Compact.Gminus d ℓ τ ζ)‖
          = ‖Work.Asymptotics.Compact.brMinus ℓ d τ ζ
              + Work.Asymptotics.Compact.Sh τ ζ * Work.Asymptotics.Compact.br0 d ℓ τ ζ‖ := by
        rw [← hC, ← norm_mul, h2, norm_neg]
      rw [eq_div_iff (by positivity : (3456 * Real.pi) ≠ 0)]
      linarith [h]
    rw [hZnorm, div_eq_mul_inv, div_eq_mul_inv]
    exact le_of_eq (by ring)

/-- Combining two `C · (scale w)^N` bounds. -/
private lemma combine_bounds {w : ℍ} {a b C₁ C₂ N₁ N₂ : ℝ} (hN₁ : 0 ≤ N₁) (hN₂ : 0 ≤ N₂)
    (hC₁ : 0 < C₁) (hC₂ : 0 < C₂)
    (h₁ : a ≤ C₁ * (Work.Kernels.scale w) ^ N₁) (h₂ : b ≤ C₂ * (Work.Kernels.scale w) ^ N₂) :
    a + b ≤ (C₁ + C₂) * (Work.Kernels.scale w) ^ (max N₁ N₂) := by
  have hs1 : (1 : ℝ) ≤ Work.Kernels.scale w := Work.Kernels.one_le_scale w
  have hs0 : (0 : ℝ) < Work.Kernels.scale w := Work.Kernels.scale_pos w
  have h1 : (Work.Kernels.scale w) ^ N₁ ≤ (Work.Kernels.scale w) ^ (max N₁ N₂) :=
    Real.rpow_le_rpow_of_exponent_le hs1 (le_max_left _ _)
  have h2 : (Work.Kernels.scale w) ^ N₂ ≤ (Work.Kernels.scale w) ^ (max N₁ N₂) :=
    Real.rpow_le_rpow_of_exponent_le hs1 (le_max_right _ _)
  have h0 : (0 : ℝ) ≤ (Work.Kernels.scale w) ^ (max N₁ N₂) := Real.rpow_nonneg hs0.le _
  calc a + b ≤ C₁ * (Work.Kernels.scale w) ^ N₁ + C₂ * (Work.Kernels.scale w) ^ N₂ :=
        add_le_add h₁ h₂
    _ ≤ C₁ * (Work.Kernels.scale w) ^ (max N₁ N₂)
          + C₂ * (Work.Kernels.scale w) ^ (max N₁ N₂) :=
        add_le_add (mul_le_mul_of_nonneg_left h1 hC₁.le) (mul_le_mul_of_nonneg_left h2 hC₂.le)
    _ = (C₁ + C₂) * (Work.Kernels.scale w) ^ (max N₁ N₂) := by ring

/-- **The main assembly.**  The four half-deviation bounds plus the small-`scale` bound give the
target. -/
private lemma tileNumBallBound_of_pieces (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24)
    (hplus : ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (w : ℍ), w ∈ Work.Asymptotics.KEpsilon →
        ∀ (n : ℤ), (n = 1 ∨ n = -1) → ∀ ζ : ℍ,
          ‖(ζ : ℂ) - (((ModularGroup.S • w : ℍ)) : ℂ)‖ ≤ 29 / 20 → 3 ≤ ζ.im →
          ‖Work.Asymptotics.Compact.Sh ((n : ℝ) +ᵥ w) ζ
            * (Work.Kernels.KPlus d ((n : ℝ) +ᵥ w) ζ
                - Work.Asymptotics.Compact.Gplus d ((n : ℝ) +ᵥ w) ζ)‖
          ≤ C * (Work.Kernels.scale w) ^ N)
    (hminus : ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (w : ℍ), w ∈ Work.Asymptotics.KEpsilon →
        ∀ (n : ℤ), (n = 1 ∨ n = -1) → ∀ ζ : ℍ,
          ‖(ζ : ℂ) - (((ModularGroup.S • w : ℍ)) : ℂ)‖ ≤ 29 / 20 → 3 ≤ ζ.im →
          ‖Work.Asymptotics.Compact.brMinus ℓ d ((n : ℝ) +ᵥ w) ζ
            + Work.Asymptotics.Compact.Sh ((n : ℝ) +ᵥ w) ζ
              * Work.Asymptotics.Compact.br0 d ℓ ((n : ℝ) +ᵥ w) ζ‖
          ≤ C * (Work.Kernels.scale w) ^ N)
    (hsmall : ∃ M : ℝ, 0 < M ∧ ∀ (w : ℍ), w ∈ Work.Asymptotics.KEpsilon →
        Work.Kernels.scale w ≤ 8 → ∀ (n : ℤ), (n = 1 ∨ n = -1) → ∀ ζ : ℍ,
          ‖(ζ : ℂ) - (((ModularGroup.S • w : ℍ)) : ℂ)‖ ≤ 29 / 20 →
          ‖2 * (Work.Asymptotics.Compact.Sh ((n : ℝ) +ᵥ w) ζ
              * (Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) ζ
                  - Work.Asymptotics.Compact.Gfun d ℓ ((n : ℝ) +ᵥ w) ζ))‖ ≤ M) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧
      ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon → ∀ (n : ℤ), (n = 1 ∨ n = -1) →
        ∀ ζ : UpperHalfPlane,
          ‖(ζ : ℂ) - (((ModularGroup.S • w : UpperHalfPlane)) : ℂ)‖ ≤ 29 / 20 →
          ‖2 * (Work.Asymptotics.Compact.Sh ((n : ℝ) +ᵥ w) ζ
              * (Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) ζ
                  - Work.Asymptotics.Compact.Gfun d ℓ ((n : ℝ) +ᵥ w) ζ))‖
            ≤ C * (Work.Kernels.scale w) ^ N := by
  obtain ⟨Cp, Np, hCp, hNp, hp⟩ := hplus
  obtain ⟨Cm, Nm, hCm, hNm, hm⟩ := hminus
  obtain ⟨M, hM, hsm⟩ := hsmall
  refine ⟨max (Cp + Cm / (3456 * Real.pi)) M, max Np Nm,
    lt_max_of_lt_left (by positivity), le_max_of_le_left hNp, ?_⟩
  intro w hw n hn ζ hζ
  have hs1 : (1 : ℝ) ≤ Work.Kernels.scale w := Work.Kernels.one_le_scale w
  have hs0 : (0 : ℝ) < Work.Kernels.scale w := Work.Kernels.scale_pos w
  by_cases h3 : 3 ≤ ζ.im
  · have e1 := hp w hw n hn ζ hζ h3
    have e2 := hm w hw n hn ζ hζ h3
    have e3 : ‖Work.Asymptotics.Compact.Sh ((n : ℝ) +ᵥ w) ζ
        * (Work.Kernels.KMinus ℓ d ((n : ℝ) +ᵥ w) ζ
            - Work.Asymptotics.Compact.Gminus d ℓ ((n : ℝ) +ᵥ w) ζ)‖
        ≤ (Cm / (3456 * Real.pi)) * (Work.Kernels.scale w) ^ Nm := by
      refine le_trans (norm_Sh_KMinus_le ℓ d hd _ _) ?_
      have h := mul_le_mul_of_nonneg_left e2 (by positivity : (0 : ℝ) ≤ 1 / (3456 * Real.pi))
      refine le_trans h (le_of_eq ?_)
      ring
    have hsplit := two_Sh_mul ℓ d hd ((n : ℝ) +ᵥ w) ζ
    have hcm0 : (0 : ℝ) ≤ Cm / (3456 * Real.pi) := by positivity
    have hcomb : Cp * (Work.Kernels.scale w) ^ Np
        + (Cm / (3456 * Real.pi)) * (Work.Kernels.scale w) ^ Nm
        ≤ (Cp + Cm / (3456 * Real.pi)) * (Work.Kernels.scale w) ^ (max Np Nm) := by
      have hp1 : (Work.Kernels.scale w) ^ Np ≤ (Work.Kernels.scale w) ^ (max Np Nm) :=
        Real.rpow_le_rpow_of_exponent_le hs1 (le_max_left _ _)
      have hp2 : (Work.Kernels.scale w) ^ Nm ≤ (Work.Kernels.scale w) ^ (max Np Nm) :=
        Real.rpow_le_rpow_of_exponent_le hs1 (le_max_right _ _)
      have h1 := mul_le_mul_of_nonneg_left hp1 hCp.le
      have h2 := mul_le_mul_of_nonneg_left hp2 hcm0
      have h3 := Real.rpow_nonneg hs0.le (max Np Nm)
      nlinarith [h1, h2, h3]
    have hmono : (Cp + Cm / (3456 * Real.pi)) * (Work.Kernels.scale w) ^ (max Np Nm)
        ≤ max (Cp + Cm / (3456 * Real.pi)) M * (Work.Kernels.scale w) ^ (max Np Nm) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hs0.le _)
    calc ‖2 * (Work.Asymptotics.Compact.Sh ((n : ℝ) +ᵥ w) ζ
            * (Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) ζ
                - Work.Asymptotics.Compact.Gfun d ℓ ((n : ℝ) +ᵥ w) ζ))‖
        = ‖Work.Asymptotics.Compact.Sh ((n : ℝ) +ᵥ w) ζ
              * (Work.Kernels.KPlus d ((n : ℝ) +ᵥ w) ζ
                  - Work.Asymptotics.Compact.Gplus d ((n : ℝ) +ᵥ w) ζ)
            + Work.Asymptotics.Compact.Sh ((n : ℝ) +ᵥ w) ζ
              * (Work.Kernels.KMinus ℓ d ((n : ℝ) +ᵥ w) ζ
                  - Work.Asymptotics.Compact.Gminus d ℓ ((n : ℝ) +ᵥ w) ζ)‖ := by rw [hsplit]
      _ ≤ ‖Work.Asymptotics.Compact.Sh ((n : ℝ) +ᵥ w) ζ
              * (Work.Kernels.KPlus d ((n : ℝ) +ᵥ w) ζ
                  - Work.Asymptotics.Compact.Gplus d ((n : ℝ) +ᵥ w) ζ)‖
            + ‖Work.Asymptotics.Compact.Sh ((n : ℝ) +ᵥ w) ζ
              * (Work.Kernels.KMinus ℓ d ((n : ℝ) +ᵥ w) ζ
                  - Work.Asymptotics.Compact.Gminus d ℓ ((n : ℝ) +ᵥ w) ζ)‖ := norm_add_le _ _
      _ ≤ Cp * (Work.Kernels.scale w) ^ Np
            + (Cm / (3456 * Real.pi)) * (Work.Kernels.scale w) ^ Nm := add_le_add e1 e3
      _ ≤ (Cp + Cm / (3456 * Real.pi)) * (Work.Kernels.scale w) ^ (max Np Nm) := hcomb
      _ ≤ max (Cp + Cm / (3456 * Real.pi)) M * (Work.Kernels.scale w) ^ (max Np Nm) := hmono
  · push_neg at h3
    have hsc : Work.Kernels.scale w ≤ 8 := scale_le_eight_of_im_lt w ζ hw hζ h3
    have e := hsm w hw hsc n hn ζ hζ
    refine le_trans e ?_
    have hone : (1 : ℝ) ≤ (Work.Kernels.scale w) ^ (max Np Nm) :=
      Real.one_le_rpow hs1 (le_max_of_le_left hNp)
    calc M ≤ max (Cp + Cm / (3456 * Real.pi)) M * 1 := by
          rw [mul_one]; exact le_max_right _ _
      _ ≤ max (Cp + Cm / (3456 * Real.pi)) M * (Work.Kernels.scale w) ^ (max Np Nm) :=
          mul_le_mul_of_nonneg_left hone
            (le_trans (by positivity : (0 : ℝ) ≤ Cp + Cm / (3456 * Real.pi)) (le_max_left _ _))


/-! ## The target -/

/-- **The `2 · Sh · (Kfun − Gfun)` ball bound.**  This is the analytic input of the
three-zeros endgame for the resonant strip of the cusp-`±1` tiles
(`Submission/Work/Asymptotics/Tile/tileWindowRestricted_strip.lean`). -/
theorem tileNumBallBoundA (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧
      ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon → ∀ (n : ℤ), (n = 1 ∨ n = -1) →
        ∀ ζ : UpperHalfPlane,
          ‖(ζ : ℂ) - (((ModularGroup.S • w : UpperHalfPlane)) : ℂ)‖ ≤ 29 / 20 →
          ‖2 * (Work.Asymptotics.Compact.Sh ((n : ℝ) +ᵥ w) ζ
              * (Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) ζ
                  - Work.Asymptotics.Compact.Gfun d ℓ ((n : ℝ) +ᵥ w) ζ))‖
            ≤ C * (Work.Kernels.scale w) ^ N := by
  rcases hd with rfl | rfl
  · exact tileNumBallBound_of_pieces ℓ 8 (Or.inl rfl)
      (Work.Asymptotics.TileDevBall.kplusDev8Ball ℓ)
      (Work.Asymptotics.TileDevBall.bracket8Ball ℓ)
      (Work.Asymptotics.TileDevBall.tileNumBallSmallA ℓ 8 (Or.inl rfl))
  · exact tileNumBallBound_of_pieces ℓ 24 (Or.inr rfl)
      (Work.Asymptotics.TileDevBall.kplusDev24Ball ℓ)
      (Work.Asymptotics.TileDevBall.bracket24Ball ℓ)
      (Work.Asymptotics.TileDevBall.tileNumBallSmallA ℓ 24 (Or.inr rfl))

end Work.Asymptotics.Tile
