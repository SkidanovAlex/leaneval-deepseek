import Mathlib
import Submission.Work.CKFinal.LineDecay.Defs
import Submission.Work.CKFinal.LineDecay.PhiAxis
import Submission.Work.CKFinal.LineDecay.Phi_axis_norm_eight
import Submission.Work.CKFinal.LineDecay.Phi_axis_norm_twentyfour
import Submission.Work.CKFinal.LineDecay.KPlus_tail_lines
import Submission.Work.CKFinal.LineDecay.KMinus_tail_lines
import Submission.Work.CKFinal.LineDecay.KPlus_tail_lines_twentyfour
import Submission.Work.CKFinal.LineDecay.KMinus_tail_lines_twentyfour
import Submission.Work.CKFinal.LineDecay.DenomLower_lines
import Submission.Work.CKFinal.LineDecay.DenomLower_lines_two

namespace Work.CKFinal.LineDecay

open UpperHalfPlane

noncomputable section

/-- Monotonicity of the majorant `B s^A (1+t)^A F` in the constant and in the exponents
(the second variable exponent on the left is allowed to be `0`). -/
private lemma majorant_mono {B₁ A₁ B₂ A₂ s u F : ℝ} (hB₁ : 0 ≤ B₁) (hA₂ : 0 ≤ A₂)
    (hB : B₁ ≤ B₂) (hA : A₁ ≤ A₂) (hs : 1 ≤ s) (hu : 1 ≤ u) (hF : 0 ≤ F) :
    B₁ * s ^ A₁ * F ≤ B₂ * s ^ A₂ * u ^ A₂ * F := by
  have hs0 : (0 : ℝ) ≤ s := by linarith
  have hB₂ : (0 : ℝ) ≤ B₂ := le_trans hB₁ hB
  have h1 : B₁ * s ^ A₁ ≤ B₂ * s ^ A₂ :=
    le_trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hs hA) hB₁)
      (mul_le_mul_of_nonneg_right hB (Real.rpow_nonneg hs0 A₂))
  have h2 : B₂ * s ^ A₂ ≤ B₂ * s ^ A₂ * u ^ A₂ :=
    le_mul_of_one_le_right (mul_nonneg hB₂ (Real.rpow_nonneg hs0 A₂))
      (Real.one_le_rpow hu hA₂)
  exact mul_le_mul (le_trans h1 h2) le_rfl hF
    (mul_nonneg (mul_nonneg hB₂ (Real.rpow_nonneg hs0 A₂)) (Real.rpow_nonneg (by linarith) A₂))

/-- Monotonicity of the majorant `B s^A u^A F` in the constant and in the exponents. -/
private lemma majorant_mono₂ {B₁ A₁ B₂ A₂ s u F : ℝ} (hB₁ : 0 ≤ B₁)
    (hB : B₁ ≤ B₂) (hA : A₁ ≤ A₂) (hs : 1 ≤ s) (hu : 1 ≤ u) (hF : 0 ≤ F) :
    B₁ * s ^ A₁ * u ^ A₁ * F ≤ B₂ * s ^ A₂ * u ^ A₂ * F := by
  have hs0 : (0 : ℝ) ≤ s := by linarith
  have hu0 : (0 : ℝ) ≤ u := by linarith
  have hB₂ : (0 : ℝ) ≤ B₂ := le_trans hB₁ hB
  have h1 : B₁ * s ^ A₁ ≤ B₂ * s ^ A₂ :=
    le_trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hs hA) hB₁)
      (mul_le_mul_of_nonneg_right hB (Real.rpow_nonneg hs0 A₂))
  have h2 : B₁ * s ^ A₁ * u ^ A₁ ≤ B₂ * s ^ A₂ * u ^ A₁ :=
    mul_le_mul h1 le_rfl (Real.rpow_nonneg hu0 A₁)
      (mul_nonneg hB₂ (Real.rpow_nonneg hs0 A₂))
  have h3 : B₂ * s ^ A₂ * u ^ A₁ ≤ B₂ * s ^ A₂ * u ^ A₂ :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hu hA)
      (mul_nonneg hB₂ (Real.rpow_nonneg hs0 A₂))
  exact mul_le_mul_of_nonneg_right (le_trans h2 h3) hF

/-- **The pointwise majorant, dimension `8`.**  Same conclusion as the target theorem, for
`K^{(8)}`, with the threshold `Im τ ≥ 2` of `DenomLower_lines_two`. -/
private lemma pointwise_eight (ℓ : Work.Kernels.LogLambdaData) :
    ∃ B A : ℝ, 0 ≤ B ∧ 0 ≤ A ∧ ∀ (τ : UpperHalfPlane) (t : ℝ),
      (τ.re = 1 / 2 ∨ τ.re = -1 / 2) → 2 ≤ τ.im → 1 ≤ t →
      ‖Work.CKFinal.Phi (Work.Kernels.Kfun ℓ 8) τ t‖ ≤
        B * (1 + ‖(τ : ℂ)‖) ^ A * (1 + t) ^ A *
          (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (τ.im - t)))) := by
  obtain ⟨c, hc, hD⟩ := DenomLower_lines_two
  obtain ⟨Cp, Ap, hCp, hAp, hKp⟩ := KPlus_tail_lines c 2 hc (by norm_num) hD
  obtain ⟨Cm, Am, hCm, hAm, hKm⟩ := KMinus_tail_lines ℓ c 2 hc (by norm_num) hD
  refine ⟨2 * (Cp + Cm), max Ap Am, by positivity, le_trans hAp (le_max_left _ _), ?_⟩
  intro τ t hτ hy ht1
  have ht0 : (0 : ℝ) < t := by linarith
  have hs : (1 : ℝ) ≤ 1 + ‖(τ : ℂ)‖ := by have := norm_nonneg (τ : ℂ); linarith
  have hu : (1 : ℝ) ≤ 1 + t := by linarith
  have hs0 : (0 : ℝ) ≤ 1 + ‖(τ : ℂ)‖ := by linarith
  have hF0 : (0 : ℝ) ≤ Real.exp (-(Real.pi * t)) /
      (1 + Real.exp (2 * Real.pi * (τ.im - t))) := by positivity
  have hA₂ : (0 : ℝ) ≤ max Ap Am := le_trans hAp (le_max_left _ _)
  have hp := hKp τ t ht0 hτ hy ht1
  have hm := hKm τ t ht0 hτ hy ht1
  have haxis := (Phi_axis_norm_eight ℓ τ ht0).1
  have hP : Cp * (1 + ‖(τ : ℂ)‖) ^ Ap *
        (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (τ.im - t))))
      ≤ (Cp + Cm) * (1 + ‖(τ : ℂ)‖) ^ (max Ap Am) * (1 + t) ^ (max Ap Am) *
          (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (τ.im - t)))) :=
    majorant_mono hCp hA₂ (by linarith) (le_max_left _ _) hs hu hF0
  have hM : Cm * (1 + ‖(τ : ℂ)‖) ^ Am * (1 + t) ^ Am *
        (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (τ.im - t))))
      ≤ (Cp + Cm) * (1 + ‖(τ : ℂ)‖) ^ (max Ap Am) * (1 + t) ^ (max Ap Am) *
          (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (τ.im - t)))) :=
    majorant_mono₂ hCm (by linarith) (le_max_right _ _) hs hu hF0
  calc ‖Work.CKFinal.Phi (Work.Kernels.Kfun ℓ 8) τ t‖
      ≤ t ^ 2 * (‖Work.Kernels.KPlus 8 τ (ModularGroup.S • Work.Kernels.imagAxis t ht0)‖
            + ‖Work.Kernels.KMinus ℓ 8 τ (ModularGroup.S • Work.Kernels.imagAxis t ht0)‖) :=
        haxis
    _ = t ^ 2 * ‖Work.Kernels.KPlus 8 τ (ModularGroup.S • Work.Kernels.imagAxis t ht0)‖
          + t ^ 2 * ‖Work.Kernels.KMinus ℓ 8 τ
              (ModularGroup.S • Work.Kernels.imagAxis t ht0)‖ := by ring
    _ ≤ Cp * (1 + ‖(τ : ℂ)‖) ^ Ap *
            (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (τ.im - t))))
          + Cm * (1 + ‖(τ : ℂ)‖) ^ Am * (1 + t) ^ Am *
            (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (τ.im - t)))) :=
        add_le_add hp hm
    _ ≤ (Cp + Cm) * (1 + ‖(τ : ℂ)‖) ^ (max Ap Am) * (1 + t) ^ (max Ap Am) *
            (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (τ.im - t))))
          + (Cp + Cm) * (1 + ‖(τ : ℂ)‖) ^ (max Ap Am) * (1 + t) ^ (max Ap Am) *
            (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (τ.im - t)))) :=
        add_le_add hP hM
    _ = 2 * (Cp + Cm) * (1 + ‖(τ : ℂ)‖) ^ (max Ap Am) * (1 + t) ^ (max Ap Am) *
          (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (τ.im - t)))) := by ring

/-- **The pointwise majorant, dimension `24`.** -/
private lemma pointwise_twentyfour (ℓ : Work.Kernels.LogLambdaData) :
    ∃ B A : ℝ, 0 ≤ B ∧ 0 ≤ A ∧ ∀ (τ : UpperHalfPlane) (t : ℝ),
      (τ.re = 1 / 2 ∨ τ.re = -1 / 2) → 2 ≤ τ.im → 1 ≤ t →
      ‖Work.CKFinal.Phi (Work.Kernels.Kfun ℓ 24) τ t‖ ≤
        B * (1 + ‖(τ : ℂ)‖) ^ A * (1 + t) ^ A *
          (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (τ.im - t)))) := by
  obtain ⟨c, hc, hD⟩ := DenomLower_lines_two
  obtain ⟨Cp, Ap, hCp, hAp, hKp⟩ := KPlus_tail_lines_twentyfour ℓ c 2 hc le_rfl hD
  obtain ⟨Cm, Am, hCm, hAm, hKm⟩ := KMinus_tail_lines_twentyfour ℓ c 2 hc le_rfl hD
  refine ⟨2 * (Cp + Cm), max Ap Am, by positivity, le_trans hAp (le_max_left _ _), ?_⟩
  intro τ t hτ hy ht1
  have ht0 : (0 : ℝ) < t := by linarith
  have hs : (1 : ℝ) ≤ 1 + ‖(τ : ℂ)‖ := by have := norm_nonneg (τ : ℂ); linarith
  have hu : (1 : ℝ) ≤ 1 + t := by linarith
  have hs0 : (0 : ℝ) ≤ 1 + ‖(τ : ℂ)‖ := by linarith
  have hF0 : (0 : ℝ) ≤ Real.exp (-(Real.pi * t)) /
      (1 + Real.exp (2 * Real.pi * (τ.im - t))) := by positivity
  have hA₂ : (0 : ℝ) ≤ max Ap Am := le_trans hAp (le_max_left _ _)
  have he1 : Real.exp (-(2 * Real.pi * τ.im)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [Real.pi_pos, hy]
  have he0 : (0 : ℝ) ≤ Real.exp (-(2 * Real.pi * τ.im)) := (Real.exp_pos _).le
  have huA : (1 : ℝ) ≤ (1 + t) ^ (max Ap Am) := Real.one_le_rpow hu hA₂
  have huA0 : (0 : ℝ) ≤ (1 + t) ^ (max Ap Am) := by linarith
  have hp := hKp τ t ht0 hτ hy ht1
  have hm := hKm τ t ht0 hτ hy ht1
  have haxis := (Phi_axis_norm_twentyfour ℓ τ ht0).1
  -- the `K₊` term
  have hP : Cp * (1 + ‖(τ : ℂ)‖) ^ Ap *
        (Real.exp (-(2 * Real.pi * τ.im)) *
          (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (τ.im - t)))))
      ≤ (Cp + Cm) * (1 + ‖(τ : ℂ)‖) ^ (max Ap Am) * (1 + t) ^ (max Ap Am) *
          (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (τ.im - t)))) := by
    have h1 : Real.exp (-(2 * Real.pi * τ.im)) *
          (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (τ.im - t))))
        ≤ (1 + t) ^ (max Ap Am) *
          (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (τ.im - t)))) :=
      mul_le_mul_of_nonneg_right (le_trans he1 huA) hF0
    have h2 : Cp * (1 + ‖(τ : ℂ)‖) ^ Ap *
          (Real.exp (-(2 * Real.pi * τ.im)) *
            (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (τ.im - t)))))
        ≤ Cp * (1 + ‖(τ : ℂ)‖) ^ Ap *
          ((1 + t) ^ (max Ap Am) *
            (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (τ.im - t))))) :=
      mul_le_mul_of_nonneg_left h1
        (mul_nonneg hCp (Real.rpow_nonneg hs0 Ap))
    have h3 : Cp * (1 + ‖(τ : ℂ)‖) ^ Ap ≤ (Cp + Cm) * (1 + ‖(τ : ℂ)‖) ^ (max Ap Am) :=
      le_trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hs (le_max_left _ _)) hCp)
        (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hs0 (max Ap Am)))
    refine le_trans h2 ?_
    calc Cp * (1 + ‖(τ : ℂ)‖) ^ Ap *
            ((1 + t) ^ (max Ap Am) *
              (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (τ.im - t)))))
        = (Cp * (1 + ‖(τ : ℂ)‖) ^ Ap * (1 + t) ^ (max Ap Am)) *
            (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (τ.im - t)))) := by ring
      _ ≤ ((Cp + Cm) * (1 + ‖(τ : ℂ)‖) ^ (max Ap Am) * (1 + t) ^ (max Ap Am)) *
            (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (τ.im - t)))) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h3 huA0) hF0
      _ = (Cp + Cm) * (1 + ‖(τ : ℂ)‖) ^ (max Ap Am) * (1 + t) ^ (max Ap Am) *
            (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (τ.im - t)))) := by ring
  -- the `K₋` term
  have hM : Cm * (1 + ‖(τ : ℂ)‖) ^ Am *
        (Real.exp (-(2 * Real.pi * τ.im)) *
          (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (τ.im - t)))))
      ≤ (Cp + Cm) * (1 + ‖(τ : ℂ)‖) ^ (max Ap Am) * (1 + t) ^ (max Ap Am) *
          (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (τ.im - t)))) := by
    have h1 : Real.exp (-(2 * Real.pi * τ.im)) *
          (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (τ.im - t))))
        ≤ (1 + t) ^ (max Ap Am) *
          (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (τ.im - t)))) :=
      mul_le_mul_of_nonneg_right (le_trans he1 huA) hF0
    have h2 : Cm * (1 + ‖(τ : ℂ)‖) ^ Am *
          (Real.exp (-(2 * Real.pi * τ.im)) *
            (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (τ.im - t)))))
        ≤ Cm * (1 + ‖(τ : ℂ)‖) ^ Am *
          ((1 + t) ^ (max Ap Am) *
            (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (τ.im - t))))) :=
      mul_le_mul_of_nonneg_left h1
        (mul_nonneg hCm (Real.rpow_nonneg hs0 Am))
    have h3 : Cm * (1 + ‖(τ : ℂ)‖) ^ Am ≤ (Cp + Cm) * (1 + ‖(τ : ℂ)‖) ^ (max Ap Am) :=
      le_trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hs (le_max_right _ _)) hCm)
        (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hs0 (max Ap Am)))
    refine le_trans h2 ?_
    calc Cm * (1 + ‖(τ : ℂ)‖) ^ Am *
            ((1 + t) ^ (max Ap Am) *
              (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (τ.im - t)))))
        = (Cm * (1 + ‖(τ : ℂ)‖) ^ Am * (1 + t) ^ (max Ap Am)) *
            (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (τ.im - t)))) := by ring
      _ ≤ ((Cp + Cm) * (1 + ‖(τ : ℂ)‖) ^ (max Ap Am) * (1 + t) ^ (max Ap Am)) *
            (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (τ.im - t)))) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h3 huA0) hF0
      _ = (Cp + Cm) * (1 + ‖(τ : ℂ)‖) ^ (max Ap Am) * (1 + t) ^ (max Ap Am) *
            (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (τ.im - t)))) := by ring
  calc ‖Work.CKFinal.Phi (Work.Kernels.Kfun ℓ 24) τ t‖
      ≤ t ^ 10 * (‖Work.Kernels.KPlus 24 τ (ModularGroup.S • Work.Kernels.imagAxis t ht0)‖
            + ‖Work.Kernels.KMinus ℓ 24 τ (ModularGroup.S • Work.Kernels.imagAxis t ht0)‖) :=
        haxis
    _ = t ^ 10 * ‖Work.Kernels.KPlus 24 τ (ModularGroup.S • Work.Kernels.imagAxis t ht0)‖
          + t ^ 10 * ‖Work.Kernels.KMinus ℓ 24 τ
              (ModularGroup.S • Work.Kernels.imagAxis t ht0)‖ := by ring
    _ ≤ Cp * (1 + ‖(τ : ℂ)‖) ^ Ap *
            (Real.exp (-(2 * Real.pi * τ.im)) *
              (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (τ.im - t)))))
          + Cm * (1 + ‖(τ : ℂ)‖) ^ Am *
            (Real.exp (-(2 * Real.pi * τ.im)) *
              (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (τ.im - t))))) :=
        add_le_add hp hm
    _ ≤ (Cp + Cm) * (1 + ‖(τ : ℂ)‖) ^ (max Ap Am) * (1 + t) ^ (max Ap Am) *
            (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (τ.im - t))))
          + (Cp + Cm) * (1 + ‖(τ : ℂ)‖) ^ (max Ap Am) * (1 + t) ^ (max Ap Am) *
            (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (τ.im - t)))) :=
        add_le_add hP hM
    _ = 2 * (Cp + Cm) * (1 + ‖(τ : ℂ)‖) ^ (max Ap Am) * (1 + t) ^ (max Ap Am) *
          (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (τ.im - t)))) := by ring

/-- **Pointwise decay of the second difference `Φ(τ,·)` of the CKMRV kernel on the imaginary axis.**

For `τ` on either line `Re τ = ±1/2` with `Im τ ≥ 2` (the threshold of `DenomLower_lines`), the
second difference `Φ(τ,t) = 2K(τ,it) - K(τ,it-1) - K(τ,it+1)` is bounded by
`B (1+‖τ‖)^A (1+t)^A · e^{-πt}/(1 + e^{2π(Im τ - t)})` for all `t ≥ 1` (a "bump" of width `O(1)`
at `t = Im τ`, decaying like `e^{-πt}` above it).  The factor `(1+‖τ‖)^A` is genuinely needed:
at the fixed `t = 1` the bound is `O(e^{-2π Im τ})` while `Φ(τ,1)` grows like `Im τ · e^{-2π Im τ}`.

This is the pointwise form of `Phi_tail_bound_eight` / `Phi_tail_bound_twentyfour`, and it is what
makes `∫_1^∞ Φ(τ,t)e^{-zt}dt` analytic on `Re z > -π` (for fixed `τ` the factor is a constant). -/
theorem Phi_axis_pointwise_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) (hτ : τ.re = 1 / 2 ∨ τ.re = - 1 / 2) (hy : 2 ≤ τ.im) :
    ∃ B A : ℝ, 0 ≤ B ∧ 0 ≤ A ∧ ∀ t : ℝ, 1 ≤ t →
      ‖Work.CKFinal.Phi (Work.Kernels.Kfun ℓ d) τ t‖ ≤
        B * (1 + ‖(τ : ℂ)‖) ^ A * (1 + t) ^ A *
          (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (τ.im - t)))) := by
  obtain ⟨B₈, A₈, hB₈, hA₈, h8⟩ := pointwise_eight ℓ
  obtain ⟨B₂₄, A₂₄, hB₂₄, hA₂₄, h24⟩ := pointwise_twentyfour ℓ
  refine ⟨max B₈ B₂₄, max A₈ A₂₄, le_trans hB₈ (le_max_left _ _),
    le_trans hA₈ (le_max_left _ _), ?_⟩
  intro t ht
  have hs : (1 : ℝ) ≤ 1 + ‖(τ : ℂ)‖ := by have := norm_nonneg (τ : ℂ); linarith
  have hu : (1 : ℝ) ≤ 1 + t := by linarith
  have hF0 : (0 : ℝ) ≤ Real.exp (-(Real.pi * t)) /
      (1 + Real.exp (2 * Real.pi * (τ.im - t))) := by positivity
  rcases hd with hd | hd
  · rw [hd]
    exact le_trans (h8 τ t hτ hy ht)
      (majorant_mono₂ hB₈ (le_max_left _ _) (le_max_left _ _) hs hu hF0)
  · rw [hd]
    exact le_trans (h24 τ t hτ hy ht)
      (majorant_mono₂ hB₂₄ (le_max_right _ _) (le_max_right _ _) hs hu hF0)

end

end Work.CKFinal.LineDecay
