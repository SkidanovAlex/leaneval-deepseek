import Mathlib
import Submission.Work.CKFinal.LineDecay.Defs
import Submission.Work.CKFinal.LineDecay.HatLayer

/-!
# Assembly of the two line-decay estimates

This file reduces the target statement `Work.CKFinal.layer_line_decay` to

* the CKMRV contour-shift identity `F = P₁+P₂+P₃` on the two lines `Re τ = ±1/2`, valid for **all**
  real `r` and for both kernels (`Kfun`, `Khat`) — the "model-subtracted shift";
* the three bound families `P₁`, `P₂`, `P₃`, each uniform in `r`, with the rate
  `e^{-μ Im τ}` (`μ = π` for `d = 8`, `μ = 3π` for `d = 24`).

Clause (2) of the target (`paperLayer (S•τ) r · τ^{-d/2}`) is turned into a bound on the hatted
layer at `τ` itself by `paperLayer_S_smul`.
-/

noncomputable section

namespace Work.CKFinal

open UpperHalfPlane MeasureTheory
open scoped Topology Manifold

/-- **The line-decay estimates from the identity and the three bound families.** -/
theorem line_decay_of_identity (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (μ : ℝ)
    (hid : ∀ (τ : UpperHalfPlane), (τ.re = 1 / 2 ∨ τ.re = -1 / 2) → 12 ≤ τ.im →
      ((∀ r : ℝ, Work.Kernels.gaussTerm τ r
          + Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r
          = P1 (Work.Kernels.Kfun ℓ d) r τ + P2 (Work.Kernels.Kfun ℓ d) r τ
            + P3 (Work.Kernels.Kfun ℓ d) r τ)
        ∧ (∀ r : ℝ, paperLayerK (Work.Kernels.Khat ℓ d) (Ghat ℓ d) r τ
          = P1 (Work.Kernels.Khat ℓ d) r τ + P2 (Work.Kernels.Khat ℓ d) r τ
            + P3 (Work.Kernels.Khat ℓ d) r τ)))
    (hP1 : ∃ C N Y₀ : ℝ, 0 ≤ C ∧ 0 ≤ N ∧ 1 ≤ Y₀ ∧
      ∀ (τ : UpperHalfPlane) (r : ℝ), (τ.re = 1 / 2 ∨ τ.re = -1 / 2) → Y₀ ≤ τ.im →
        (‖P1 (Work.Kernels.Kfun ℓ d) r τ‖ ≤ C * τ.im ^ N * Real.exp (-(μ * τ.im))
          ∧ ‖P1 (Work.Kernels.Khat ℓ d) r τ‖ ≤ C * τ.im ^ N * Real.exp (-(μ * τ.im))))
    (hP2 : ∃ C N Y₀ : ℝ, 0 ≤ C ∧ 0 ≤ N ∧ 1 ≤ Y₀ ∧
      ∀ (τ : UpperHalfPlane) (r : ℝ), (τ.re = 1 / 2 ∨ τ.re = -1 / 2) → Y₀ ≤ τ.im →
        (‖P2 (Work.Kernels.Kfun ℓ d) r τ‖ ≤ C * τ.im ^ N * Real.exp (-(μ * τ.im))
          ∧ ‖P2 (Work.Kernels.Khat ℓ d) r τ‖ ≤ C * τ.im ^ N * Real.exp (-(μ * τ.im))))
    (hP3 : ∃ C N Y₀ : ℝ, 0 ≤ C ∧ 0 ≤ N ∧ 1 ≤ Y₀ ∧
      ∀ (τ : UpperHalfPlane) (r : ℝ), (τ.re = 1 / 2 ∨ τ.re = -1 / 2) → Y₀ ≤ τ.im →
        (‖P3 (Work.Kernels.Kfun ℓ d) r τ‖ ≤ C * τ.im ^ N * Real.exp (-(μ * τ.im))
          ∧ ‖P3 (Work.Kernels.Khat ℓ d) r τ‖ ≤ C * τ.im ^ N * Real.exp (-(μ * τ.im)))) :
    ∃ C N Y₀ : ℝ, 0 ≤ C ∧ 0 ≤ N ∧ 1 ≤ Y₀ ∧
      ∀ (τ : UpperHalfPlane) (r : ℝ), (τ.re = 1 / 2 ∨ τ.re = -1 / 2) → Y₀ ≤ τ.im →
        (‖Work.Kernels.gaussTerm τ r
            + Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r‖
          ≤ C * τ.im ^ N * Real.exp (-(μ * τ.im))
        ∧ ‖Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d
              (ModularGroup.S • τ) r * (τ : ℂ) ^ (-((d : ℤ) / 2))‖
          ≤ C * τ.im ^ N * Real.exp (-(μ * τ.im))) := by
  obtain ⟨C₁, N₁, Y₁, hC₁, hN₁, hY₁, hb₁⟩ := hP1
  obtain ⟨C₂, N₂, Y₂, hC₂, hN₂, hY₂, hb₂⟩ := hP2
  obtain ⟨C₃, N₃, Y₃, hC₃, hN₃, hY₃, hb₃⟩ := hP3
  refine ⟨C₁ + C₂ + C₃ + 1, max N₁ (max N₂ N₃), max 12 (max Y₁ (max Y₂ Y₃)),
    by positivity, ?_, ?_, ?_⟩
  · exact le_trans hN₁ (le_max_left _ _)
  · exact le_trans (by norm_num : (1 : ℝ) ≤ 12) (le_max_left _ _)
  · intro τ r hline hY
    have hy12 : 12 ≤ τ.im := le_trans (le_max_left (12 : ℝ) (max Y₁ (max Y₂ Y₃))) hY
    have hy1 : Y₁ ≤ τ.im :=
      le_trans (le_trans (le_max_left Y₁ (max Y₂ Y₃))
        (le_max_right (12 : ℝ) (max Y₁ (max Y₂ Y₃)))) hY
    have hy2 : Y₂ ≤ τ.im :=
      le_trans (le_trans (le_trans (le_max_left Y₂ Y₃) (le_max_right Y₁ (max Y₂ Y₃)))
        (le_max_right (12 : ℝ) (max Y₁ (max Y₂ Y₃)))) hY
    have hy3 : Y₃ ≤ τ.im :=
      le_trans (le_trans (le_trans (le_max_right Y₂ Y₃) (le_max_right Y₁ (max Y₂ Y₃)))
        (le_max_right (12 : ℝ) (max Y₁ (max Y₂ Y₃)))) hY
    obtain ⟨hK, hKh⟩ := hid τ hline hy12
    obtain ⟨h1a, h1b⟩ := hb₁ τ r hline hy1
    obtain ⟨h2a, h2b⟩ := hb₂ τ r hline hy2
    obtain ⟨h3a, h3b⟩ := hb₃ τ r hline hy3
    have hy1le : (1 : ℝ) ≤ τ.im := le_trans (by norm_num : (1 : ℝ) ≤ 12) hy12
    have hy0 : (0 : ℝ) ≤ τ.im := le_trans zero_le_one hy1le
    have hE0 : 0 ≤ Real.exp (-(μ * τ.im)) := Real.exp_nonneg _
    have hNmax : N₁ ≤ max N₁ (max N₂ N₃) := le_max_left _ _
    have hN₂' : N₂ ≤ max N₁ (max N₂ N₃) := le_trans (le_max_left N₂ N₃) (le_max_right _ _)
    have hN₃' : N₃ ≤ max N₁ (max N₂ N₃) := le_trans (le_max_right N₂ N₃) (le_max_right _ _)
    have hp1 : τ.im ^ N₁ ≤ τ.im ^ (max N₁ (max N₂ N₃)) :=
      Real.rpow_le_rpow_of_exponent_le hy1le hNmax
    have hp2 : τ.im ^ N₂ ≤ τ.im ^ (max N₁ (max N₂ N₃)) :=
      Real.rpow_le_rpow_of_exponent_le hy1le hN₂'
    have hp3 : τ.im ^ N₃ ≤ τ.im ^ (max N₁ (max N₂ N₃)) :=
      Real.rpow_le_rpow_of_exponent_le hy1le hN₃'
    have hZ0 : 0 ≤ τ.im ^ (max N₁ (max N₂ N₃)) * Real.exp (-(μ * τ.im)) :=
      mul_nonneg (Real.rpow_nonneg hy0 _) hE0
    have hy1le : (1 : ℝ) ≤ τ.im := le_trans (by norm_num : (1 : ℝ) ≤ 12) hy12
    have hy0 : (0 : ℝ) ≤ τ.im := le_trans zero_le_one hy1le
    have hE0 : 0 ≤ Real.exp (-(μ * τ.im)) := Real.exp_nonneg _
    have hNmax : N₁ ≤ max N₁ (max N₂ N₃) := le_max_left _ _
    have hN₂' : N₂ ≤ max N₁ (max N₂ N₃) := le_trans (le_max_left N₂ N₃) (le_max_right _ _)
    have hN₃' : N₃ ≤ max N₁ (max N₂ N₃) := le_trans (le_max_right N₂ N₃) (le_max_right _ _)
    have hp1 : τ.im ^ N₁ ≤ τ.im ^ (max N₁ (max N₂ N₃)) :=
      Real.rpow_le_rpow_of_exponent_le hy1le hNmax
    have hp2 : τ.im ^ N₂ ≤ τ.im ^ (max N₁ (max N₂ N₃)) :=
      Real.rpow_le_rpow_of_exponent_le hy1le hN₂'
    have hp3 : τ.im ^ N₃ ≤ τ.im ^ (max N₁ (max N₂ N₃)) :=
      Real.rpow_le_rpow_of_exponent_le hy1le hN₃'
    have hZ0 : 0 ≤ τ.im ^ (max N₁ (max N₂ N₃)) * Real.exp (-(μ * τ.im)) :=
      mul_nonneg (Real.rpow_nonneg hy0 _) hE0
    have key : ∀ (C : ℝ) (hC : 0 ≤ C) (N' : ℝ) (hN' : N' ≤ max N₁ (max N₂ N₃))
        (b₁ b₂ b₃ : ℝ),
        b₁ ≤ C₁ * τ.im ^ N' * Real.exp (-(μ * τ.im)) → b₁ ≤ C₁ * τ.im ^ N' * Real.exp (-(μ * τ.im)) →
        True := fun _ _ _ _ _ _ _ _ _ => trivial
    -- termwise comparison of the three bounds at the exponent `max N₁ (max N₂ N₃)`
    have cmp₁ : ∀ b : ℝ, b ≤ C₁ * τ.im ^ N₁ * Real.exp (-(μ * τ.im)) →
        b ≤ C₁ * (τ.im ^ (max N₁ (max N₂ N₃)) * Real.exp (-(μ * τ.im))) := by
      intro b hb
      refine le_trans hb ?_
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hp1 hE0) hC₁
    have cmp₂ : ∀ b : ℝ, b ≤ C₂ * τ.im ^ N₂ * Real.exp (-(μ * τ.im)) →
        b ≤ C₂ * (τ.im ^ (max N₁ (max N₂ N₃)) * Real.exp (-(μ * τ.im))) := by
      intro b hb
      refine le_trans hb ?_
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hp2 hE0) hC₂
    have cmp₃ : ∀ b : ℝ, b ≤ C₃ * τ.im ^ N₃ * Real.exp (-(μ * τ.im)) →
        b ≤ C₃ * (τ.im ^ (max N₁ (max N₂ N₃)) * Real.exp (-(μ * τ.im))) := by
      intro b hb
      refine le_trans hb ?_
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hp3 hE0) hC₃
    have norm3 : ∀ (a b c : ℂ), ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
      intro a b c
      refine le_trans (norm_add_le _ _) ?_
      refine le_trans (add_le_add (norm_add_le _ _) le_rfl) ?_
      exact le_of_eq (by ring)
    have finish : ∀ (b₁ b₂ b₃ : ℝ),
        b₁ ≤ C₁ * τ.im ^ N₁ * Real.exp (-(μ * τ.im)) →
        b₂ ≤ C₂ * τ.im ^ N₂ * Real.exp (-(μ * τ.im)) →
        b₃ ≤ C₃ * τ.im ^ N₃ * Real.exp (-(μ * τ.im)) →
        b₁ + b₂ + b₃ ≤ (C₁ + C₂ + C₃ + 1) * τ.im ^ (max N₁ (max N₂ N₃))
            * Real.exp (-(μ * τ.im)) := by
      intro b₁ b₂ b₃ h₁ h₂ h₃
      have k₁ := cmp₁ b₁ h₁
      have k₂ := cmp₂ b₂ h₂
      have k₃ := cmp₃ b₃ h₃
      calc b₁ + b₂ + b₃
          ≤ C₁ * (τ.im ^ (max N₁ (max N₂ N₃)) * Real.exp (-(μ * τ.im)))
            + C₂ * (τ.im ^ (max N₁ (max N₂ N₃)) * Real.exp (-(μ * τ.im)))
            + C₃ * (τ.im ^ (max N₁ (max N₂ N₃)) * Real.exp (-(μ * τ.im))) :=
            add_le_add (add_le_add k₁ k₂) k₃
        _ = (C₁ + C₂ + C₃) * (τ.im ^ (max N₁ (max N₂ N₃))
              * Real.exp (-(μ * τ.im))) := by ring
        _ ≤ (C₁ + C₂ + C₃ + 1) * (τ.im ^ (max N₁ (max N₂ N₃))
              * Real.exp (-(μ * τ.im))) :=
            mul_le_mul_of_nonneg_right (by linarith) hZ0
        _ = (C₁ + C₂ + C₃ + 1) * τ.im ^ (max N₁ (max N₂ N₃))
              * Real.exp (-(μ * τ.im)) := by ring
    constructor
    · -- clause (1)
      rw [hK r]
      refine le_trans (norm3 _ _ _) ?_
      exact finish _ _ _ h1a h2a h3a
    · -- clause (2)
      have hτ0 : (τ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero τ
      have hab : (τ : ℂ) ^ ((d : ℤ) / 2) * (τ : ℂ) ^ (-((d : ℤ) / 2)) = 1 := by
        rw [← zpow_add₀ hτ0]
        simp
      have hcanon : Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d
            (ModularGroup.S • τ) r * (τ : ℂ) ^ (-((d : ℤ) / 2))
          = -paperLayerK (Work.Kernels.Khat ℓ d) (Ghat ℓ d) r τ := by
        rw [paperLayer_S_smul ℓ d hd τ r]
        calc (-((τ : ℂ) ^ ((d : ℤ) / 2)) * paperLayerK (Work.Kernels.Khat ℓ d) (Ghat ℓ d) r τ)
              * (τ : ℂ) ^ (-((d : ℤ) / 2))
            = -(((τ : ℂ) ^ ((d : ℤ) / 2) * (τ : ℂ) ^ (-((d : ℤ) / 2)))
                * paperLayerK (Work.Kernels.Khat ℓ d) (Ghat ℓ d) r τ) := by ring
          _ = -paperLayerK (Work.Kernels.Khat ℓ d) (Ghat ℓ d) r τ := by rw [hab]; ring
      rw [hcanon, norm_neg, hKh r]
      refine le_trans (norm3 _ _ _) ?_
      exact finish _ _ _ h1b h2b h3b

end Work.CKFinal
