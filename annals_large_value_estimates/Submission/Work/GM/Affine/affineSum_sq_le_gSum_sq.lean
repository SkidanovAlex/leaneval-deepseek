import Mathlib
import Submission.Work.GM.Affine.setup
import Submission.Work.GM.Affine.fine_setup
import Submission.Work.GM.Affine.gSum_fourier

/-!
# `∫ (affineSum)² ≤ ∫ (gSum)²`

GM's affine sum `affineSum K M₁ M₂ M₃ f` is dominated pointwise by the smoothed majorant
`gSum K M₁ M₂ M₃ f` (`Work.GM.Affine.affineSum_le_gSum`). Since `f ≥ 0`, both sums are
non-negative, so the pointwise domination passes to the squares and hence to the integrals.

This file only records that elementary consequence; it needs no Fourier analysis.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.GM.Affine

noncomputable section

/-- The real-valued majorant `gSum` is continuous when `f` is. -/
lemma continuous_gSum_real' (K M₁ M₂ M₃ : ℝ) {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (fun u : ℝ => gSum K M₁ M₂ M₃ f u) := by
  have h := continuous_gSum_complex K M₁ M₂ M₃ hf
  have h2 : (fun u : ℝ => gSum K M₁ M₂ M₃ f u)
      = fun u : ℝ => Complex.re (((gSum K M₁ M₂ M₃ f u : ℝ) : ℂ)) := by
    funext u
    simp
  rw [h2]
  exact Complex.continuous_re.comp h

/-- The real-valued majorant `gSum` has compact support when `f` does. -/
lemma hasCompactSupport_gSum_real' (K M₁ M₂ M₃ : ℝ) (hM₁ : 0 < M₁) {f : ℝ → ℝ}
    (hcs : HasCompactSupport f) : HasCompactSupport (fun u : ℝ => gSum K M₁ M₂ M₃ f u) := by
  have h := hasCompactSupport_gSum_complex K M₁ M₂ M₃ hM₁ hcs
  have h2 : (fun u : ℝ => gSum K M₁ M₂ M₃ f u)
      = fun u : ℝ => Complex.re (((gSum K M₁ M₂ M₃ f u : ℝ) : ℂ)) := by
    funext u
    simp
  rw [h2]
  exact HasCompactSupport.comp_left h (g := fun z : ℂ => z.re) (by simp)

theorem affineSum_sq_le_gSum_sq {K M₁ M₂ M₃ : ℝ} (hK : 0 < K) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂)
    (hM₃ : 0 < M₃) {f : ℝ → ℝ} (hf : Continuous f) (hcs : HasCompactSupport f)
    (hfnn : ∀ u, 0 ≤ f u) :
    ∫ u, (Submission.GM.affineSum K M₁ M₂ M₃ f u) ^ 2 ≤ ∫ u, (gSum K M₁ M₂ M₃ f u) ^ 2 := by
  have hcont : Continuous (fun u : ℝ => gSum K M₁ M₂ M₃ f u) :=
    continuous_gSum_real' K M₁ M₂ M₃ hf
  have hcsg : HasCompactSupport (fun u : ℝ => gSum K M₁ M₂ M₃ f u) :=
    hasCompactSupport_gSum_real' K M₁ M₂ M₃ hM₁ hcs
  have hint : Integrable (fun u : ℝ => (gSum K M₁ M₂ M₃ f u) ^ 2) := by
    have hpow : Continuous (fun u : ℝ => (gSum K M₁ M₂ M₃ f u) ^ 2) := hcont.pow 2
    have hcs2 : HasCompactSupport (fun u : ℝ => (gSum K M₁ M₂ M₃ f u) ^ 2) := by
      have heq2 : ((fun x : ℝ => x ^ 2) ∘ fun u : ℝ => gSum K M₁ M₂ M₃ f u)
          = fun u : ℝ => (gSum K M₁ M₂ M₃ f u) ^ 2 := by
        funext u
        rfl
      have hh := hcsg.comp_left (g := fun x : ℝ => x ^ 2) (by simp)
      rwa [heq2] at hh
    exact hpow.integrable_of_hasCompactSupport hcs2
  have hpt : ∀ u, (Submission.GM.affineSum K M₁ M₂ M₃ f u) ^ 2 ≤
      (gSum K M₁ M₂ M₃ f u) ^ 2 := by
    intro u
    have h1 : Submission.GM.affineSum K M₁ M₂ M₃ f u ≤ gSum K M₁ M₂ M₃ f u :=
      affineSum_le_gSum hK.le hM₃ hfnn u
    have h2 : 0 ≤ Submission.GM.affineSum K M₁ M₂ M₃ f u := by
      rw [affineSum_eq]
      exact Finset.sum_nonneg fun m₁ _ => Finset.sum_nonneg fun m₂ _ =>
        Finset.sum_nonneg fun m₃ _ => hfnn _
    exact pow_le_pow_left₀ h2 h1 2
  exact integral_mono_of_nonneg (Filter.Eventually.of_forall fun u => sq_nonneg _) hint
    (Filter.Eventually.of_forall hpt)

end

end Work.GM.Affine
