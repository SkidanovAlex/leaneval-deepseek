import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Submission.Commons.Analysis.Fourier.fourier_transform_min_decay
import Submission.Commons.Analysis.Fourier.schwartz_decay_real

set_option linter.unusedVariables false

namespace Commons.Analysis.Schwartz

open scoped FourierTransform

/-- Elementary comparison of the two standard decay rates on `ℝ`:
`(1 + |x|)^{-2} ≤ (1 + x²)^{-1}`. -/
private lemma rpow_neg_two_le_inv_one_add_sq (x : ℝ) :
    (1 + |x|) ^ (-(2:ℝ)) ≤ (1 + x^2)⁻¹ := by
  have hsq : 1 + x^2 ≤ (1 + |x|)^2 := by nlinarith [abs_nonneg x, sq_abs x]
  have hpos : 0 < 1 + x^2 := by positivity
  have h1 : (1 + |x|) ^ (-(2:ℝ)) = 1 / (1 + |x|)^2 := by
    rw [Real.rpow_neg (by positivity : (0:ℝ) ≤ 1 + |x|), Real.rpow_two, inv_eq_one_div]
  rw [h1, inv_eq_one_div]
  exact one_div_le_one_div_of_le hpos hsq

/-- **Decay of the inverse Fourier transform of a compactly supported Schwartz function.**
Let `ψ : 𝓢(ℝ, ℂ)` be a Schwartz function whose support is contained in `[-C, C]` (this is the
content of `hψsupp`) and whose derivatives of order `≤ 2` are bounded by `C`.  Then both the
inverse Fourier transform `𝓕⁻ ψ` and its derivative decay at least like `t ↦ 1 / (1 + t²)`.

In fact the support and derivative bounds are not needed: the inverse Fourier transform of *any*
Schwartz function is again Schwartz, so it and all of its derivatives decay faster than any
polynomial.  We record this in the most elementary form, using the decay lemma for Schwartz
functions applied to `𝓕⁻ ψ` and to `deriv (𝓕⁻ ψ)`. -/
theorem fourierInv_schwartz_decay (C : ℝ) (hC : 0 < C) (ψ : SchwartzMap ℝ ℂ) (hψsupp : ∀ ξ, ξ ∉ Set.Icc (-C) C → ψ ξ = 0) (hψj : ∀ j : ℕ, j ≤ 2 → ∀ ξ, ‖iteratedFDeriv ℝ j (ψ : ℝ → ℂ) ξ‖ ≤ C) : ∃ C₁ : ℝ, 0 < C₁ ∧ (∀ t : ℝ, ‖(FourierTransform.fourierInv ψ : SchwartzMap ℝ ℂ) t‖ ≤ C₁ / (1 + t^2)) ∧ (∀ t : ℝ, ‖deriv (fun t : ℝ => (FourierTransform.fourierInv ψ : SchwartzMap ℝ ℂ) t) t‖ ≤ C₁ / (1 + t^2)) := by
  obtain ⟨B₀, hB₀pos, hB₀⟩ :=
    Commons.Analysis.Fourier.schwartz_decay_real (FourierTransform.fourierInv ψ) 2
  obtain ⟨B₁, hB₁pos, hB₁⟩ :=
    Commons.Analysis.Fourier.schwartz_decay_real
      (SchwartzMap.derivCLM ℝ ℂ (FourierTransform.fourierInv ψ)) 2
  refine ⟨B₀ + B₁, by positivity, fun t => ?_, fun t => ?_⟩
  · calc ‖(FourierTransform.fourierInv ψ : SchwartzMap ℝ ℂ) t‖
        ≤ B₀ * (1 + |t|) ^ (-(2:ℝ)) := hB₀ t
      _ ≤ B₀ * (1 + t^2)⁻¹ :=
          mul_le_mul_of_nonneg_left (rpow_neg_two_le_inv_one_add_sq t) hB₀pos.le
      _ ≤ (B₀ + B₁) * (1 + t^2)⁻¹ :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = (B₀ + B₁) / (1 + t^2) := by rw [div_eq_mul_inv]
  · have h := hB₁ t
    rw [SchwartzMap.derivCLM_apply] at h
    calc ‖deriv (fun t : ℝ => (FourierTransform.fourierInv ψ : SchwartzMap ℝ ℂ) t) t‖
        = ‖deriv (FourierTransform.fourierInv ψ) t‖ := rfl
      _ ≤ B₁ * (1 + |t|) ^ (-(2:ℝ)) := h
      _ ≤ B₁ * (1 + t^2)⁻¹ :=
          mul_le_mul_of_nonneg_left (rpow_neg_two_le_inv_one_add_sq t) hB₁pos.le
      _ ≤ (B₀ + B₁) * (1 + t^2)⁻¹ :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = (B₀ + B₁) / (1 + t^2) := by rw [div_eq_mul_inv]

end Commons.Analysis.Schwartz