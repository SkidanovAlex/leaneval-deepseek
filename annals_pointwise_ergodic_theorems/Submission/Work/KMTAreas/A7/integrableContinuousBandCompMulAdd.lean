import Mathlib
import Submission.Commons.Analysis.Fourier.fourier_comp_mul_left

namespace Work.KMTAreas.A7

open MeasureTheory
open scoped FourierTransform

/-
Fourier/analytic properties of the rescaled-and-translated function `t ↦ γ (q * t + r₀)`:
integrability, continuity, and Fourier support in `[-qβ, qβ]`.

Suggested route: `Commons.Analysis.Fourier.fourier_comp_mul_left` gives
`𝓕 (fun t => g (q * t)) ξ = (q:ℂ)⁻¹ * 𝓕 g (ξ / q)` for `q > 0`, and
`Commons.Analysis.Fourier.fourier_comp_sub` (in `fourier_scaled_translate.lean`) gives the
modulation by the shift `r₀`; the modulation is unimodular, so the Fourier support of
`t ↦ γ (q * t + r₀)` is `q • supp 𝓕γ ⊆ [-qβ, qβ]`.  Integrability: change of variables
(`MeasureTheory.Integrable.comp_mul_left'` + `MeasureTheory.Integrable.comp_sub_right`).
-/
theorem integrableContinuousBandCompMulAdd {q : ℕ} (hq : 0 < q) {β : ℝ} {r₀ : ℤ} {γ : ℝ → ℂ}
    (hγint : MeasureTheory.Integrable γ) (hγcont : Continuous γ)
    (hγband : ∀ ξ : ℝ, ξ ∉ Set.Icc (-β) β → FourierTransform.fourier γ ξ = 0) :
    MeasureTheory.Integrable (fun t : ℝ => γ ((q : ℝ) * t + (r₀ : ℝ))) ∧
      Continuous (fun t : ℝ => γ ((q : ℝ) * t + (r₀ : ℝ))) ∧
      (∀ ξ : ℝ, ξ ∉ Set.Icc (-((q : ℝ) * β)) ((q : ℝ) * β) →
        FourierTransform.fourier (fun t : ℝ => γ ((q : ℝ) * t + (r₀ : ℝ))) ξ = 0) := by
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hqne : ((q : ℝ)) ≠ 0 := hqpos.ne'
  refine ⟨?_, ?_, ?_⟩
  · -- integrability: translate, then dilate
    have hmp : MeasureTheory.MeasurePreserving (fun v : ℝ => v + (r₀ : ℝ)) volume volume :=
      ⟨measurable_add_const _, by rw [MeasureTheory.map_add_right_eq_self volume (r₀ : ℝ)]⟩
    have htrans : MeasureTheory.Integrable (fun v : ℝ => γ (v + (r₀ : ℝ))) :=
      hmp.integrable_comp_of_integrable hγint
    simpa only [Function.comp_apply] using htrans.comp_mul_left' hqne
  · -- continuity
    exact hγcont.comp (by fun_prop)
  · -- Fourier support
    intro ξ hξ
    rw [show (fun t : ℝ => γ ((q : ℝ) * t + (r₀ : ℝ)))
        = (fun x : ℝ => (fun v : ℝ => γ (v + (r₀ : ℝ))) ((q : ℝ) * x)) from rfl]
    rw [Commons.Analysis.Fourier.fourier_comp_mul_left (fun v : ℝ => γ (v + (r₀ : ℝ))) hqpos ξ]
    rw [show (fun v : ℝ => γ (v + (r₀ : ℝ))) = (fun x : ℝ => γ (x - (-(r₀ : ℝ)))) from by
      funext v; congr 1; ring]
    rw [Commons.Analysis.Fourier.fourier_comp_sub γ (-(r₀ : ℝ)) (ξ / (q : ℝ))]
    have hband : FourierTransform.fourier γ (ξ / (q : ℝ)) = 0 := by
      apply hγband
      intro hmem
      have hcases : ξ < -((q : ℝ) * β) ∨ (q : ℝ) * β < ξ := by
        rcases lt_or_ge ξ (-((q : ℝ) * β)) with h | h
        · exact Or.inl h
        · exact Or.inr (lt_of_not_ge fun hle => hξ ⟨h, hle⟩)
      have hdiv : ξ / (q : ℝ) < -β ∨ β < ξ / (q : ℝ) := by
        rcases hcases with h | h
        · left
          rw [div_lt_iff₀ hqpos]
          linarith
        · right
          rw [lt_div_iff₀ hqpos]
          linarith
      rcases hdiv with h | h
      · exact absurd hmem.1 (not_le.mpr h)
      · exact absurd hmem.2 (not_le.mpr h)
    rw [hband, smul_zero, mul_zero]

end Work.KMTAreas.A7
