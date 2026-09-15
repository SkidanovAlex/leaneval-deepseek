import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-!
# Integrals over `Fin 1 → ℝ`

The Lebesgue measure on `Fin 1 → ℝ` is the push-forward of Lebesgue measure on `ℝ` under the
map `s ↦ (fun _ : Fin 1 => s)`. Consequently, the Bochner integral of a function
`f : (Fin 1 → ℝ) → ℂ` against Lebesgue measure on `Fin 1 → ℝ` coincides with the integral over
`ℝ` of the function `s ↦ f (fun _ => s)`.

This is the Bochner (i.e. `ℂ`-valued) counterpart of the `ℝ≥0∞`-valued statement
`Commons.Analysis.Inequalities.lintegral_const_fin_one`.
-/

open MeasureTheory

namespace Commons.Analysis.Measure

/-- The measurable equivalence `(Fin 1 → ℝ) ≃ᵐ ℝ` is measure preserving, hence its inverse
`ℝ → (Fin 1 → ℝ)`, `s ↦ (fun _ => s)`, transports Lebesgue measure on `ℝ` to Lebesgue
measure on `Fin 1 → ℝ`. -/
theorem integral_fin_one (f : (Fin 1 → ℝ) → ℂ) :
    (∫ t : Fin 1 → ℝ, f t) = ∫ s : ℝ, f (fun _ => s) := by
  have h : MeasurePreserving (MeasurableEquiv.piUnique (fun _ : Fin 1 => ℝ)).symm
      volume (volume : Measure (Fin 1 → ℝ)) :=
    (volume_preserving_piUnique (fun _ : Fin 1 => ℝ)).symm
  rw [← h.integral_comp' f]
  refine integral_congr_ae ?_
  filter_upwards with s
  have he : (MeasurableEquiv.piUnique (fun _ : Fin 1 => ℝ)).symm s = (fun _ : Fin 1 => s) := by
    funext i
    rw [MeasurableEquiv.piUnique_symm_apply]
    simp [uniqueElim]
  rw [he]

end Commons.Analysis.Measure