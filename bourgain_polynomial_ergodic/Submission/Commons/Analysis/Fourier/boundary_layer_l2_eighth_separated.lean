import Mathlib
import Submission.Commons.Analysis.Fourier.boundary_layer_eighth_separated_real
import Submission.Commons.Analysis.Fourier.boundary_layer_l2

namespace Commons.Analysis.Fourier

open MeasureTheory
open scoped ENNReal

/-- **Boundary-layer `L²` square-function bound for `1/8`-separated frequencies**, phrased with the
`ℝ≥0∞`-valued `enorm` on the right-hand side.

This is an immediate consequence of `boundary_layer_eighth_separated_real`: for a complex number
`z` one has `‖z‖ₑ = ENNReal.ofReal ‖z‖` (`BoundaryLayer.enorm_eq_ofReal_norm`), so the two
statements differ only in how the `L²` norm of `f` is written. -/
theorem boundary_layer_l2_eighth_separated :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (lam : Fin N → ℝ),
      (∀ i j : Fin N, i ≠ j → (2 : ℝ) ^ (-(3 : ℤ)) ≤ |lam i - lam j|) →
      ∀ (φ : ℝ → ℝ), (∀ x : ℝ, |x| ≤ 1 / 2 → φ x = 1) →
        (∀ x : ℝ, 1 ≤ |x| → φ x = 0) → (∀ x : ℝ, 0 ≤ φ x ∧ φ x ≤ 1) →
      ∀ (f : ℝ → ℂ), MeasureTheory.MemLp f 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ) →
        ∫⁻ x : ℝ, (∑' j : ℕ,
            ENNReal.ofReal ‖∫ y : ℝ, f y *
            (∑ k : Fin N,
              ∫ θ in (lam k - (2 : ℝ) ^ (-(j : ℝ) - 1))..(lam k + (2 : ℝ) ^ (-(j : ℝ) - 1)),
                ((1 - φ ((θ - lam k) / (2 : ℝ) ^ (-(j : ℝ) - 1))) : ℂ) *
                  Complex.exp (-(2 * Real.pi * Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))))‖ ^ (2 : ℝ))
          ∂MeasureTheory.volume
        ≤ ENNReal.ofReal (C^2) * ∫⁻ x : ℝ, ‖f x‖ₑ ^ (2 : ℝ) ∂MeasureTheory.volume := by
  obtain ⟨C, hC, h⟩ := boundary_layer_eighth_separated_real
  refine ⟨C, hC, ?_⟩
  intro N lam hsep φ h1 h0 hbdd f hf
  simp only [BoundaryLayer.enorm_eq_ofReal_norm]
  exact h N lam hsep φ h1 h0 hbdd f hf

end Commons.Analysis.Fourier
