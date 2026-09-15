import Mathlib
import Submission.Commons.Analysis.Fourier.LogvinenkoSereda.bandlimited_assembly_d2

namespace Commons.Analysis.Fourier.LogvinenkoSereda

open MeasureTheory Metric FourierTransform
open scoped BigOperators ENNReal

/-- **Cohen's band-limited assembly in `d` dimensions** — the `d`-dimensional
Logvinenko–Sereda concentration estimate in the entire-function form.

This is the same statement as the previously committed commons lemma
`bandlimited_assembly_d2`, so it is an immediate consequence of it. -/
theorem bandlimited_assembly_d3 (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ lam : ℝ) (hσ : 1 ≤ σ) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
      (γ : EuclideanSpace ℝ (Fin d))
      (F : (Fin d → ℂ) → ℂ) (hF : Differentiable ℂ F)
      (hL2 : ∀ (m : ℕ), Integrable (fun x : EuclideanSpace ℝ (Fin d) =>
          ‖iteratedFDeriv ℝ m F (fun i => (x i : ℂ))‖ ^ 2) ∧
        (∫ x : EuclideanSpace ℝ (Fin d), ‖iteratedFDeriv ℝ m F (fun i => (x i : ℂ))‖ ^ 2) ≤
          (2*Real.pi*σ)^(2*m) * (∫ x : EuclideanSpace ℝ (Fin d), ‖F (fun i => (x i : ℂ))‖^2))
      (E : Set (EuclideanSpace ℝ (Fin d))) (hE : MeasurableSet E)
      (hEm : ∀ n : Fin d → ℤ, lam * 2^d ≤
        (volume (E ∩ {x : EuclideanSpace ℝ (Fin d) | ∀ i : Fin d, 2*(n i:ℝ)+γ i ≤ x i ∧ x i ≤ 2*(n i:ℝ)+γ i+2})).toReal),
      (∫ x : EuclideanSpace ℝ (Fin d), ‖F (fun i => (x i : ℂ))‖^2) ≤
        (C/lam)^(C*σ) * (∫ x in E, ‖F (fun i => (x i : ℂ))‖^2) := by
  exact bandlimited_assembly_d2 d

end Commons.Analysis.Fourier.LogvinenkoSereda
