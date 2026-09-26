import Mathlib
import Submission.Work.FunctionalEquations.Basic
import Submission.Work.FunctionalEquations.DifferenceExpansionF
import Submission.Work.FunctionalEquations.TauDifferenceExpansionF
import Submission.Work.FunctionalEquations.DifferenceExpansionFtilde
import Submission.Work.FunctionalEquations.TauDifferenceExpansionFtilde

namespace Work.FunctionalEquations

open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Filter Topology
open scoped FourierTransform SchwartzMap

/-- **CKMRV Theorem 3.1, Step 1 (paper (3.1)--(3.4))**: a solution of the functional
equations on the upper half plane gives, for each `x`, the four Dirichlet series

`F τ x - τ (F (τ+1) x - F τ x) = ∑_{m ≥ 1} a_m e^{2πimτ}`,
`(F (τ+1) x - F τ x)/(2πi) = ∑_{m ≥ 1} √(2m) b_m e^{2πimτ}`,

and the same for `F̃`, together with the contour-integral formulas for the coefficients
along any horizontal line `Im τ = y > 0`. -/
theorem ExpansionFromFunctionalEquations {n : ℕ} [NeZero n]
    (S : FunctionalEquationSolution n) (x : E n) :
    ∃ a b atilde btilde : Set.Ici (1 : ℕ) → ℂ,
      (∀ τ : ℂ, 0 < τ.im → HasSum (fun m : Set.Ici (1 : ℕ) =>
          a m * dirichletTerm m.1 τ)
        (S.F τ x - τ * (S.F (τ + 1) x - S.F τ x))) ∧
      (∀ τ : ℂ, 0 < τ.im → HasSum (fun m : Set.Ici (1 : ℕ) =>
          (rate m.1 : ℂ) * b m * dirichletTerm m.1 τ)
        ((S.F (τ + 1) x - S.F τ x) / (2 * (Real.pi : ℂ) * Complex.I))) ∧
      (∀ τ : ℂ, 0 < τ.im → HasSum (fun m : Set.Ici (1 : ℕ) =>
          atilde m * dirichletTerm m.1 τ)
        (S.Ftilde τ x - τ * (S.Ftilde (τ + 1) x - S.Ftilde τ x))) ∧
      (∀ τ : ℂ, 0 < τ.im → HasSum (fun m : Set.Ici (1 : ℕ) =>
          (rate m.1 : ℂ) * btilde m * dirichletTerm m.1 τ)
        ((S.Ftilde (τ + 1) x - S.Ftilde τ x) / (2 * (Real.pi : ℂ) * Complex.I))) ∧
      (∀ (m : Set.Ici (1 : ℕ)) (y : ℝ), 0 < y →
        b m = (2 * (Real.pi : ℂ) * Complex.I * (rate m.1 : ℂ))⁻¹ *
          ∫ t in (0 : ℝ)..1, (S.F ((t : ℂ) + (y : ℂ) * Complex.I + 1) x
              - S.F ((t : ℂ) + (y : ℂ) * Complex.I) x) *
            Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (m.1 : ℂ)
              * ((t : ℂ) + (y : ℂ) * Complex.I)))) ∧
      (∀ (m : Set.Ici (1 : ℕ)) (y : ℝ), 0 < y →
        a m = ∫ t in (0 : ℝ)..1,
          (S.F ((t : ℂ) + (y : ℂ) * Complex.I) x
            - ((t : ℂ) + (y : ℂ) * Complex.I) * (S.F ((t : ℂ) + (y : ℂ) * Complex.I + 1) x
              - S.F ((t : ℂ) + (y : ℂ) * Complex.I) x)) *
            Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (m.1 : ℂ)
              * ((t : ℂ) + (y : ℂ) * Complex.I)))) ∧
      (∀ (m : Set.Ici (1 : ℕ)) (y : ℝ), 0 < y →
        btilde m = (2 * (Real.pi : ℂ) * Complex.I * (rate m.1 : ℂ))⁻¹ *
          ∫ t in (0 : ℝ)..1, (S.Ftilde ((t : ℂ) + (y : ℂ) * Complex.I + 1) x
              - S.Ftilde ((t : ℂ) + (y : ℂ) * Complex.I) x) *
            Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (m.1 : ℂ)
              * ((t : ℂ) + (y : ℂ) * Complex.I)))) ∧
      (∀ (m : Set.Ici (1 : ℕ)) (y : ℝ), 0 < y →
        atilde m = ∫ t in (0 : ℝ)..1,
          (S.Ftilde ((t : ℂ) + (y : ℂ) * Complex.I) x
            - ((t : ℂ) + (y : ℂ) * Complex.I) * (S.Ftilde ((t : ℂ) + (y : ℂ) * Complex.I + 1) x
              - S.Ftilde ((t : ℂ) + (y : ℂ) * Complex.I) x)) *
            Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (m.1 : ℂ)
              * ((t : ℂ) + (y : ℂ) * Complex.I)))) := by
  obtain ⟨c, hc, hcf⟩ := Work.FunctionalEquations.DifferenceExpansionF S x
  obtain ⟨a, ha, haf⟩ := Work.FunctionalEquations.TauDifferenceExpansionF S x
  obtain ⟨c', hc', hc'f⟩ := Work.FunctionalEquations.DifferenceExpansionFtilde S x
  obtain ⟨atilde, ha', ha'f⟩ := Work.FunctionalEquations.TauDifferenceExpansionFtilde S x
  refine ⟨a, fun m => (2 * (Real.pi : ℂ) * Complex.I * (rate m.1 : ℂ))⁻¹ * c m, atilde,
    fun m => (2 * (Real.pi : ℂ) * Complex.I * (rate m.1 : ℂ))⁻¹ * c' m, ha, ?_, ha', ?_, ?_, haf, ?_, ha'f⟩
  · intro τ hτ
    have h := (hc τ hτ).mul_left ((2 * (Real.pi : ℂ) * Complex.I)⁻¹)
    rw [div_eq_inv_mul]
    refine h.congr_fun (fun m => ?_)
    have hR : (rate m.1 : ℂ) ≠ 0 := by
      have hpos : (0 : ℝ) < rate m.1 := by
        rw [rate]
        apply Real.sqrt_pos.mpr
        have : (1 : ℝ) ≤ (m.1 : ℝ) := by exact_mod_cast m.2
        linarith
      exact_mod_cast ne_of_gt hpos
    have hC : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      simp [Complex.I_ne_zero, Real.pi_ne_zero]
    have hCR : (2 * (Real.pi : ℂ) * Complex.I * (rate m.1 : ℂ)) ≠ 0 := mul_ne_zero hC hR
    field_simp
  · intro τ hτ
    have h := (hc' τ hτ).mul_left ((2 * (Real.pi : ℂ) * Complex.I)⁻¹)
    rw [div_eq_inv_mul]
    refine h.congr_fun (fun m => ?_)
    have hR : (rate m.1 : ℂ) ≠ 0 := by
      have hpos : (0 : ℝ) < rate m.1 := by
        rw [rate]
        apply Real.sqrt_pos.mpr
        have : (1 : ℝ) ≤ (m.1 : ℝ) := by exact_mod_cast m.2
        linarith
      exact_mod_cast ne_of_gt hpos
    have hC : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      simp [Complex.I_ne_zero, Real.pi_ne_zero]
    have hCR : (2 * (Real.pi : ℂ) * Complex.I * (rate m.1 : ℂ)) ≠ 0 := mul_ne_zero hC hR
    field_simp
  · intro m y hy
    show (2 * (Real.pi : ℂ) * Complex.I * (rate m.1 : ℂ))⁻¹ * c m = _
    rw [hcf m y hy]
  · intro m y hy
    show (2 * (Real.pi : ℂ) * Complex.I * (rate m.1 : ℂ))⁻¹ * c' m = _
    rw [hc'f m y hy]

end Work.FunctionalEquations
