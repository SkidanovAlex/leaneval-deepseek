import Mathlib
import Submission.Work.FunctionalEquations.Coefficients
import Submission.Work.FunctionalEquations.ExpansionFromFunctionalEquations

namespace Work.FunctionalEquations

open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Filter Topology
open scoped FourierTransform SchwartzMap

theorem FunctionExpansion {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n) :
    (∀ (τ : ℂ) (x : E n), 0 < τ.im →
      S.F τ x = (∑' m : Set.Ici (1 : ℕ), aCoeff S m x * dirichletTerm m.1 τ)
        + (2 * (Real.pi : ℂ) * Complex.I * τ)
          * ∑' m : Set.Ici (1 : ℕ), (rate m.1 : ℂ) * bCoeff S m x * dirichletTerm m.1 τ) ∧
    (∀ (τ : ℂ) (x : E n), 0 < τ.im →
      S.Ftilde τ x = (∑' m : Set.Ici (1 : ℕ), aTildeCoeff S m x * dirichletTerm m.1 τ)
        + (2 * (Real.pi : ℂ) * Complex.I * τ)
          * ∑' m : Set.Ici (1 : ℕ), (rate m.1 : ℂ) * bTildeCoeff S m x * dirichletTerm m.1 τ) := by
  have hI : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    norm_num [Complex.I_ne_zero, Real.pi_ne_zero]
  constructor
  · intro τ x hτ
    obtain ⟨a, b, atilde, btilde, h1, h2, h3, h4, h5b, h5a, h5bt, h5at⟩ :=
      Work.FunctionalEquations.ExpansionFromFunctionalEquations S x
    have ha : ∀ m, a m = aCoeff S m x := by
      intro m
      rw [h5a m 1 (by norm_num)]
      unfold aCoeff aKernel
      simp only [Complex.ofReal_one, one_mul]
    have hb : ∀ m, b m = bCoeff S m x := by
      intro m
      rw [h5b m 1 (by norm_num)]
      unfold bCoeff bKernel
      simp only [Complex.ofReal_one, one_mul]
    have hA : (∑' m : Set.Ici (1 : ℕ), a m * dirichletTerm m.1 τ)
        = (∑' m : Set.Ici (1 : ℕ), aCoeff S m x * dirichletTerm m.1 τ) :=
      tsum_congr (fun m => by rw [ha m])
    have hB : (∑' m : Set.Ici (1 : ℕ), (rate m.1 : ℂ) * b m * dirichletTerm m.1 τ)
        = (∑' m : Set.Ici (1 : ℕ),
            (rate m.1 : ℂ) * bCoeff S m x * dirichletTerm m.1 τ) :=
      tsum_congr (fun m => by rw [hb m])
    rw [← hA, ← hB]
    rw [(h1 τ hτ).tsum_eq, (h2 τ hτ).tsum_eq]
    field_simp
    ring
  · intro τ x hτ
    obtain ⟨a, b, atilde, btilde, h1, h2, h3, h4, h5b, h5a, h5bt, h5at⟩ :=
      Work.FunctionalEquations.ExpansionFromFunctionalEquations S x
    have hat : ∀ m, atilde m = aTildeCoeff S m x := by
      intro m
      rw [h5at m 1 (by norm_num)]
      unfold aTildeCoeff
      simp only [Complex.ofReal_one, one_mul]
    have hbt : ∀ m, btilde m = bTildeCoeff S m x := by
      intro m
      rw [h5bt m 1 (by norm_num)]
      unfold bTildeCoeff
      simp only [Complex.ofReal_one, one_mul]
    have hA : (∑' m : Set.Ici (1 : ℕ), atilde m * dirichletTerm m.1 τ)
        = (∑' m : Set.Ici (1 : ℕ), aTildeCoeff S m x * dirichletTerm m.1 τ) :=
      tsum_congr (fun m => by rw [hat m])
    have hB : (∑' m : Set.Ici (1 : ℕ), (rate m.1 : ℂ) * btilde m * dirichletTerm m.1 τ)
        = (∑' m : Set.Ici (1 : ℕ),
            (rate m.1 : ℂ) * bTildeCoeff S m x * dirichletTerm m.1 τ) :=
      tsum_congr (fun m => by rw [hbt m])
    rw [← hA, ← hB]
    rw [(h3 τ hτ).tsum_eq, (h4 τ hτ).tsum_eq]
    field_simp
    ring

end Work.FunctionalEquations
