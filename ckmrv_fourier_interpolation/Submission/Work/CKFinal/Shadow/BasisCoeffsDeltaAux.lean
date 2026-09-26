import Submission.Work.FunctionalEquations.BasisCoeffsDeltaAux
import Submission.Work.CKFinal.Shadow.Util
import Submission.Work.CKFinal.Shadow.Basic
import Submission.Work.CKFinal.Shadow.SummableExpansionTerms

open scoped ContDiff
set_option linter.dupNamespace false

namespace Work.CKFinal.Shadow

namespace Work.FunctionalEquations.BasisDelta
export _root_.Work.FunctionalEquations.BasisDelta (radialDeriv_zero_eq)
end Work.FunctionalEquations.BasisDelta

/-!
# Auxiliary material for the Kronecker-delta pattern of the interpolation basis

This file collects the general-purpose lemmas used in
`Submission.Work.FunctionalEquations.BasisCoeffsDelta` to deduce the Kronecker-delta
pattern for the samples of the coefficient families `a_n, ã_n, b_n, b̃_n` of an
`InterpolationSolution`.

The mathematics is the elementary part of CKMRV Section 8:

* the Dirichlet kernel `dirichletTerm m τ = e^{2 π i m τ}` is `1`-periodic in `τ`, hence
  so is any Dirichlet series `τ ↦ ∑' m, c m * dirichletTerm m τ`;
* splitting off the `τ`-linear part of such a series (`PeriodicAddSmulUHP`) identifies
  both the periodic and the linear coefficient series;
* uniqueness of Dirichlet coefficients (`DirichletCoeffUnique`), proved by integrating
  against characters (`EqZeroOfTsumExp`), turns the resulting identity of series into an
  identity of coefficients;
* polynomial growth of the coefficient families at a sample point
  (`basis_sample_bound`, `radialDeriv_basis_sample_bound`) supplies the absolute
  convergence needed for the uniqueness step.
-/

namespace Work.FunctionalEquations.BasisDelta

open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Filter Topology
open scoped FourierTransform SchwartzMap

/-- Polynomial growth of the coefficient families at the sample point of index `k`. -/
lemma basis_sample_bound {n : ℕ} [NeZero n] (S : InterpolationSolution n) (j : Fin 4)
    (k : Set.Ici (1 : ℕ)) :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ m : Set.Ici (1 : ℕ),
      ‖(S.basis (m, j)).1 (samplePoint (n := n) (k.1 : ℝ))‖ ≤ C * ((m.1 : ℝ) + 1) ^ N := by
  obtain ⟨C, N, hC, h⟩ := S.growth_radial 0 0
  refine ⟨C, N, hC, fun m => ?_⟩
  have h1 := h m j (samplePoint (n := n) (k.1 : ℝ))
  rw [pow_zero, one_mul, radialDeriv_zero_eq] at h1
  exact h1

/-- Polynomial growth of the radial derivatives of the coefficient families at the
sample point of index `k`. -/
lemma radialDeriv_basis_sample_bound {n : ℕ} [NeZero n] (S : InterpolationSolution n)
    (j : Fin 4) (k : Set.Ici (1 : ℕ)) :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ m : Set.Ici (1 : ℕ),
      ‖radialDeriv 1 (⇑(S.basis (m, j)).1) (samplePoint (n := n) (k.1 : ℝ))‖
        ≤ C * ((m.1 : ℝ) + 1) ^ N := by
  obtain ⟨C, N, hC, h⟩ := S.growth_radial 0 1
  refine ⟨C, N, hC, fun m => ?_⟩
  have h1 := h m j (samplePoint (n := n) (k.1 : ℝ))
  rw [pow_zero, one_mul] at h1
  exact h1

end Work.FunctionalEquations.BasisDelta


end Work.CKFinal.Shadow
