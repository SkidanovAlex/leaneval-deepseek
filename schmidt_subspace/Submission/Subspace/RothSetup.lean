import Mathlib
import Submission.Subspace.RothTransfer
import Submission.Commons.Algebra.Polynomial.exists_minimal_decomposition
import Submission.Commons.Algebra.Polynomial.wronskian_linearIndependent
import Submission.Commons.Algebra.MvPolynomial.linearIndependent_iff_exists_wronskian

/-!
# Wronskian data for a multivariate polynomial (the Roth setup)

Given `P ∈ K[x_0, …, x_n]` (`K` a field of characteristic zero) we produce the data used by the
multivariate Roth lemma: a *minimal decomposition*
`P = ∑_{j<k} Φ_j Ψ_j` into products of a polynomial in `x_1,…,x_n` and a polynomial in `x_0`,
together with multi-indices `μ_i` (`|μ_i| ≤ i`) and the two nonzero Wronskians
`det (∂^{μ_i} Φ_j)` and `det (∂^{i e_0} Ψ_j)`.  The shortest such decomposition has length
`k ≤ deg_{x_0} P + 1`.
-/

open MvPolynomial

namespace Submission.Subspace

variable {K : Type*} [Field K] [CharZero K] {n : ℕ}

/-- **The Wronskian data of a multivariate polynomial.** -/
theorem exists_roth_data (P : MvPolynomial (Fin (n + 1)) K) :
    ∃ (k : ℕ) (φ : Fin k → MvPolynomial (Fin n) K) (ψ : Fin k → Polynomial K)
      (μ : Fin k → Fin n →₀ ℕ),
      P = ∑ j, MvPolynomial.rename Fin.succ (φ j) *
            Polynomial.aeval (A := MvPolynomial (Fin (n + 1)) K) (MvPolynomial.X 0) (ψ j) ∧
      (∀ i, (μ i).sum (fun _ m => m) ≤ (i : ℕ)) ∧
      (Matrix.of fun i j : Fin k =>
        Commons.Algebra.MvPolynomial.pderivIter (μ i) (φ j)).det ≠ 0 ∧
      (Matrix.of fun i j : Fin k => (Polynomial.derivative^[(i : ℕ)]) (ψ j)).det ≠ 0 ∧
      (P ≠ 0 → k ≤ MvPolynomial.degreeOf 0 P + 1) := by
  classical
  obtain ⟨k, φ, ψ, hdec, hindφ, hindψ, hk⟩ :=
    Commons.Algebra.Polynomial.exists_minimal_decomposition
      (MvPolynomial.finSuccEquiv K n P)
  -- the multi-indices μ of the (n)-variable Wronskian
  obtain ⟨μ, hμ, hdetμ⟩ :=
    Commons.Algebra.MvPolynomial.exists_wronskian_det_ne_zero_of_linearIndependent φ hindφ
  -- the decomposition transported to the variable presentation
  have hdec' : P = ∑ j, MvPolynomial.rename Fin.succ (φ j) *
      Polynomial.aeval (A := MvPolynomial (Fin (n + 1)) K) (MvPolynomial.X 0) (ψ j) := by
    conv_lhs => rw [← AlgEquiv.symm_apply_apply (MvPolynomial.finSuccEquiv K n) P]
    rw [hdec, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, finSuccEquiv_symm_C, finSuccEquiv_symm_map_C]
  refine ⟨k, φ, ψ, μ, hdec', hμ, hdetμ,
    Commons.Algebra.Polynomial.wronskian_linearIndependent ψ hindψ, ?_⟩
  intro hP
  rw [← MvPolynomial.natDegree_finSuccEquiv]
  exact hk (fun h => hP ((MvPolynomial.finSuccEquiv K n).injective (by rw [h, map_zero])))

end Submission.Subspace
