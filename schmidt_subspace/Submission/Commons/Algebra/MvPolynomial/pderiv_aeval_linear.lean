import Submission.Commons.Algebra.MvPolynomial.pderiv_bind1
import Mathlib

namespace Commons.Algebra.MvPolynomial

open scoped BigOperators

theorem pderiv_aeval_linear {σ τ : Type*} [Fintype σ] [Fintype τ] [DecidableEq σ] [DecidableEq τ] (A : σ → τ → ℚ) (P : MvPolynomial σ ℚ) (y : τ) : MvPolynomial.pderiv y (MvPolynomial.aeval (fun x => ∑ z, MvPolynomial.C (A x z) * MvPolynomial.X z) P) = MvPolynomial.aeval (fun x => ∑ z, MvPolynomial.C (A x z) * MvPolynomial.X z) (∑ x : σ, MvPolynomial.C (A x y) * MvPolynomial.pderiv x P) := by
  classical
  have hf : ∀ x : σ, MvPolynomial.pderiv y (∑ z : τ, MvPolynomial.C (A x z) * MvPolynomial.X z) = MvPolynomial.C (A x y) := by
    intro x
    rw [map_sum]
    simp only [MvPolynomial.pderiv_C_mul]
    rw [Finset.sum_eq_single y]
    · simp
    · intro z _ hz
      rw [MvPolynomial.pderiv_X_of_ne hz, mul_zero]
    · intro hy
      exact absurd (Finset.mem_univ y) hy
  rw [MvPolynomial.aeval_eq_bind₁]
  rw [pderiv_bind1 (fun x => ∑ z, MvPolynomial.C (A x z) * MvPolynomial.X z) y P]
  simp_rw [hf]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul, MvPolynomial.bind₁_C_right]

end Commons.Algebra.MvPolynomial

