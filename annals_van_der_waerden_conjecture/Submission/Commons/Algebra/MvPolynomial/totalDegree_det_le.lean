import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace Commons.Algebra.MvPolynomial

open Finset

theorem totalDegree_det_le {R : Type*} [CommRing R] {σ : Type*} {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (MvPolynomial σ R))
    (h : ∀ i j, (A i j).totalDegree ≤ (i : ℕ) + (j : ℕ)) :
    A.det.totalDegree ≤ n * (n - 1) := by
  rw [Matrix.det_apply]
  refine MvPolynomial.totalDegree_finsetSum_le (fun τ _ => ?_)
  calc (Equiv.Perm.sign τ • ∏ i, A (τ i) i).totalDegree
      ≤ (∏ i, A (τ i) i).totalDegree := MvPolynomial.totalDegree_smul_le _ _
    _ ≤ ∑ i : Fin n, (A (τ i) i).totalDegree := MvPolynomial.totalDegree_finsetProd _ _
    _ ≤ ∑ i : Fin n, ((τ i : ℕ) + (i : ℕ)) :=
        Finset.sum_le_sum (fun i _ => h (τ i) i)
    _ = n * (n - 1) := by
        rw [Finset.sum_add_distrib]
        have hperm : ∑ i : Fin n, ((τ i : ℕ)) = ∑ i : Fin n, (i : ℕ) :=
          Equiv.sum_comp τ (fun i => (i : ℕ))
        rw [hperm]
        have h2 : (∑ i : Fin n, (i : ℕ)) * 2 = n * (n - 1) := by
          rw [← Finset.sum_range_id_mul_two n]
          congr 1
          exact Fin.sum_univ_eq_sum_range (fun i => i) n
        omega

end Commons.Algebra.MvPolynomial