import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace Commons.LinearAlgebra.Matrix

open Polynomial
open scoped BigOperators

/-- The natDegree of a determinant of a matrix with polynomial entries is bounded by
the sum over columns of the maximal natDegree in that column. -/
theorem det_natDegree_le {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [CommRing R]
    (M : Matrix ι ι R[X]) (D : ι → ℕ) (hD : ∀ i j, (M i j).natDegree ≤ D j) :
    M.det.natDegree ≤ ∑ j : ι, D j := by
  rw [Matrix.det_apply]
  have hterm : ∀ σ : Equiv.Perm ι,
      ((Equiv.Perm.sign σ • ∏ i : ι, M (σ i) i).natDegree) ≤ ∑ j : ι, D j := by
    intro σ
    calc
      ((Equiv.Perm.sign σ • ∏ i : ι, M (σ i) i).natDegree)
          ≤ (∏ i : ι, M (σ i) i).natDegree := by
            exact Polynomial.natDegree_smul_le (Equiv.Perm.sign σ) (∏ i : ι, M (σ i) i)
      _ ≤ ∑ i : ι, (M (σ i) i).natDegree := by
            simpa using (Polynomial.natDegree_prod_le (Finset.univ : Finset ι) (fun i => M (σ i) i))
      _ ≤ ∑ i : ι, D i := by
            exact Finset.sum_le_sum (fun i hi => hD (σ i) i)
      _ = ∑ j : ι, D j := by
            rfl
  exact Polynomial.natDegree_sum_le_of_forall_le (Finset.univ : Finset (Equiv.Perm ι))
    (fun σ : Equiv.Perm ι => Equiv.Perm.sign σ • (∏ i : ι, M (σ i) i))
    (fun σ hσ => hterm σ)

end Commons.LinearAlgebra.Matrix