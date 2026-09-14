import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace Commons.Algebra.Matrix

open Matrix

/-
**Multilinearity of the determinant in the rows (expansion of a sum).**

If the `k`-th row of a square matrix `A` is a finite linear combination
`A k = ∑ i, c k i • row k i` of given row vectors, then
`A.det = ∑ f, (∏ k, c k (f k)) * (Matrix.of (fun k => row k (f k))).det`,
the sum being over all functions `f` choosing an index `f k` for every row `k`.

Suggested proof: use `Matrix.det_apply` and expand the product of sums with
`Finset.prod_univ_sum`, then exchange the two sums. -/
theorem det_eq_sum_of_rows {n : ℕ} {R : Type*} [CommRing R]
    {ι : Fin n → Type*} [∀ k, Fintype (ι k)]
    (A : Matrix (Fin n) (Fin n) R) (row : (k : Fin n) → ι k → (Fin n → R))
    (c : (k : Fin n) → ι k → R)
    (hA : ∀ k, A k = ∑ i, c k i • row k i) :
    A.det = ∑ f : ((k : Fin n) → ι k),
      (∏ k, c k (f k)) * (Matrix.of (fun k => row k (f k))).det := by
  classical
  -- The determinant as an alternating (hence multilinear) map on the rows.
  let D : MultilinearMap R (fun _ : Fin n => (Fin n → R)) R :=
    (Matrix.detRowAlternating : (Fin n → R) [⋀^Fin n]→ₗ[R] R)
  -- Replace `A` by the matrix whose rows are the given linear combinations.
  have hAf : A = Matrix.of (fun k => ∑ i, c k i • row k i) := by
    ext k j
    rw [Matrix.of_apply]
    exact congr_fun (hA k) j
  rw [hAf]
  -- `det` is `D` applied to the rows.
  have hDet : (Matrix.of (fun k => ∑ i, c k i • row k i)).det
      = D (fun k => ∑ i, c k i • row k i) := rfl
  rw [hDet, MultilinearMap.map_sum D (fun k i => c k i • row k i)]
  -- Now each summand is a multilinear map applied to scaled rows.
  apply Finset.sum_congr rfl
  intro f _
  rw [MultilinearMap.map_smul_univ D (fun k => c k (f k)) (fun k => row k (f k))]
  rw [show D (fun k => row k (f k)) = (Matrix.of (fun k => row k (f k))).det from rfl]
  rw [smul_eq_mul]

end Commons.Algebra.Matrix