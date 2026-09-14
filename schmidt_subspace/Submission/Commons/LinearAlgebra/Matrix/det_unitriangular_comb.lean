import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Nonsingular

namespace Commons.LinearAlgebra.Matrix

-- Let `xs j` (`j : Fin N`) be integer vectors that are `ℚ`-linearly independent, and let `ξ`
-- be an integer matrix with `ξ i j = 0` whenever `j ≤ i`.  Then the "straightened" vectors
-- `v j i = xs j i + ∑ p, xs p i * ξ p j` (i.e. `V = X * (1 + ξ)` where the columns of `X` are the
-- `xs j`) have a nonzero determinant.  Proof: `V = X * (1 + ξ)`, `det X ≠ 0` (independent
-- columns) and `1 + ξ` is upper triangular with all diagonal entries `1`, hence `det (1+ξ) = 1`.
theorem det_unitriangular_comb {N : ℕ} (xs : Fin N → Fin N → ℤ) (ξ : Fin N → Fin N → ℤ)
    (hξ : ∀ i j, j ≤ i → ξ i j = 0)
    (hli : LinearIndependent ℚ (fun j : Fin N => fun i : Fin N => (xs j i : ℚ))) :
    (Matrix.of (fun i j : Fin N => xs j i + ∑ p : Fin N, xs p i * ξ p j)).det ≠ 0 := by
  classical
  set V : Matrix (Fin N) (Fin N) ℤ := Matrix.of (fun i j => xs j i + ∑ p, xs p i * ξ p j) with hVdef
  set X : Matrix (Fin N) (Fin N) ℤ := Matrix.of (fun i j => xs j i) with hXdef
  set U : Matrix (Fin N) (Fin N) ℤ := 1 + Matrix.of (fun p j => ξ p j) with hUdef
  -- `V` is the product of `X` (columns the `xs j`) with the unitriangular matrix `1 + ξ`.
  have hVXU : V = X * U := by
    ext i j
    simp only [hVdef, hXdef, hUdef, Matrix.of_apply, Matrix.mul_apply, Matrix.add_apply,
      Matrix.one_apply]
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib]
    have h1 : (∑ x, xs x i * (if x = j then 1 else 0)) = xs j i := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro p _ hp; simp [hp]
      · intro hj; exact absurd (Finset.mem_univ j) hj
    rw [h1]
  -- `1 + ξ` is upper triangular with unit diagonal, hence has determinant `1`.
  have hUdet : U.det = 1 := by
    rw [hUdef, Matrix.det_of_isUpperTriangular]
    · simp only [Matrix.add_apply, Matrix.one_apply, Matrix.of_apply]
      refine Finset.prod_eq_one fun j _ => ?_
      simp [hξ j j le_rfl]
    · intro i j hij
      have hne : i ≠ j := ne_of_gt hij
      simp only [Matrix.add_apply, Matrix.one_apply, Matrix.of_apply]
      simp [hne, hξ i j (le_of_lt hij)]
  -- The columns of `X` over `ℚ` are linearly independent, hence `det X ≠ 0`.
  have hXq : (X.map (fun x : ℤ => (x : ℚ))).det ≠ 0 := by
    rw [← Matrix.nonsingular_iff_det_ne_zero, ← Matrix.linearIndependent_col_iff]
    have hcol : (X.map (fun x : ℤ => (x : ℚ))).col = fun j i => (xs j i : ℚ) := by
      ext j i; simp [hXdef, Matrix.col, Matrix.map_apply]
    rw [hcol]
    exact hli
  have hXdet : X.det ≠ 0 := by
    intro h
    refine hXq ?_
    rw [← Int.cast_det X, h]
    simp
  intro hVdet
  have hzero : V.det = 0 := hVdet
  rw [hVXU, Matrix.det_mul, hUdet, mul_one] at hzero
  exact hXdet hzero

end Commons.LinearAlgebra.Matrix