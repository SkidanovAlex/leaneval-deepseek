import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Matrix.PosDef

open scoped Matrix BigOperators ComplexOrder
open Matrix

namespace Commons.LinearAlgebra.Matrix

/-- If a matrix of weights `w` is doubly stochastic (nonneg, row and column sums are one),
then for any nonnegative family `z`, `∏ z ≤ ∏ i (∑ j, w i j * z j)`. -/
lemma doublyStochastic_prod_le_prod_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ι → ℝ) (z : ι → ℝ)
    (hw0 : ∀ i j, 0 ≤ w i j)
    (hrow : ∀ i, ∑ j : ι, w i j = 1)
    (hcol : ∀ j, ∑ i : ι, w i j = 1)
    (hz0 : ∀ j, 0 ≤ z j) :
    (∏ j : ι, z j) ≤ ∏ i : ι, (∑ j : ι, w i j * z j) := by
  classical
  -- Pointwise weighted AM-GM inequality for each row `i`.
  have hGM : ∀ i : ι, (∏ j : ι, z j ^ (w i j)) ≤ (∑ j : ι, w i j * z j) := by
    intro i
    exact Real.geom_mean_le_arith_mean_weighted (s := (Finset.univ : Finset ι))
      (fun j => w i j) z (by intro j _; exact hw0 i j)
      (by simpa using hrow i) (by intro j _; exact hz0 j)
  have hG0 : ∀ i : ι, 0 ≤ ∏ j : ι, z j ^ (w i j) := by
    intro i
    exact Finset.prod_nonneg (fun j _ => Real.rpow_nonneg (hz0 j) (w i j))
  -- The product of the geometric means equals `∏ z` because the column sums are one.
  have hprodG : (∏ i : ι, ∏ j : ι, z j ^ (w i j)) = ∏ j : ι, z j := by
    calc
      (∏ i : ι, ∏ j : ι, z j ^ (w i j))
          = ∏ j : ι, ∏ i : ι, z j ^ (w i j) := by
              simpa using (Finset.prod_comm : (∏ i ∈ (Finset.univ : Finset ι),
                ∏ j ∈ (Finset.univ : Finset ι), z j ^ (w i j)) =
                ∏ j ∈ (Finset.univ : Finset ι),
                ∏ i ∈ (Finset.univ : Finset ι), z j ^ (w i j))
      _ = ∏ j : ι, z j ^ (∑ i : ι, w i j) := by
              apply Finset.prod_congr rfl
              intro j _
              rw [Real.rpow_sum_of_nonneg (hz0 j) (fun i _ => hw0 i j)]
      _ = ∏ j : ι, z j := by
              apply Finset.prod_congr rfl
              intro j _
              rw [hcol j, Real.rpow_one]
  calc
    ∏ j : ι, z j = ∏ i : ι, ∏ j : ι, z j ^ (w i j) := hprodG.symm
    _ ≤ ∏ i : ι, (∑ j : ι, w i j * z j) := by
        exact Finset.prod_le_prod₀ (s := (Finset.univ : Finset ι))
          (f := fun i => ∏ j : ι, z j ^ (w i j))
          (g := fun i => ∑ j : ι, w i j * z j)
          (by intro i _; exact hG0 i)
          (by intro i _; exact hGM i)

/-- The rows of an orthogonal real matrix have squared norm one. -/
lemma orthogonal_row_sum_sq {n : ℕ} (U : Matrix (Fin n) (Fin n) ℝ) (hUU : U * Uᵀ = 1) :
    ∀ i : Fin n, (∑ k : Fin n, U i k * U i k) = 1 := by
  classical
  intro i
  calc
    (∑ k : Fin n, U i k * U i k) = (U * Uᵀ) i i := by simp [Matrix.mul_apply]
    _ = 1 := by rw [hUU]; simp

/-- The columns of an orthogonal real matrix have squared norm one. -/
lemma orthogonal_col_sum_sq {n : ℕ} (U : Matrix (Fin n) (Fin n) ℝ) (hUU : Uᵀ * U = 1) :
    ∀ k : Fin n, (∑ i : Fin n, U i k * U i k) = 1 := by
  classical
  intro k
  calc
    (∑ i : Fin n, U i k * U i k) = (Uᵀ * U) k k := by simp [Matrix.mul_apply]
    _ = 1 := by rw [hUU]; simp

/-- The diagonal entries of a matrix diagonalized as `U * diagonal lam * Uᵀ` (with `U` orthogonal)
are the weighted sums `∑ k, (U i k)^2 * lam k`. -/
lemma diagonalization_diag_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (U : Matrix (Fin n) (Fin n) ℝ) (lam : Fin n → ℝ)
    (hspec : A = U * Matrix.diagonal lam * Uᵀ) :
    ∀ i : Fin n, A i i = ∑ k : Fin n, U i k * U i k * lam k := by
  classical
  intro i
  conv_lhs => rw [hspec]
  simp [Matrix.mul_apply, Matrix.diagonal_apply]
  ring_nf

lemma det_le_prod_diag_of_posSemidef {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosSemidef) : A.det ≤ ∏ i : Fin n, A i i := by
  classical
  let hherm : A.IsHermitian := hA.1
  let U : Matrix (Fin n) (Fin n) ℝ := hherm.eigenvectorUnitary
  let lam : Fin n → ℝ := hherm.eigenvalues
  have hUU : U * Uᵀ = 1 := by
    have h := Unitary.coe_mul_star_self (U := hherm.eigenvectorUnitary)
    simpa [U, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using h
  have hUUt : Uᵀ * U = 1 := by
    have h := Unitary.coe_star_mul_self (U := hherm.eigenvectorUnitary)
    simpa [U, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using h
  have hspec : A = U * Matrix.diagonal lam * Uᵀ := by
    have h' := hherm.spectral_theorem (𝕜 := ℝ)
    rw [Unitary.conjStarAlgAut_apply] at h'
    simpa [U, lam, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using h'
  have hrow : ∀ i : Fin n, (∑ k : Fin n, U i k * U i k) = 1 :=
    orthogonal_row_sum_sq U hUU
  have hcol : ∀ k : Fin n, (∑ i : Fin n, U i k * U i k) = 1 :=
    orthogonal_col_sum_sq U hUUt
  have hdiag : ∀ i : Fin n, A i i = ∑ k : Fin n, U i k * U i k * lam k :=
    diagonalization_diag_eq A U lam hspec
  have hlam0 : ∀ k : Fin n, 0 ≤ lam k := by
    intro k
    simpa [lam] using hA.eigenvalues_nonneg k
  calc
    A.det = ∏ k : Fin n, lam k := by
      simpa [lam] using hherm.det_eq_prod_eigenvalues (𝕜 := ℝ)
    _ ≤ ∏ i : Fin n, (∑ k : Fin n, (U i k * U i k) * lam k) := by
      exact doublyStochastic_prod_le_prod_sum (fun i k => U i k * U i k) lam
        (by intro i k; exact mul_self_nonneg (U i k)) hrow hcol hlam0
    _ = ∏ i : Fin n, A i i := by
      apply Finset.prod_congr rfl
      intro i _
      exact (hdiag i).symm

end Commons.LinearAlgebra.Matrix