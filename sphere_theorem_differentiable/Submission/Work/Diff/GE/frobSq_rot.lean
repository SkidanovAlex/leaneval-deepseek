import Mathlib
import Submission.Work.Diff.GE.deps

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators Matrix
open Bundle ContDiff Set VectorField CovariantDerivative Metric

/-!
# `N4 (A Aᵀ) (rot A R) = frobSq R` for an invertible matrix `A`

`N4 Γ R` is the full contraction of `R` with the inverse of `Γ` (see
`Submission.Work.Diff.GE.norms_defs`), and `rot A R` is the change of an orthonormal frame by `A`.
The identity `N4 (A Aᵀ) (rot A R) = frobSq R` is the statement that the curvature norm computed in
a `g`-orthonormal frame is independent of the frame also when the frame change is a *non*-orthogonal
matrix, provided the Gram matrix `A Aᵀ` is used to raise the indices.

The strategy: flatten `Curv4 n` to the pair-indexed matrix `fsr_toM R` (`R i j k l ↦ R (i,j) (k,l)`).
Then

* `fsr_toM (rot A R) = (A ⊗ A) * fsr_toM R * (A ⊗ A)ᵀ` (`fsr_toM_rot`),
* `N4 Γ R = trace ((fsr_toM R) * ((fsr_toM (rot Γ⁻¹ R))ᵀ))` (`fsr_N4_trace`),
* and the remaining statement is the purely matrix-theoretic cyclicity computation
  `fsr_trace_algebra`, using `A ⊗ A = kronecker A A` and `(A Aᵀ)⁻¹ A Aᵀ (A ⊗ A) = 1`.
-/

/-! ## Sum reindexing helpers -/

/-- Swap the two blocks `(a,b,c,d)` and `(c,d,a,b)` of a fourfold sum. -/
theorem fsr_bswap22 {n : ℕ} (g : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, g a b c d) = ∑ c, ∑ d, ∑ a, ∑ b, g a b c d := by
  have hL : (∑ a, ∑ b, ∑ c, ∑ d, g a b c d)
      = ∑ x : Fin n × Fin n, ∑ y : Fin n × Fin n, g x.1 x.2 y.1 y.2 := by
    rw [← Fintype.sum_prod_type']
    apply Finset.sum_congr rfl
    intro x _
    rw [← Fintype.sum_prod_type']
  have hR : (∑ c, ∑ d, ∑ a, ∑ b, g a b c d)
      = ∑ y : Fin n × Fin n, ∑ x : Fin n × Fin n, g x.1 x.2 y.1 y.2 := by
    rw [← Fintype.sum_prod_type']
    apply Finset.sum_congr rfl
    intro y _
    rw [← Fintype.sum_prod_type']
  rw [hL, hR, Finset.sum_comm]

/-- Group a fourfold sum into a sum over pairs. -/
theorem fsr_grp4 {n : ℕ} (H : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, H a b c d)
      = ∑ x : Fin n × Fin n, ∑ y : Fin n × Fin n, H x.1 x.2 y.1 y.2 := by
  rw [← Fintype.sum_prod_type']
  apply Finset.sum_congr rfl
  intro x _
  rw [← Fintype.sum_prod_type']

/-! ## Flattening `Curv4` to matrices -/

/-- A `(0,4)`-tensor array as a matrix indexed by pairs, `R i j k l ↦ R (i,j) (k,l)`. -/
noncomputable def fsr_toM {n : ℕ} (R : Curv4 n) : Matrix (Fin n × Fin n) (Fin n × Fin n) ℝ :=
  fun p q => R p.1 p.2 q.1 q.2

/-- The frame change `rot A` is the congruence action by the Kronecker square `A ⊗ A`. -/
theorem fsr_toM_rot {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (R : Curv4 n) :
    fsr_toM (rot A R) = Matrix.kronecker A A * fsr_toM R * (Matrix.kronecker A A).transpose := by
  ext p q
  simp only [fsr_toM, rot, Matrix.mul_apply, Matrix.transpose_apply, Matrix.kronecker,
    Matrix.kroneckerMap_apply]
  simp only [Finset.sum_mul]
  rw [fsr_grp4]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro y _
  apply Finset.sum_congr rfl; intro x _
  ring

/-- `N4 Γ R` contracted with the standard pairing inside `Curv4`. -/
lemma fsr_N4_eq {n : ℕ} (Γ : Matrix (Fin n) (Fin n) ℝ) (R : Curv4 n) :
    N4 Γ R = ∑ i, ∑ j, ∑ k, ∑ l, R i j k l * (rot Γ⁻¹ R) i j k l := by
  simp only [N4, rot, Finset.mul_sum]
  repeat (apply Finset.sum_congr rfl; intro _ _)
  ring

/-- The standard pairing inside `Curv4` is the trace of `M Nᵀ`. -/
lemma fsr_trace_mul_transpose_toM {n : ℕ} (R S : Curv4 n) :
    Matrix.trace (fsr_toM R * (fsr_toM S)ᵀ) = ∑ i, ∑ j, ∑ k, ∑ l, R i j k l * S i j k l := by
  rw [Matrix.trace]
  simp only [Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, fsr_toM]
  simp only [Fintype.sum_prod_type]

/-- `N4 Γ R` as a trace of flattened matrices. -/
lemma fsr_N4_trace {n : ℕ} (Γ : Matrix (Fin n) (Fin n) ℝ) (R : Curv4 n) :
    N4 Γ R = Matrix.trace (fsr_toM R * (fsr_toM (rot Γ⁻¹ R))ᵀ) := by
  rw [fsr_N4_eq, fsr_trace_mul_transpose_toM]

/-! ## Kronecker calculus -/

/-- Multiplication of Kronecker squares. -/
lemma fsr_kron_mul {n : ℕ} (X Y : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.kronecker X X * Matrix.kronecker Y Y = Matrix.kronecker (X * Y) (X * Y) :=
  (Matrix.mul_kronecker_mul X Y X Y).symm

/-- The Kronecker square of the identity is the identity. -/
lemma fsr_kron_one {n : ℕ} :
    Matrix.kronecker (1 : Matrix (Fin n) (Fin n) ℝ) (1 : Matrix (Fin n) (Fin n) ℝ) =
      (1 : Matrix (Fin n × Fin n) (Fin n × Fin n) ℝ) :=
  Matrix.one_kronecker_one

/-- The transpose of a Kronecker square. -/
lemma fsr_kron_tr {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) :
    (Matrix.kronecker X X)ᵀ = Matrix.kronecker Xᵀ Xᵀ :=
  (Matrix.kroneckerMap_transpose (fun a b : ℝ => a * b) X X).symm

/-! ## The matrix computation -/

/-- The core cyclicity computation, with `Γ = A Aᵀ`. -/
lemma fsr_trace_algebra {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det)
    (M : Matrix (Fin n × Fin n) (Fin n × Fin n) ℝ) :
    Matrix.trace ((Matrix.kronecker A A * M * (Matrix.kronecker A A)ᵀ) *
      ((Matrix.kronecker ((A * Aᵀ)⁻¹) ((A * Aᵀ)⁻¹) *
        (Matrix.kronecker A A * M * (Matrix.kronecker A A)ᵀ) *
        (Matrix.kronecker ((A * Aᵀ)⁻¹) ((A * Aᵀ)⁻¹))ᵀ))ᵀ)
      = Matrix.trace (M * Mᵀ) := by
  have hAt : IsUnit Aᵀ.det := by rwa [Matrix.det_transpose]
  have h1 : Aᵀ * (A * Aᵀ)⁻¹ * A = 1 := by
    rw [Matrix.mul_inv_rev]
    rw [Matrix.mul_assoc, Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul A hA, Matrix.mul_one, Matrix.mul_nonsing_inv Aᵀ hAt]
  have h3 : Aᵀ * (A * Aᵀ)⁻¹ = A⁻¹ := by
    rw [Matrix.mul_inv_rev]
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv Aᵀ hAt, Matrix.one_mul]
  have h4 : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hA
  have hAAt : (A * Aᵀ)ᵀ = A * Aᵀ := by rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  have hBt : ((A * Aᵀ)⁻¹)ᵀ = (A * Aᵀ)⁻¹ := by rw [Matrix.transpose_nonsing_inv, hAAt]
  have hmid : ∀ X : Matrix (Fin n × Fin n) (Fin n × Fin n) ℝ,
      (Matrix.kronecker A A)ᵀ * (Matrix.kronecker ((A * Aᵀ)⁻¹) ((A * Aᵀ)⁻¹) *
        (Matrix.kronecker A A * X)) = X := by
    intro X
    rw [fsr_kron_tr]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, fsr_kron_mul, fsr_kron_mul, h1, fsr_kron_one,
      Matrix.one_mul]
  have hend : (Matrix.kronecker A A)ᵀ * (Matrix.kronecker ((A * Aᵀ)⁻¹) ((A * Aᵀ)⁻¹))ᵀ =
      Matrix.kronecker A⁻¹ A⁻¹ := by
    rw [fsr_kron_tr, fsr_kron_tr, fsr_kron_mul, hBt, h3]
  have hlast : Matrix.kronecker A⁻¹ A⁻¹ * Matrix.kronecker A A = 1 := by
    rw [fsr_kron_mul, h4, fsr_kron_one]
  have hlast' : ∀ X : Matrix (Fin n × Fin n) (Fin n × Fin n) ℝ,
      Matrix.kronecker A⁻¹ A⁻¹ * (Matrix.kronecker A A * X) = X := by
    intro X
    rw [← Matrix.mul_assoc, hlast, Matrix.one_mul]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [hmid]
  rw [hend]
  rw [← Matrix.mul_assoc]
  rw [Matrix.trace_mul_cycle]
  simp only [Matrix.mul_assoc]
  rw [hlast']
  rw [Matrix.trace_mul_comm]

/-- **Frame independence of the curvature norm for a general change of frame.**  If `A` is
invertible and `Γ = A Aᵀ` is the Gram matrix of the frame `e'ᵢ = ∑ₐ Aᵢₐ eₐ`, then contracting
`rot A R` with `Γ⁻¹` gives the same value as the Frobenius norm of `R`. -/
theorem frobSq_rot {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) (R : Curv4 n) :
    N4 (A * Matrix.transpose A) (rot A R) = frobSq R := by
  rw [fsr_N4_trace]
  simp only [fsr_toM_rot]
  rw [fsr_trace_algebra A hA (fsr_toM R)]
  rw [fsr_trace_mul_transpose_toM R R]
  simp only [frobSq, pow_two]

end Work.Diff.GE
