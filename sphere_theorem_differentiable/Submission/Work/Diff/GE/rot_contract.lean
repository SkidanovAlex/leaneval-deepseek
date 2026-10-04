import Mathlib
import Submission.Work.Diff.Alg.q2p_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The core contraction identity for `rot` (`Work.Diff.GE.rot_contract`)

`rot A R i j k l = ∑ a b c d, A i a * A j b * A k c * A l d * R a b c d` is the fourfold
Kronecker action `A ⊗ A ⊗ A ⊗ A` of an orthogonal change of frame `A` on a curvature array.
Here we prove that contracting two `rot`-transformed tensors over their *last two* indices is the
same as `rot`-transforming the contraction: for `A` orthogonal,

`∑ p q, rot A φ i j p q * rot A ψ k l p q
   = ∑ a b c d, A i a * A j b * A k c * A l d * (∑ p q, φ a b p q * ψ c d p q)`.

No algebraic hypothesis on `φ`, `ψ` is used — only the column orthogonality `Aᵀ A = 1`.

## Route

Regroup each `Curv4` as a matrix on the pair index `(i,j)`, `curvMat R (i,j) (k,l) = R i j k l`, and
let `kronAA A = A ⊗ A` be the twofold Kronecker matrix.  Then

* `curvMat_rot`: `curvMat (rot A R) = kronAA A * curvMat R * (kronAA A)ᵀ` (the `rot` action is the
  matrix conjugation by `A ⊗ A`);
* `rotc_product_entry`: the sum `∑ p q, X (i,j) (p,q) * Y (k,l) (p,q)` is the `(i,j),(k,l)` entry of
  `X * Yᵀ`;
* `rotc_sandwich_mul`: for `Kᵀ K = 1`, `(K P Kᵀ) * (K Q Kᵀ)ᵀ = K P Qᵀ Kᵀ`; with `K = kronAA A`
  (`kronAA_orth`) this contracts `(A ⊗ A)ᵀ (A ⊗ A) = 1`;
* `rotc_entry_four`: the entry of `K M Kᵀ` expands into the four sums `∑ a b c d`.
-/

namespace Work.Diff.GE

open Finset Submission.Diff.Alg
open scoped Matrix

variable {n : ℕ}

/-- A `Curv4` array regrouped as a matrix on the pair index `(i, j)`. -/
noncomputable def curvMat (R : Curv4 n) : Matrix (Fin n × Fin n) (Fin n × Fin n) ℝ :=
  fun x y => R x.1 x.2 y.1 y.2

/-- The twofold Kronecker matrix `A ⊗ A` acting on pairs of indices. -/
noncomputable def kronAA (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n × Fin n) (Fin n × Fin n) ℝ :=
  Matrix.kroneckerMap (fun a b : ℝ => a * b) A A

/-- `A ⊗ A` is orthogonal when `A` is. -/
lemma kronAA_orth (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ) : (kronAA A)ᵀ * kronAA A = 1 := by
  have hAA : Aᵀ * A = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).mp hA
  simp only [kronAA]
  rw [← Matrix.kroneckerMap_transpose]
  rw [← Matrix.mul_kronecker_mul, hAA]
  exact Matrix.one_kronecker_one

/-- Contracting the two pair-index legs of matrices: `∑ p q, X (i,j) (p,q) * Y (k,l) (p,q)` is the
`(i,j), (k,l)` entry of `X * Yᵀ`. -/
lemma rotc_product_entry (X Y : Matrix (Fin n × Fin n) (Fin n × Fin n) ℝ) (i j k l : Fin n) :
    (∑ p, ∑ q, X (i,j) (p,q) * Y (k,l) (p,q)) = (X * Yᵀ) (i,j) (k,l) := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [Matrix.transpose_apply]

/-- The `(a,b),(c,d)` entry of `curvMat φ * (curvMat ψ)ᵀ` is the last-two-index contraction of `φ`
and `ψ`. -/
lemma rotc_PQ_entry (φ ψ : Curv4 n) (a b c d : Fin n) :
    (curvMat φ * (curvMat ψ)ᵀ) (a,b) (c,d) = ∑ p, ∑ q, φ a b p q * ψ c d p q := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [Matrix.transpose_apply, curvMat]

/-- Entrywise expansion of the conjugation by `A ⊗ A`. -/
lemma rotc_entry_four (A : Matrix (Fin n) (Fin n) ℝ)
    (M : Matrix (Fin n × Fin n) (Fin n × Fin n) ℝ) (i j k l : Fin n) :
    (kronAA A * M * (kronAA A)ᵀ) (i,j) (k,l)
      = ∑ a, ∑ b, ∑ c, ∑ d, A i a * A j b * M (a,b) (c,d) * A k c * A l d := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, kronAA, Matrix.kroneckerMap_apply]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  apply Finset.sum_congr rfl; intro c _
  apply Finset.sum_congr rfl; intro d _
  ring

/-- `rot A` is the matrix conjugation by `A ⊗ A` on the pair index. -/
lemma curvMat_rot (A : Matrix (Fin n) (Fin n) ℝ) (R : Curv4 n) :
    curvMat (rot A R) = kronAA A * curvMat R * (kronAA A)ᵀ := by
  ext x y
  obtain ⟨i,j⟩ := x
  obtain ⟨p,q⟩ := y
  rw [rotc_entry_four]
  simp only [curvMat, rot]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  apply Finset.sum_congr rfl; intro c _
  apply Finset.sum_congr rfl; intro d _
  ring

/-- Contraction of a sandwiched product against a `Kᵀ K = 1` matrix. -/
lemma rotc_sandwich_mul (K : Matrix (Fin n × Fin n) (Fin n × Fin n) ℝ) (hK : Kᵀ * K = 1)
    (P Q : Matrix (Fin n × Fin n) (Fin n × Fin n) ℝ) :
    (K * P * Kᵀ) * (K * Q * Kᵀ)ᵀ = K * P * Qᵀ * Kᵀ := by
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [Matrix.mul_assoc (K * P) Kᵀ (K * (Qᵀ * Kᵀ)), ← Matrix.mul_assoc Kᵀ K (Qᵀ * Kᵀ), hK,
    Matrix.one_mul]
  simp only [Matrix.mul_assoc]

/-- **Core contraction identity for `rot`.**  With `rot A φ i j k l = ∑ a b c d, A i a * A j b * A k c * A l d * φ a b c d`
(`Submission.Diff.Alg.rot`) and `A` orthogonal, the double contraction over the *last two* indices of two
`rot`-transformed 4-tensors is the `rot`-transform of the same contraction:
`∑ p q, rot A φ i j p q * rot A ψ k l p q = ∑ a b c d, A i a * A j b * A k c * A l d * (∑ p q, φ a b p q * ψ c d p q)`.

Ingredients (elementary; no algebraic hypotheses on `φ`, `ψ` are needed):
* `A ∈ Matrix.orthogonalGroup (Fin n) ℝ` gives `Aᵀ * A = 1` (`Matrix.mem_orthogonalGroup_iff'`), i.e.
  column orthogonality `∑ p, A p c * A p c' = if c = c' then 1 else 0`;
* expand both factors of the LHS with `Finset.sum_mul_sum` (a 10-fold sum), commute the `p`- and `q`-sums
  inwards (via `Finset.sum_comm`, or flatten with `Fintype.sum_prod_type` and swap the outer sums),
  contract using column orthogonality, then rename the remaining summation indices.
Sanity check: `φ = ψ = Submission.Diff.Alg.Iso n` (round sphere) gives `∑ p q, Iso i j p q * Iso k l p q` on the left.
The four-fold index reordering lemmas `sum_swap2`, `sum4_swap12/23/34`, `sum4_cycle`, `block_swap` already
proved in `Submission/Work/Diff/Alg/q2p_defs.lean` (namespace `Work.Diff.Alg.Q2P`) are useful here. -/
theorem rot_contract {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ) (φ ψ : Submission.Diff.Alg.Curv4 n)
    (i j k l : Fin n) :
    (∑ p, ∑ q, Submission.Diff.Alg.rot A φ i j p q * Submission.Diff.Alg.rot A ψ k l p q)
      = ∑ a, ∑ b, ∑ c, ∑ d, A i a * A j b * A k c * A l d *
          (∑ p, ∑ q, φ a b p q * ψ c d p q) := by
  have hkey : curvMat (rot A φ) * (curvMat (rot A ψ))ᵀ
      = kronAA A * curvMat φ * (curvMat ψ)ᵀ * (kronAA A)ᵀ := by
    rw [curvMat_rot A φ, curvMat_rot A ψ]
    exact rotc_sandwich_mul (kronAA A) (kronAA_orth A hA) (curvMat φ) (curvMat ψ)
  calc ∑ p, ∑ q, rot A φ i j p q * rot A ψ k l p q
      = (curvMat (rot A φ) * (curvMat (rot A ψ))ᵀ) (i,j) (k,l) := by
          rw [← rotc_product_entry (curvMat (rot A φ)) (curvMat (rot A ψ)) i j k l]
          apply Finset.sum_congr rfl; intro p _
          apply Finset.sum_congr rfl; intro q _
          rfl
    _ = (kronAA A * curvMat φ * (curvMat ψ)ᵀ * (kronAA A)ᵀ) (i,j) (k,l) := by rw [hkey]
    _ = (kronAA A * (curvMat φ * (curvMat ψ)ᵀ) * (kronAA A)ᵀ) (i,j) (k,l) := by
          simp only [Matrix.mul_assoc]
    _ = ∑ a, ∑ b, ∑ c, ∑ d,
          A i a * A j b * (curvMat φ * (curvMat ψ)ᵀ) (a,b) (c,d) * A k c * A l d :=
          rotc_entry_four A (curvMat φ * (curvMat ψ)ᵀ) i j k l
    _ = ∑ a, ∑ b, ∑ c, ∑ d, A i a * A j b * A k c * A l d *
          (∑ p, ∑ q, φ a b p q * ψ c d p q) := by
          apply Finset.sum_congr rfl; intro a _
          apply Finset.sum_congr rfl; intro b _
          apply Finset.sum_congr rfl; intro c _
          apply Finset.sum_congr rfl; intro d _
          rw [rotc_PQ_entry φ ψ a b c d]; ring

end Work.Diff.GE
