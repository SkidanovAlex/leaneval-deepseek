import Mathlib
import Submission.Diff.Grad

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Orthogonal invariance of the Frobenius norm of a curvature tensor

`Work.Diff.GE.rot_frobsq`: for an orthogonal matrix `A` and a 4-index array `R` (curvature
components in an orthonormal frame), the Frobenius sum of squares `frobSq` is invariant under the
change of frame `rot A R i j k l = ∑ Aᵢₐ Aⱼᵦ Aₖ_c Aₗ_d R a b c d`.

This is the statement that `A ↦ rot A` is an orthogonal (norm preserving) action on the space of
algebraic curvature tensors: `rot A` is the fourfold Kronecker matrix `A ⊗ A ⊗ A ⊗ A` acting on
the flattened tensor, and that matrix is again orthogonal.

## Proof outline

* `Idx n = (Fin n × Fin n) × (Fin n × Fin n)` indexes the flattened tensor
  `vecOf R x = R x.1.1 x.1.2 x.2.1 x.2.2`.
* `sum_sq_mulVec`: for a matrix `B` with orthonormal columns and a vector `v`,
  `∑ i, (B *ᵥ v) i ^ 2 = ∑ i, v i ^ 2` (an orthogonal matrix preserves sums of squares).
* `frobSq_eq`: `frobSq R = ∑ x : Idx n, (vecOf R x) ^ 2` (regrouping the four sums).
* `rot_eq_mulVec`: `vecOf (rot A R) = kmat A *ᵥ vecOf R`, where `kmat A` is the fourfold
  Kronecker product `(A ⊗ A) ⊗ (A ⊗ A)`.
* `kmat_orth`: `(kmat A)ᵀ * kmat A = 1` whenever `A ∈ Matrix.orthogonalGroup` (Kronecker product
  of orthogonal matrices), which supplies the hypothesis of `sum_sq_mulVec`.
-/

namespace Work.Diff.GE

open Finset
open Submission.Diff.Alg

variable {n : ℕ}

/-! ## The index type and the flattening of a `Curv4` -/

/-- The four-fold index set, paired as `((i,j),(k,l))`. -/
abbrev Idx (n : ℕ) := (Fin n × Fin n) × (Fin n × Fin n)

/-- Flattening of a 4-index array to a function on `Idx n`. -/
def vecOf (R : Curv4 n) : Idx n → ℝ := fun x => R x.1.1 x.1.2 x.2.1 x.2.2

/-- The twofold Kronecker matrix on pairs of indices. -/
noncomputable def kA (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n × Fin n) (Fin n × Fin n) ℝ :=
  Matrix.kroneckerMap (fun a b : ℝ => a * b) A A

/-- The fourfold Kronecker matrix `A ⊗ A ⊗ A ⊗ A` acting on the flattened curvature tensor. -/
noncomputable def kmat (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Idx n) (Idx n) ℝ :=
  Matrix.kroneckerMap (fun a b : ℝ => a * b) (kA A) (kA A)

/-! ## Orthogonal matrices preserve sums of squares -/

/-- A matrix with orthonormal columns preserves the sum of squares of a vector. -/
theorem sum_sq_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : Matrix ι ι ℝ} (hcol : ∀ j j' : ι, ∑ i, B i j * B i j' = if j = j' then 1 else 0)
    (v : ι → ℝ) : ∑ i, (Matrix.mulVec B v) i ^ 2 = ∑ i, v i ^ 2 := by
  have expand : ∀ i, (∑ j, B i j * v j) ^ 2 = ∑ j, ∑ j', B i j * B i j' * v j * v j' := by
    intro i
    rw [sq, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro j _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j' _
    ring
  calc ∑ i, (Matrix.mulVec B v) i ^ 2
      = ∑ i, ∑ j, ∑ j', B i j * B i j' * v j * v j' := by
        apply Finset.sum_congr rfl; intro i _
        rw [Matrix.mulVec_apply_eq_sum]
        exact expand i
    _ = ∑ j, ∑ j', ∑ i, B i j * B i j' * v j * v j' := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
    _ = ∑ j, ∑ j', (∑ i, B i j * B i j') * v j * v j' := by
        apply Finset.sum_congr rfl; intro j _
        apply Finset.sum_congr rfl; intro j' _
        rw [Finset.sum_mul, Finset.sum_mul]
    _ = ∑ j, ∑ j', (if j = j' then 1 else 0) * v j * v j' := by
        apply Finset.sum_congr rfl; intro j _
        apply Finset.sum_congr rfl; intro j' _
        rw [hcol]
    _ = ∑ i, v i ^ 2 := by
        apply Finset.sum_congr rfl; intro j _
        rw [Finset.sum_eq_single j]
        · simp [sq]
        · intro b _ hb
          simp [show ¬ (j = b) from fun h => hb h.symm]
        · intro h; exact absurd (Finset.mem_univ j) h

/-! ## `frobSq` as a sum of squares over `Idx n` -/

/-- `frobSq` regrouped as a single sum over the four-fold index type. -/
theorem frobSq_eq (R : Curv4 n) : frobSq R = ∑ x : Idx n, (vecOf R x) ^ 2 := by
  have h1 : (∑ i, ∑ j, ∑ k, ∑ l, R i j k l ^ 2) = ∑ x : Idx n, (vecOf R x) ^ 2 := by
    rw [← Fintype.sum_prod_type' (f := fun (i j : Fin n) => ∑ k, ∑ l, R i j k l ^ 2)]
    trans ∑ p : Fin n × Fin n, ∑ q : Fin n × Fin n, R p.1 p.2 q.1 q.2 ^ 2
    · apply Finset.sum_congr rfl
      intro p _
      exact (Fintype.sum_prod_type' (f := fun (k l : Fin n) => R p.1 p.2 k l ^ 2)).symm
    · exact (Fintype.sum_prod_type (f := fun x : Idx n => (vecOf R x) ^ 2)).symm
  rw [frobSq]
  exact h1

/-! ## The rotation is the fourfold Kronecker matrix on the flattened tensor -/

/-- `rot A R` is the action of `A ⊗ A ⊗ A ⊗ A` on the flattened tensor. -/
theorem rot_eq_mulVec (A : Matrix (Fin n) (Fin n) ℝ) (R : Curv4 n) :
    vecOf (rot A R) = Matrix.mulVec (kmat A) (vecOf R) := by
  funext x
  show rot A R x.1.1 x.1.2 x.2.1 x.2.2 = _
  rw [rot]
  rw [Matrix.mulVec_apply_eq_sum]
  simp only [kmat, kA, Matrix.kroneckerMap_apply, vecOf]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  apply Finset.sum_congr rfl; intro c _
  apply Finset.sum_congr rfl; intro d _
  ring

/-! ## The fourfold Kronecker matrix is orthogonal -/

theorem kmat_orth {A : Matrix (Fin n) (Fin n) ℝ} (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ) :
    Matrix.transpose (kmat A) * kmat A = 1 := by
  have hAA : Matrix.transpose A * A = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (n := Fin n) (R := ℝ)).mp hA
  have hK : Matrix.transpose (kA A) * kA A = 1 := by
    simp only [kA]
    rw [← Matrix.kroneckerMap_transpose (f := fun a b : ℝ => a * b)]
    rw [← Matrix.mul_kronecker_mul, hAA]
    exact Matrix.one_kronecker_one
  simp only [kmat]
  rw [← Matrix.kroneckerMap_transpose (f := fun a b : ℝ => a * b)]
  rw [← Matrix.mul_kronecker_mul, hK]
  exact Matrix.one_kronecker_one

/-! ## The target -/

theorem rot_frobsq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ) (R : Submission.Diff.Alg.Curv4 n) :
    Submission.Diff.Alg.frobSq (Submission.Diff.Alg.rot A R) = Submission.Diff.Alg.frobSq R := by
  have hcol : ∀ j j' : Idx n, ∑ i, kmat A i j * kmat A i j' = if j = j' then 1 else 0 := by
    intro j j'
    have h := congrFun (congrFun (kmat_orth hA) j) j'
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using h
  calc frobSq (rot A R) = ∑ x : Idx n, (vecOf (rot A R) x) ^ 2 := frobSq_eq _
    _ = ∑ x : Idx n, (Matrix.mulVec (kmat A) (vecOf R)) x ^ 2 := by rw [rot_eq_mulVec]
    _ = ∑ x : Idx n, (vecOf R x) ^ 2 := sum_sq_mulVec hcol (vecOf R)
    _ = frobSq R := (frobSq_eq R).symm

end Work.Diff.GE
