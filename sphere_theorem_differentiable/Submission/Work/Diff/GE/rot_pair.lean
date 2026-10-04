import Mathlib
import Submission.Work.Diff.GE.Frame
import Submission.Work.Diff.GE.rot_frobsq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Orthogonal invariance of the Frobenius *pairing* of two curvature tensors

`Work.Diff.GE.rot_frobsq` proves that an orthogonal change of frame `A` preserves the Frobenius
quadratic form `frobSq R = ∑ Rᵢⱼₖₗ²` of a curvature array `R`.  Here we prove the corresponding
statement for the *bilinear* form, i.e. the polarization of that quadratic form:

`∑ᵢⱼₖₗ (rot A R)ᵢⱼₖₗ (rot A S)ᵢⱼₖₗ = ∑ᵢⱼₖₗ Rᵢⱼₖₗ Sᵢⱼₖₗ` for every `A ∈ O(n)`.

Route (mirroring `rot_frobsq`): flatten `Curv4 n` to functions on the index type
`Idx n = (Fin n × Fin n) × (Fin n × Fin n)`.  Then

* `bil_eq`: the fourfold sum `∑ᵢⱼₖₗ Rᵢⱼₖₗ Sᵢⱼₖₗ` is the single sum `∑ₓ vecOf R x * vecOf S x`;
* `sum_mul_mulVec`: the bilinear companion of `sum_sq_mulVec` -- a matrix with orthonormal columns
  preserves the pairing `∑ᵢ vᵢ wᵢ`;
* `rot_eq_mulVec` / `kmat_orth` (imported): `rot A` is `A ⊗ A ⊗ A ⊗ A` on the flattened tensor,
  whose columns are orthonormal when `A ∈ O(n)`.
-/

namespace Work.Diff.GE

open Finset
open Submission.Diff.Alg

variable {n : ℕ}

/-! ## The Frobenius pairing -/

/-- The Frobenius bilinear pairing of two 4-index arrays, `⟨R, S⟩ = ∑ᵢⱼₖₗ Rᵢⱼₖₗ Sᵢⱼₖₗ`. -/
noncomputable def bil (R S : Curv4 n) : ℝ :=
  ∑ i, ∑ j, ∑ k, ∑ l, R i j k l * S i j k l

/-- `bil` regrouped as a single sum over the four-fold index type. -/
theorem bil_eq (R S : Curv4 n) : bil R S = ∑ x : Idx n, vecOf R x * vecOf S x := by
  have h1 : (∑ i, ∑ j, ∑ k, ∑ l, R i j k l * S i j k l)
      = ∑ x : Idx n, vecOf R x * vecOf S x := by
    rw [← Fintype.sum_prod_type'
      (f := fun (i j : Fin n) => ∑ k, ∑ l, R i j k l * S i j k l)]
    trans ∑ p : Fin n × Fin n, ∑ q : Fin n × Fin n,
        R p.1 p.2 q.1 q.2 * S p.1 p.2 q.1 q.2
    · apply Finset.sum_congr rfl
      intro p _
      exact (Fintype.sum_prod_type'
        (f := fun (k l : Fin n) => R p.1 p.2 k l * S p.1 p.2 k l)).symm
    · exact (Fintype.sum_prod_type (f := fun x : Idx n => vecOf R x * vecOf S x)).symm
  rw [bil]
  exact h1

/-! ## Orthogonal matrices preserve the pairing -/

/-- A matrix with orthonormal columns preserves the bilinear pairing of two vectors
(the bilinear companion of `sum_sq_mulVec`). -/
theorem sum_mul_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : Matrix ι ι ℝ} (hcol : ∀ j j' : ι, ∑ i, B i j * B i j' = if j = j' then 1 else 0)
    (v w : ι → ℝ) :
    ∑ i, (Matrix.mulVec B v) i * (Matrix.mulVec B w) i = ∑ i, v i * w i := by
  have expand : ∀ i, (∑ j, B i j * v j) * (∑ j, B i j * w j)
      = ∑ j, ∑ j', B i j * B i j' * v j * w j' := by
    intro i
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro j _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j' _
    ring
  calc ∑ i, (Matrix.mulVec B v) i * (Matrix.mulVec B w) i
      = ∑ i, ∑ j, ∑ j', B i j * B i j' * v j * w j' := by
        apply Finset.sum_congr rfl; intro i _
        rw [Matrix.mulVec_apply_eq_sum, Matrix.mulVec_apply_eq_sum]
        exact expand i
    _ = ∑ j, ∑ j', ∑ i, B i j * B i j' * v j * w j' := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
    _ = ∑ j, ∑ j', (∑ i, B i j * B i j') * v j * w j' := by
        apply Finset.sum_congr rfl; intro j _
        apply Finset.sum_congr rfl; intro j' _
        rw [Finset.sum_mul, Finset.sum_mul]
    _ = ∑ j, ∑ j', (if j = j' then 1 else 0) * v j * w j' := by
        apply Finset.sum_congr rfl; intro j _
        apply Finset.sum_congr rfl; intro j' _
        rw [hcol]
    _ = ∑ i, v i * w i := by
        apply Finset.sum_congr rfl; intro j _
        rw [Finset.sum_eq_single j]
        · simp
        · intro b _ hb
          simp [show ¬ (j = b) from fun h => hb h.symm]
        · intro h; exact absurd (Finset.mem_univ j) h

/-! ## The target -/

theorem rot_pair {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ) (R S : Submission.Diff.Alg.Curv4 n) :
    (∑ i, ∑ j, ∑ k, ∑ l, Submission.Diff.Alg.rot A R i j k l * Submission.Diff.Alg.rot A S i j k l)
      = ∑ i, ∑ j, ∑ k, ∑ l, R i j k l * S i j k l := by
  have hcol : ∀ j j' : Idx n, ∑ i, kmat A i j * kmat A i j' = if j = j' then 1 else 0 := by
    intro j j'
    have h := congrFun (congrFun (kmat_orth hA) j) j'
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using h
  show bil (rot A R) (rot A S) = bil R S
  calc bil (rot A R) (rot A S)
      = ∑ x : Idx n, vecOf (rot A R) x * vecOf (rot A S) x := bil_eq _ _
    _ = ∑ x : Idx n, (Matrix.mulVec (kmat A) (vecOf R)) x
            * (Matrix.mulVec (kmat A) (vecOf S)) x := by rw [rot_eq_mulVec A R, rot_eq_mulVec A S]
    _ = ∑ x : Idx n, vecOf R x * vecOf S x := sum_mul_mulVec hcol _ _
    _ = bil R S := (bil_eq R S).symm

end Work.Diff.GE
