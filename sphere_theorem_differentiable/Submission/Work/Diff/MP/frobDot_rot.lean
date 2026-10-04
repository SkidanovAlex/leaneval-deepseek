import Mathlib
import Submission.Work.Diff.MP.Basic
import Submission.Work.Diff.GE.rot_frobsq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Orthogonal invariance of the Frobenius inner product on curvature arrays

`Work.Diff.MP.frobDot_rot`: for `A ∈ O(n)` and two curvature arrays `X`, `Y`,
`frobDot (rot A X) (rot A Y) = frobDot X Y`.  This is the statement that the Frobenius inner
product on `Curv4 n` is invariant under an orthogonal change of frame.

The proof flattens a `Curv4 n` into a vector indexed by `Idx n = (Fin n × Fin n) × (Fin n × Fin n)`
(`Work.Diff.GE.vecOf`), on which `rot A` acts as the fourfold Kronecker matrix `kmat A`
(`Work.Diff.GE.rot_eq_mulVec`), whose columns are orthonormal (`Work.Diff.GE.kmat_orth`).  A matrix
with orthonormal columns preserves the standard inner product of vectors (`sum_mulVec_mulVec`), and
`frobDot` is that inner product on the flattened tensors (`frobDot_eq_sum_vecOf`).
-/

namespace Work.Diff.MP

open Submission.Diff.Alg
open Work.Diff.GE (Idx vecOf kmat rot_eq_mulVec kmat_orth)

variable {n : ℕ}

/-- `frobDot` regrouped as a single sum over the fourfold index type. -/
theorem frobDot_eq_sum_vecOf (X Y : Curv4 n) :
    frobDot X Y = ∑ x : Idx n, vecOf X x * vecOf Y x := by
  have h1 : (∑ i, ∑ j, ∑ k, ∑ l, X i j k l * Y i j k l)
      = ∑ x : Idx n, vecOf X x * vecOf Y x := by
    rw [← Fintype.sum_prod_type'
      (f := fun (i j : Fin n) => ∑ k, ∑ l, X i j k l * Y i j k l)]
    trans ∑ p : Fin n × Fin n, ∑ q : Fin n × Fin n,
        X p.1 p.2 q.1 q.2 * Y p.1 p.2 q.1 q.2
    · refine Finset.sum_congr rfl fun p _ => ?_
      exact (Fintype.sum_prod_type'
        (f := fun (k l : Fin n) => X p.1 p.2 k l * Y p.1 p.2 k l)).symm
    · exact (Fintype.sum_prod_type (f := fun x : Idx n => vecOf X x * vecOf Y x)).symm
  rw [frobDot]
  exact h1

/-- A matrix whose columns are orthonormal preserves the standard inner product of vectors. -/
theorem sum_mulVec_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : Matrix ι ι ℝ} (hcol : ∀ j j' : ι, ∑ i, B i j * B i j' = if j = j' then 1 else 0)
    (v w : ι → ℝ) :
    ∑ i, Matrix.mulVec B v i * Matrix.mulVec B w i = ∑ i, v i * w i := by
  have expand : ∀ i, Matrix.mulVec B v i * Matrix.mulVec B w i
      = ∑ j, ∑ j', B i j * B i j' * v j * w j' := by
    intro i
    rw [Matrix.mulVec_apply_eq_sum, Matrix.mulVec_apply_eq_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j' _ => ?_
    ring
  calc ∑ i, Matrix.mulVec B v i * Matrix.mulVec B w i
      = ∑ i, ∑ j, ∑ j', B i j * B i j' * v j * w j' :=
        Finset.sum_congr rfl fun i _ => expand i
    _ = ∑ j, ∑ j', ∑ i, B i j * B i j' * v j * w j' := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
    _ = ∑ j, ∑ j', (∑ i, B i j * B i j') * v j * w j' := by
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
        rw [Finset.sum_mul, Finset.sum_mul]
    _ = ∑ j, ∑ j', (if j = j' then 1 else 0) * v j * w j' := by
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
        rw [hcol]
    _ = ∑ j, v j * w j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_eq_single j]
        · simp
        · intro b _ hb
          simp [show ¬ (j = b) from fun h => hb h.symm]
        · intro h; exact absurd (Finset.mem_univ j) h

/-- The columns of the fourfold Kronecker matrix of an orthogonal matrix are orthonormal. -/
theorem kmat_col_orth (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ) (j j' : Idx n) :
    ∑ i, kmat A i j * kmat A i j' = if j = j' then 1 else 0 := by
  have h := congrFun (congrFun (kmat_orth hA) j) j'
  simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using h

theorem frobDot_rot (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ) (X Y : Curv4 n) :
    frobDot (rot A X) (rot A Y) = frobDot X Y := by
  calc frobDot (rot A X) (rot A Y)
      = ∑ x : Idx n, vecOf (rot A X) x * vecOf (rot A Y) x :=
        frobDot_eq_sum_vecOf (rot A X) (rot A Y)
    _ = ∑ x : Idx n, Matrix.mulVec (kmat A) (vecOf X) x
          * Matrix.mulVec (kmat A) (vecOf Y) x := by
        rw [rot_eq_mulVec, rot_eq_mulVec]
    _ = ∑ x : Idx n, vecOf X x * vecOf Y x :=
        sum_mulVec_mulVec (kmat_col_orth A hA) (vecOf X) (vecOf Y)
    _ = frobDot X Y := (frobDot_eq_sum_vecOf X Y).symm

end Work.Diff.MP
