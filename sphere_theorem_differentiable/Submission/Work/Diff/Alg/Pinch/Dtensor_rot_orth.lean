import Mathlib
import Submission.Work.Diff.Alg.Pinch.Defs
import Submission.Work.Diff.Alg.Pinch.DtensorDefs
import Submission.Work.Diff.Alg.Pinch.Linv
import Submission.Work.Diff.Alg.Pinch.Rot2Defs
import Submission.Work.Diff.Alg.Pinch.rot_knProd_id2
import Submission.Work.Diff.Alg.Pinch.EFun_X_aux
import Submission.Work.Diff.Alg.Pinch.ric_rot

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `O(n)`-equivariance of the Böhm–Wilking difference tensor `D_{a,b}`

The Böhm–Wilking difference tensor `D_{a,b}` (`Work.Diff.Alg.Pinch.Dtensor`) is built out of the
Ricci tensor, the traceless Ricci tensor, its square and the Kulkarni–Nomizu product with the
identity.  All of these are `O(n)`-equivariant, so

`rot A (D_{a,b}(R)) = D_{a,b}(rot A R)`

for every orthogonal change of frame `A`.  This is the equivariance used when the Böhm–Wilking
identity is applied in an arbitrary orthonormal frame.

The proof is term-by-term: `rot` is linear, `rot A (knProd X Y) = knProd (rot2 A X) (rot2 A Y)`
(`dorth_rot_knProd`), the `(0,2)`-parts transform by `rot2` (`ric_rot`, `dorth_ric0_rot`,
`dorth_ric0sq_rot`), `rot2 A (id2 n) = id2 n` for orthogonal `A` (`dorth_rot2_id2_orth`), and the
scalar invariant `ric0Frob2` is unchanged (`dorth_ric0Frob2_rot`).

The `(0,2)` transport facts are proved through the matrix identity
`Matrix.of (rot2 A M) = A * Matrix.of M * Aᵀ` (`dorth_rot2_mat`): then `ric0sq` is matrix
multiplication and `ric0Frob2` is `trace (M Mᵀ)`, both invariant under an orthogonal conjugation.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg
open scoped Matrix

variable {n : ℕ}

/-! ## The `(0,2)`-tensor action on the identity tensor -/

/-- `rot2 A` sends the Kronecker delta `id2 n` to the matrix `A * Aᵀ`. -/
lemma dorth_rot2_id2 (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) :
    rot2 A (id2 n) = A * Aᵀ := by
  ext i j
  simp only [rot2, id2, Matrix.mul_apply, Matrix.transpose_apply]
  apply Finset.sum_congr rfl; intro a _
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    have h : ¬ (a = b) := fun hh => hb hh.symm
    simp [h]
  · intro h; exact absurd (Finset.mem_univ a) h

/-- For an orthogonal matrix `A`, the `(0,2)`-action fixes the identity tensor `id2 n`. -/
lemma dorth_rot2_id2_orth (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ) : rot2 A (id2 n) = id2 n := by
  rw [dorth_rot2_id2, (Matrix.mem_orthogonalGroup_iff (n := Fin n) (R := ℝ)).mp hA]
  ext i j
  simp [id2, Matrix.one_apply]

/-! ## `rot2` as a matrix conjugation -/

/-- The `(0,2)`-action is the matrix conjugation `M ↦ A M Aᵀ`. -/
lemma dorth_rot2_mat (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (M : Fin n → Fin n → ℝ) :
    Matrix.of (rot2 A M) = A * Matrix.of M * Aᵀ := by
  ext i j
  simp only [rot2, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro b _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl; intro a _
  ring

/-- For an orthogonal change of frame, the `(0,2)`-action is multiplicative for the matrix
product of `(0,2)`-tensors. -/
lemma dorth_rot2_mul (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ) (M N : Fin n → Fin n → ℝ) :
    rot2 A (fun i j => ∑ k, M i k * N k j)
      = fun i j => ∑ k, rot2 A M i k * rot2 A N k j := by
  have hAt : Aᵀ * A = 1 := (Matrix.mem_orthogonalGroup_iff' (n := Fin n) (R := ℝ)).mp hA
  have key : A * (Matrix.of M * Matrix.of N) * Aᵀ
      = (A * Matrix.of M * Aᵀ) * (A * Matrix.of N * Aᵀ) := by
    have h1 : Aᵀ * (A * (Matrix.of N * Aᵀ)) = Matrix.of N * Aᵀ := by
      rw [← Matrix.mul_assoc, hAt, Matrix.one_mul]
    simp only [Matrix.mul_assoc]
    rw [h1]
  apply (Matrix.of : (Fin n → Fin n → ℝ) ≃ Matrix (Fin n) (Fin n) ℝ).injective
  rw [dorth_rot2_mat n A (fun i j => ∑ k, M i k * N k j),
    show Matrix.of (fun i j => ∑ k, M i k * N k j) = Matrix.of M * Matrix.of N from rfl,
    show Matrix.of (fun i j => ∑ k, rot2 A M i k * rot2 A N k j)
      = Matrix.of (rot2 A M) * Matrix.of (rot2 A N) from rfl,
    dorth_rot2_mat n A M, dorth_rot2_mat n A N]
  exact key

/-! ## Naturality of the Kulkarni–Nomizu product -/

/-- The Kulkarni–Nomizu product is natural under the frame action: for *any* matrix `A`,
`rot A (knProd X Y) = knProd (rot2 A X) (rot2 A Y)`.  Orthogonality is not needed. -/
lemma dorth_rot_knProd (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (X Y : Fin n → Fin n → ℝ) :
    rot A (knProd X Y) = knProd (rot2 A X) (rot2 A Y) := by
  funext i j k l
  have hsplit : ∀ a b c d : Fin n,
      A i a * A j b * A k c * A l d
          * (X a c * Y b d - X a d * Y b c - X b c * Y a d + X b d * Y a c)
        = (A i a * A k c * X a c) * (A j b * A l d * Y b d)
          - (A i a * A l d * X a d) * (A j b * A k c * Y b c)
          - (A i a * A l d * Y a d) * (A j b * A k c * X b c)
          + (A i a * A k c * Y a c) * (A j b * A l d * X b d) := by
    intro a b c d; ring
  simp only [rot, knProd, hsplit, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [sum4_factor (fun a c => A i a * A k c * X a c) (fun b d => A j b * A l d * Y b d),
    sum4_factor' (fun a d => A i a * A l d * X a d) (fun b c => A j b * A k c * Y b c),
    sum4_factor' (fun a d => A i a * A l d * Y a d) (fun b c => A j b * A k c * X b c),
    sum4_factor (fun a c => A i a * A k c * Y a c) (fun b d => A j b * A l d * X b d)]
  simp only [rot2]
  ring

/-! ## The traceless Ricci tensor -/

/-- Under an orthogonal change of frame the traceless Ricci tensor transforms by `rot2`. -/
lemma dorth_ric0_rot (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ) (R : Curv4 n) :
    ric0 (rot A R) = rot2 A (ric0 R) := by
  have hid2 : rot2 A (id2 n) = id2 n := dorth_rot2_id2_orth n A hA
  calc ric0 (rot A R)
      = ric (rot A R) - (scalAlg (rot A R) / (n : ℝ)) • id2 n := by
        funext i j
        simp only [ric0, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    _ = rot2 A (ric R) - (scalAlg R / (n : ℝ)) • id2 n := by
        rw [ric_rot n A hA R, rt_scalAlg_rot A hA R]
    _ = rot2 A (ric R) - (scalAlg R / (n : ℝ)) • rot2 A (id2 n) := by
        rw [hid2]
    _ = rot2 A (ric R) - rot2 A ((scalAlg R / (n : ℝ)) • id2 n) := by
        rw [rot2_smul]
    _ = rot2 A (ric R - (scalAlg R / (n : ℝ)) • id2 n) := by
        rw [rot2_sub]
    _ = rot2 A (ric0 R) := by congr 1

/-! ## The square of the traceless Ricci tensor -/

/-- Under an orthogonal change of frame the square of the traceless Ricci tensor transforms by
`rot2`. -/
lemma dorth_ric0sq_rot (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ) (R : Curv4 n) :
    ric0sq (rot A R) = rot2 A (ric0sq R) := by
  have h1 : ric0 (rot A R) = rot2 A (ric0 R) := dorth_ric0_rot n A hA R
  have h2 := dorth_rot2_mul n A hA (ric0 R) (ric0 R)
  rw [show ric0sq (rot A R)
      = fun i j => ∑ k, ric0 (rot A R) i k * ric0 (rot A R) k j from rfl, h1, ← h2]
  rfl

/-! ## The Frobenius norm of the traceless Ricci tensor -/

/-- `∑ i j, B i j * B i j` is the trace of `B * Bᵀ`. -/
lemma dorth_sum_mul_self_eq_trace (n : ℕ) (B : Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, B i j * B i j) = Matrix.trace (Matrix.of B * (Matrix.of B)ᵀ) := by
  rw [Matrix.trace]
  apply Finset.sum_congr rfl; intro i _
  rw [Matrix.diag_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl; intro j _
  rw [Matrix.transpose_apply, Matrix.of_apply]

/-- Under an orthogonal change of frame the Frobenius norm of the traceless Ricci tensor is
unchanged. -/
lemma dorth_ric0Frob2_rot (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ) (R : Curv4 n) :
    ric0Frob2 (rot A R) = ric0Frob2 R := by
  have hAt : Aᵀ * A = 1 := (Matrix.mem_orthogonalGroup_iff' (n := Fin n) (R := ℝ)).mp hA
  have hB : Matrix.of (ric0 (rot A R)) = A * Matrix.of (ric0 R) * Aᵀ := by
    rw [dorth_ric0_rot n A hA R]
    exact dorth_rot2_mat n A (ric0 R)
  have hsq : (A * Matrix.of (ric0 R) * Aᵀ) * (A * Matrix.of (ric0 R) * Aᵀ)ᵀ
      = A * (Matrix.of (ric0 R) * (Matrix.of (ric0 R))ᵀ) * Aᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
    have h1 : Aᵀ * (A * ((Matrix.of (ric0 R))ᵀ * Aᵀ)) = (Matrix.of (ric0 R))ᵀ * Aᵀ := by
      rw [← Matrix.mul_assoc, hAt, Matrix.one_mul]
    simp only [Matrix.mul_assoc]
    rw [h1]
  have htr : Matrix.trace (A * (Matrix.of (ric0 R) * (Matrix.of (ric0 R))ᵀ) * Aᵀ)
      = Matrix.trace (Matrix.of (ric0 R) * (Matrix.of (ric0 R))ᵀ) := by
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
    rw [Matrix.mul_assoc, hAt, Matrix.mul_one]
  have h1 : (∑ i, ∑ j, ric0 (rot A R) i j * ric0 (rot A R) i j)
      = Matrix.trace (Matrix.of (ric0 (rot A R)) * (Matrix.of (ric0 (rot A R)))ᵀ) :=
    dorth_sum_mul_self_eq_trace n (ric0 (rot A R))
  have h2 : (∑ i, ∑ j, ric0 R i j * ric0 R i j)
      = Matrix.trace (Matrix.of (ric0 R) * (Matrix.of (ric0 R))ᵀ) :=
    dorth_sum_mul_self_eq_trace n (ric0 R)
  simp only [ric0Frob2]
  rw [h1, h2, hB, hsq, htr]

/-! ## The equivariance of the difference tensor -/

theorem Dtensor_rot_orth (n : ℕ) (b : ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ) (R : Submission.Diff.Alg.Curv4 n) :
    Submission.Diff.Alg.rot A (Work.Diff.Alg.Pinch.Dtensor n b R)
      = Work.Diff.Alg.Pinch.Dtensor n b (Submission.Diff.Alg.rot A R) := by
  simp only [Dtensor, rot_add_lin, rot_smul_lin, dorth_rot_knProd,
    ← dorth_ric0_rot n A hA R, ← ric_rot n A hA R, ← dorth_ric0sq_rot n A hA R,
    dorth_rot2_id2_orth n A hA, dorth_ric0Frob2_rot n A hA R]

end Work.Diff.Alg.Pinch
