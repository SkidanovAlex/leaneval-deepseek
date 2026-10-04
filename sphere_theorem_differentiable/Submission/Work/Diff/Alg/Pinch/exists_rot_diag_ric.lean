import Mathlib
import Submission.Work.Diff.Alg.Pinch.Defs
import Submission.Work.Diff.Alg.Pinch.ell_isAlgCurv
import Submission.Work.Diff.Alg.Pinch.exists_orthonormal_eigenbasis
import Submission.Work.Diff.Alg.Pinch.EFun_X_aux
import Submission.Work.Diff.Alg.Pinch.rot_toolkit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Diagonalising the Ricci tensor of an algebraic curvature tensor

The Ricci tensor `ric R i j = ∑ k, R k i k j` of an algebraic curvature tensor is symmetric
(pair symmetry of `R`), hence the spectral theorem for symmetric matrices produces an orthonormal
eigenbasis.  Reading that eigenbasis as the transpose of an orthogonal matrix `A` makes the Ricci
tensor of the rotated curvature tensor `rot A R` diagonal: for `A ∈ O(n)` the Ricci tensor
transforms as a `(0,2)`-tensor, `ric (rot A R) i j = ∑ b d, A i b A j d ric R b d`
(`Work.Diff.Alg.Pinch.rt_ric_rot`), so `A = fᵀ` gives the conjugation `fᵀ · ric R · f`, which is
diagonal on the eigenbasis of `ric R`.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

/-- The Ricci tensor of an algebraic curvature tensor is symmetric: this is exactly the
pair-symmetry component `R k l i j = R i j k l` of `IsAlgCurv`. -/
theorem ric_symm_of_isAlgCurv {n : ℕ} {R : Curv4 n} (hR : IsAlgCurv R) :
    ∀ i j : Fin n, ric R i j = ric R j i := by
  intro i j
  simp only [ric]
  apply Finset.sum_congr rfl
  intro k _
  exact (hR.2.1 k i k j).symm

/-- **Diagonalisation of the Ricci tensor.**  For every algebraic curvature tensor `R` on `ℝⁿ`
there is an orthogonal change of frame `A` such that the Ricci tensor of `rot A R` is diagonal. -/
theorem exists_rot_diag_ric (n : ℕ) (R : Submission.Diff.Alg.Curv4 n)
    (hR : Submission.Diff.Alg.IsAlgCurv R) :
    ∃ A : Matrix (Fin n) (Fin n) ℝ, A ∈ Matrix.orthogonalGroup (Fin n) ℝ ∧
      (∀ i j : Fin n, i ≠ j → Work.Diff.Alg.Pinch.ric (Submission.Diff.Alg.rot A R) i j = 0) := by
  classical
  -- An orthonormal eigenbasis of the symmetric matrix `ric R`.
  obtain ⟨f, mu, horth, heig⟩ :=
    exists_orthonormal_eigenbasis n (fun i j => ric R i j) (ric_symm_of_isAlgCurv hR)
  -- The orthogonal matrix `A = fᵀ` whose *rows* are the eigenvectors `f · i`.
  have hA : Matrix.of (fun i j : Fin n => f j i) ∈ Matrix.orthogonalGroup (Fin n) ℝ := by
    rw [Matrix.mem_orthogonalGroup_iff]
    ext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Matrix.of_apply]
    exact horth i j
  refine ⟨Matrix.of (fun i j : Fin n => f j i), hA, ?_⟩
  intro i j hij
  -- The rotated Ricci tensor is the conjugation `fᵀ · ric R · f`, hence diagonal.
  have hkey : ric (rot (Matrix.of (fun i j : Fin n => f j i)) R) i j
      = mu j * (if i = j then 1 else 0) := by
    rw [rt_ric_rot (Matrix.of (fun i j : Fin n => f j i)) hA R i j]
    simp only [Matrix.of_apply]
    calc ∑ b, ∑ d, f b i * f d j * ric R b d
        = ∑ b, f b i * (∑ d, ric R b d * f d j) := by
          apply Finset.sum_congr rfl; intro b _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro d _
          ring
      _ = ∑ b, f b i * (mu j * f b j) := by
          apply Finset.sum_congr rfl; intro b _
          rw [heig j b]
      _ = ∑ b, mu j * (f b i * f b j) := by
          apply Finset.sum_congr rfl; intro b _
          ring
      _ = mu j * ∑ b, f b i * f b j := by
          rw [Finset.mul_sum]
      _ = mu j * (if i = j then 1 else 0) := by rw [horth]
  rw [hkey]
  simp [hij]

end Work.Diff.Alg.Pinch
