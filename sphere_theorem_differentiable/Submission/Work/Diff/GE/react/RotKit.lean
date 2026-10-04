import Mathlib
import Submission.Diff.Alg
import Submission.Work.Diff.Evol.Calc

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Index-computation kit for `rot`-equivariance of the curvature reaction algebra

The orthogonal group `O(n)` acts on curvature arrays by
`rot A R i j k l = ∑ a b c d, A i a * A j b * A k c * A l d * R a b c d`
(`Submission.Diff.Alg.rot`).  This file collects the elementary index computations that are needed
to prove that the reaction algebra of the Ricci flow,
`rmReact R = Q R - Xact R` (`Work.Diff.GE.rmReact`), commutes with this action.

Contents:

* `sum3_*`, `sum4_*`, `sum5_*` — reorderings of nested finite sums over `Fin n` (moving the
  innermost sum to the outside, swapping adjacent sums).  Everything here is bare `Finset.sum_comm`
  bookkeeping;
* `orthCols` — the columns of an orthogonal matrix are orthonormal, `∑ p, A p c * A p c' = δ_{c c'}`;
* `ricArr_rot` — the Ricci contraction `ricArr R i j = ∑ a, R a i a j` transforms as a `(0,2)`-tensor:
  `ricArr (rot A R) i p = ∑ e, A p e * (∑ c, A i c * ricArr R c e)`;
* `contract_Avec` — contracting an `A`-transformed vector against an `A`-transformed vector is
  `A`-invariant: `∑ p, (∑ e, A p e * u e) * (∑ a, A p a * v a) = ∑ e, u e * v e`;
* `rot_apply_factor`, `rot_apply_factor2/3/4` — the definition of `rot` with the other three sums
  factored out of the `A i a` (resp. `A j b`, `A k c`, `A l d`) factor, so that `rot A R i j k l`
  can be fed to `contract_Avec` in whichever slot carries the contraction index;
* `rot_sub` — `rot A` is additive in the tensor, `rot A (S - T) = rot A S - rot A T`.
-/

namespace Work.Diff.GE.react

open Finset Matrix
open Submission.Diff.Alg
open Work.Diff.Evol

variable {n : ℕ}

/-! ## Reordering nested sums over `Fin n` -/

theorem sum3_swap12 (f : Fin n → Fin n → Fin n → ℝ) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ b, ∑ a, ∑ c, f a b c := Finset.sum_comm

theorem sum3_swap23 (f : Fin n → Fin n → Fin n → ℝ) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ a, ∑ c, ∑ b, f a b c := by
  apply Finset.sum_congr rfl; intro a _
  exact Finset.sum_comm

/-- Rotate the innermost summation index to the front: `∑ a ∑ b ∑ c = ∑ b ∑ c ∑ a`. -/
theorem sum3_rot (f : Fin n → Fin n → Fin n → ℝ) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ b, ∑ c, ∑ a, f a b c := by
  rw [sum3_swap12, sum3_swap23]

/-- Reverse a triple sum: `∑ a ∑ b ∑ c = ∑ c ∑ b ∑ a`. -/
theorem sum3_321 (f : Fin n → Fin n → Fin n → ℝ) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ c, ∑ b, ∑ a, f a b c := by
  rw [sum3_swap12, sum3_swap23, sum3_swap12]

theorem sum4_swap12 (f : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ b, ∑ a, ∑ c, ∑ d, f a b c d :=
  Finset.sum_comm

theorem sum4_swap23 (f : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ a, ∑ c, ∑ b, ∑ d, f a b c d := by
  apply Finset.sum_congr rfl; intro a _
  exact Finset.sum_comm

theorem sum4_swap34 (f : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ a, ∑ b, ∑ d, ∑ c, f a b c d := by
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  exact Finset.sum_comm

theorem sum5_swap12 (f : Fin n → Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f a b c d e) = ∑ b, ∑ a, ∑ c, ∑ d, ∑ e, f a b c d e :=
  Finset.sum_comm

theorem sum5_swap23 (f : Fin n → Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f a b c d e) = ∑ a, ∑ c, ∑ b, ∑ d, ∑ e, f a b c d e := by
  apply Finset.sum_congr rfl; intro a _
  exact Finset.sum_comm

theorem sum5_swap34 (f : Fin n → Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f a b c d e) = ∑ a, ∑ b, ∑ d, ∑ c, ∑ e, f a b c d e := by
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  exact Finset.sum_comm

theorem sum5_swap45 (f : Fin n → Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f a b c d e) = ∑ a, ∑ b, ∑ c, ∑ e, ∑ d, f a b c d e := by
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  apply Finset.sum_congr rfl; intro c _
  exact Finset.sum_comm

/-- Rotate the innermost summation index of a fivefold sum to the front. -/
theorem sum5_rot (f : Fin n → Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f a b c d e) = ∑ b, ∑ c, ∑ d, ∑ e, ∑ a, f a b c d e := by
  rw [sum5_swap12, sum5_swap23, sum5_swap34, sum5_swap45]

/-! ## Orthogonality -/

/-- The columns of an orthogonal matrix are orthonormal: `∑ p, A p c * A p c' = δ_{c c'}`. -/
theorem orthCols (A : Matrix (Fin n) (Fin n) ℝ) (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ)
    (c c' : Fin n) : ∑ p, A p c * A p c' = if c = c' then 1 else 0 := by
  have h : Aᵀ * A = 1 := Iff.mp (Matrix.mem_orthogonalGroup_iff' (n := Fin n) (R := ℝ)) hA
  have h1 : (Aᵀ * A) c c' = ∑ p, A p c * A p c' := by
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun p _ => by rw [Matrix.transpose_apply]
  rw [← h1, h, Matrix.one_apply]

/-! ## The Ricci contraction transforms as a `(0,2)`-tensor -/

theorem ricArr_rot (A : Matrix (Fin n) (Fin n) ℝ) (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ)
    (R : Curv4 n) (i p : Fin n) :
    ricArr (rot A R) i p = ∑ e, A p e * (∑ c, A i c * ricArr R c e) := by
  simp only [ricArr, rot]
  rw [show (∑ e, A p e * (∑ c, A i c * ∑ a, R a c a e))
        = ∑ e, ∑ c, ∑ a, A p e * (A i c * R a c a e) from by simp only [Finset.mul_sum]]
  calc ∑ a, ∑ a_1, ∑ b, ∑ c, ∑ d, A a a_1 * A i b * A a c * A p d * R a_1 b c d
      = ∑ a_1, ∑ b, ∑ c, ∑ d, ∑ a, A a a_1 * A i b * A a c * A p d * R a_1 b c d :=
        sum5_rot (fun a a_1 b c d => A a a_1 * A i b * A a c * A p d * R a_1 b c d)
    _ = ∑ a_1, ∑ b, ∑ c, ∑ d, (∑ a, A a a_1 * A a c) * (A i b * A p d * R a_1 b c d) := by
        apply Finset.sum_congr rfl; intro a_1 _
        apply Finset.sum_congr rfl; intro b _
        apply Finset.sum_congr rfl; intro c _
        apply Finset.sum_congr rfl; intro d _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl; intro a _
        ring
    _ = ∑ a_1, ∑ b, ∑ c, ∑ d, (if a_1 = c then 1 else 0) * (A i b * A p d * R a_1 b c d) := by
        apply Finset.sum_congr rfl; intro a_1 _
        apply Finset.sum_congr rfl; intro b _
        apply Finset.sum_congr rfl; intro c _
        apply Finset.sum_congr rfl; intro d _
        rw [orthCols A hA a_1 c]
    _ = ∑ a_1, ∑ b, ∑ d, A i b * A p d * R a_1 b a_1 d := by
        apply Finset.sum_congr rfl; intro a_1 _
        apply Finset.sum_congr rfl; intro b _
        rw [Finset.sum_eq_single a_1]
        · simp
        · intro c _ hc
          simp [show ¬ (a_1 = c) from fun h => hc h.symm]
        · intro h
          exact absurd (Finset.mem_univ a_1) h
    _ = ∑ e, ∑ c, ∑ a, A p e * (A i c * R a c a e) := by
        rw [show (∑ a_1, ∑ b, ∑ d, A i b * A p d * R a_1 b a_1 d)
              = ∑ d, ∑ b, ∑ a_1, A i b * A p d * R a_1 b a_1 d from
              sum3_321 (fun a_1 b d => A i b * A p d * R a_1 b a_1 d)]
        apply Finset.sum_congr rfl; intro e _
        apply Finset.sum_congr rfl; intro c _
        apply Finset.sum_congr rfl; intro a _
        ring

/-! ## Single-index contraction against an `A`-transformed vector -/

theorem contract_Avec (A : Matrix (Fin n) (Fin n) ℝ) (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ)
    (u v : Fin n → ℝ) :
    (∑ p, (∑ e, A p e * u e) * (∑ a, A p a * v a)) = ∑ e, u e * v e := by
  have expand : ∀ p, (∑ e, A p e * u e) * (∑ a, A p a * v a)
      = ∑ e, ∑ a, A p e * A p a * u e * v a := by
    intro p
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro e _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro a _
    ring
  calc ∑ p, (∑ e, A p e * u e) * (∑ a, A p a * v a)
      = ∑ p, ∑ e, ∑ a, A p e * A p a * u e * v a := by
        apply Finset.sum_congr rfl; intro p _; exact expand p
    _ = ∑ e, ∑ a, ∑ p, A p e * A p a * u e * v a :=
        sum3_rot (fun p e a => A p e * A p a * u e * v a)
    _ = ∑ e, ∑ a, (∑ p, A p e * A p a) * u e * v a := by
        apply Finset.sum_congr rfl; intro e _
        apply Finset.sum_congr rfl; intro a _
        rw [Finset.sum_mul, Finset.sum_mul]
    _ = ∑ e, ∑ a, (if e = a then 1 else 0) * u e * v a := by
        apply Finset.sum_congr rfl; intro e _
        apply Finset.sum_congr rfl; intro a _
        rw [orthCols A hA e a]
    _ = ∑ e, u e * v e := by
        apply Finset.sum_congr rfl; intro e _
        rw [Finset.sum_eq_single e]
        · simp
        · intro b _ hb; simp [show ¬ (e = b) from fun h => hb h.symm]
        · intro h; exact absurd (Finset.mem_univ e) h

/-! ## The definition of `rot`, factored -/

/-- `rot A R i j k l` with the last three summations factored out of the `a`-sum. -/
theorem rot_apply_factor (A : Matrix (Fin n) (Fin n) ℝ) (R : Curv4 n) (i j k l : Fin n) :
    rot A R i j k l = ∑ a, A i a * (∑ b, ∑ c, ∑ d, A j b * A k c * A l d * R a b c d) := by
  simp only [rot]
  apply Finset.sum_congr rfl; intro a _
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro b _
  apply Finset.sum_congr rfl; intro c _
  apply Finset.sum_congr rfl; intro d _
  ring

/-! ## Additivity of `rot` in the tensor -/

/-- `rot A R i j k l` with the last three summations factored out of the `j`-sum. -/
theorem rot_apply_factor2 (A : Matrix (Fin n) (Fin n) ℝ) (R : Curv4 n) (i j k l : Fin n) :
    rot A R i j k l = ∑ b, A j b * (∑ a, ∑ c, ∑ d, A i a * A k c * A l d * R a b c d) := by
  simp only [rot]
  rw [sum4_swap12]
  apply Finset.sum_congr rfl; intro b _
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro c _
  apply Finset.sum_congr rfl; intro d _
  ring

/-- `rot A R i j k l` with the last three summations factored out of the `k`-sum. -/
theorem rot_apply_factor3 (A : Matrix (Fin n) (Fin n) ℝ) (R : Curv4 n) (i j k l : Fin n) :
    rot A R i j k l = ∑ c, A k c * (∑ a, ∑ b, ∑ d, A i a * A j b * A l d * R a b c d) := by
  simp only [rot]
  rw [sum4_swap23, sum4_swap12]
  apply Finset.sum_congr rfl; intro c _
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  apply Finset.sum_congr rfl; intro d _
  ring

/-- `rot A R i j k l` with the last three summations factored out of the `l`-sum. -/
theorem rot_apply_factor4 (A : Matrix (Fin n) (Fin n) ℝ) (R : Curv4 n) (i j k l : Fin n) :
    rot A R i j k l = ∑ d, A l d * (∑ a, ∑ b, ∑ c, A i a * A j b * A k c * R a b c d) := by
  simp only [rot]
  rw [sum4_swap34, sum4_swap23, sum4_swap12]
  apply Finset.sum_congr rfl; intro d _
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  apply Finset.sum_congr rfl; intro c _
  ring

theorem rot_sub (A : Matrix (Fin n) (Fin n) ℝ) (S T : Curv4 n) :
    rot A (S - T) = rot A S - rot A T := by
  ext i j k l
  simp only [rot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

end Work.Diff.GE.react
