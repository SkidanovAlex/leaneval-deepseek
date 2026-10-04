import Mathlib
import Submission.Work.Diff.Alg.Pinch.Linv
import Submission.Work.Diff.GE.rot_contract
import Submission.Work.Diff.GE.react.RotKit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The `O(n)`-action on algebraic curvature tensors: a toolkit

`Submission.Diff.Alg.rot A R i j k l = ∑ a b c d, A i a * A j b * A k c * A l d * R a b c d` is the
action of a change of frame `A` on a curvature array.  This file collects the four structural
facts about it that the maximum-principle arguments of the Ricci-flow proof need, all in one
place (`Work.Diff.Alg.Pinch.rot_toolkit`):

* `rot A` maps algebraic curvature tensors to algebraic curvature tensors (for *any* `A`; no
  orthogonality is used for this part);
* `rot` is a monoid action: `rot A (rot B R) = rot (A * B) R` and `rot 1 R = R`;
* for `A ∈ O(n)` the Ricci tensor transforms as a `(0,2)`-tensor,
  `ric (rot A R) i j = ∑ b d, A i b * A j d * ric R b d`;
* for `A ∈ O(n)` the scalar curvature is unchanged, `scalAlg (rot A R) = scalAlg R`.

## Route

Regrouping a `Curv4` array as a matrix on its pair of index pairs
(`Work.Diff.GE.curvMat R (i,j) (k,l) = R i j k l`), a change of frame is the conjugation
`curvMat (rot A R) = (A ⊗ A) * curvMat R * (A ⊗ A)ᵀ` (`Work.Diff.GE.curvMat_rot`), so the
composition law follows from `(A ⊗ A) * (B ⊗ B) = ((A * B) ⊗ (A * B))`, and the invariance of
`scalAlg` (the trace of `curvMat`) from the cyclicity of the trace.  The preservation of the
algebraic symmetries is done indexwise: pair symmetry is `curvMat R` being symmetric, while
antisymmetry in the first pair and the first Bianchi identity are literal reindexings of the
defining fourfold sum (`rt_sum4_swap12`, `rt_sum4_cyc`, `rt_sum4_cyc'`).

## Main definitions

* `rt_pairs4`, `rt_cyc4`, `rt_cyc4'`: the index permutations of `Fin n × Fin n × Fin n × Fin n`
  used for the reindexings (`(a,b,c,d) ↦ (c,d,a,b)`, `↦ (b,c,a,d)`, `↦ (c,a,b,d)`).
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg
open scoped Matrix

variable {n : ℕ}

/-! ## Permutation equivalences and reindexing lemmas for fourfold sums -/

/-- The permutation `(a,b,c,d) ↦ (c,d,a,b)` of a fourfold index. -/
def rt_pairs4 (n : ℕ) : (Fin n × Fin n × Fin n × Fin n) ≃ (Fin n × Fin n × Fin n × Fin n) where
  toFun x := (x.2.2.1, (x.2.2.2, (x.1, x.2.1)))
  invFun x := (x.2.2.1, (x.2.2.2, (x.1, x.2.1)))
  left_inv := by rintro ⟨a, b, c, d⟩; rfl
  right_inv := by rintro ⟨a, b, c, d⟩; rfl

/-- The permutation `(a,b,c,d) ↦ (b,c,a,d)` of a fourfold index. -/
def rt_cyc4 (n : ℕ) : (Fin n × Fin n × Fin n × Fin n) ≃ (Fin n × Fin n × Fin n × Fin n) where
  toFun x := (x.2.1, (x.2.2.1, (x.1, x.2.2.2)))
  invFun x := (x.2.2.1, (x.1, (x.2.1, x.2.2.2)))
  left_inv := by rintro ⟨a, b, c, d⟩; rfl
  right_inv := by rintro ⟨a, b, c, d⟩; rfl

/-- The permutation `(a,b,c,d) ↦ (c,a,b,d)` of a fourfold index. -/
def rt_cyc4' (n : ℕ) : (Fin n × Fin n × Fin n × Fin n) ≃ (Fin n × Fin n × Fin n × Fin n) where
  toFun x := (x.2.2.1, (x.1, (x.2.1, x.2.2.2)))
  invFun x := (x.2.1, (x.2.2.1, (x.1, x.2.2.2)))
  left_inv := by rintro ⟨a, b, c, d⟩; rfl
  right_inv := by rintro ⟨a, b, c, d⟩; rfl

/-- A fourfold sum equals the single sum over the fourfold product of its indices. -/
theorem rt_split4 (f : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ x : Fin n × Fin n × Fin n × Fin n, f x.1 x.2.1 x.2.2.1 x.2.2.2)
      = ∑ a, ∑ b, ∑ c, ∑ d, f a b c d := by
  simp only [Fintype.sum_prod_type]

/-- The `(a,b,c,d) ↦ (c,d,a,b)`-reindexing as a single sum over the fourfold product. -/
theorem rt_split4_pairs (f : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ x : Fin n × Fin n × Fin n × Fin n, f x.2.2.1 x.2.2.2 x.1 x.2.1)
      = ∑ a, ∑ b, ∑ c, ∑ d, f c d a b := by
  simp only [Fintype.sum_prod_type]

/-- The `(a,b,c,d) ↦ (b,c,a,d)`-reindexing as a single sum over the fourfold product. -/
theorem rt_split4_cyc (f : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ x : Fin n × Fin n × Fin n × Fin n, f x.2.1 x.2.2.1 x.1 x.2.2.2)
      = ∑ a, ∑ b, ∑ c, ∑ d, f b c a d := by
  simp only [Fintype.sum_prod_type]

/-- The `(a,b,c,d) ↦ (c,a,b,d)`-reindexing as a single sum over the fourfold product. -/
theorem rt_split4_cyc' (f : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ x : Fin n × Fin n × Fin n × Fin n, f x.2.2.1 x.1 x.2.1 x.2.2.2)
      = ∑ a, ∑ b, ∑ c, ∑ d, f c a b d := by
  simp only [Fintype.sum_prod_type]

/-- Reindex a fourfold sum by the permutation `(a,b,c,d) ↦ (c,d,a,b)`. -/
theorem rt_sum4_pairs (f : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ a, ∑ b, ∑ c, ∑ d, f c d a b := by
  have hM : (∑ x : Fin n × Fin n × Fin n × Fin n, f x.2.2.1 x.2.2.2 x.1 x.2.1)
      = ∑ x : Fin n × Fin n × Fin n × Fin n, f x.1 x.2.1 x.2.2.1 x.2.2.2 := by
    simpa only [rt_pairs4, Equiv.coe_fn_mk] using
      (Equiv.sum_comp (rt_pairs4 n)
        (fun x : Fin n × Fin n × Fin n × Fin n => f x.1 x.2.1 x.2.2.1 x.2.2.2))
  exact (rt_split4 f).symm.trans (hM.symm.trans (rt_split4_pairs f))

/-- Reindex a fourfold sum by the permutation `(a,b,c,d) ↦ (b,c,a,d)`. -/
theorem rt_sum4_cyc (f : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ a, ∑ b, ∑ c, ∑ d, f b c a d := by
  have hM : (∑ x : Fin n × Fin n × Fin n × Fin n, f x.2.1 x.2.2.1 x.1 x.2.2.2)
      = ∑ x : Fin n × Fin n × Fin n × Fin n, f x.1 x.2.1 x.2.2.1 x.2.2.2 := by
    simpa only [rt_cyc4, Equiv.coe_fn_mk] using
      (Equiv.sum_comp (rt_cyc4 n)
        (fun x : Fin n × Fin n × Fin n × Fin n => f x.1 x.2.1 x.2.2.1 x.2.2.2))
  exact (rt_split4 f).symm.trans (hM.symm.trans (rt_split4_cyc f))

/-- Reindex a fourfold sum by the permutation `(a,b,c,d) ↦ (c,a,b,d)`. -/
theorem rt_sum4_cyc' (f : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ a, ∑ b, ∑ c, ∑ d, f c a b d := by
  have hM : (∑ x : Fin n × Fin n × Fin n × Fin n, f x.2.2.1 x.1 x.2.1 x.2.2.2)
      = ∑ x : Fin n × Fin n × Fin n × Fin n, f x.1 x.2.1 x.2.2.1 x.2.2.2 := by
    simpa only [rt_cyc4', Equiv.coe_fn_mk] using
      (Equiv.sum_comp (rt_cyc4' n)
        (fun x : Fin n × Fin n × Fin n × Fin n => f x.1 x.2.1 x.2.2.1 x.2.2.2))
  exact (rt_split4 f).symm.trans (hM.symm.trans (rt_split4_cyc' f))

/-- Swapping the first two indices of a fourfold sum. -/
theorem rt_sum4_swap12 (f : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ b, ∑ a, ∑ c, ∑ d, f a b c d :=
  Finset.sum_comm

/-- Distributing a sum of three fourfold sums. -/
theorem rt_sum_add3 (f1 f2 f3 : Fin n → Fin n → Fin n → Fin n → ℝ) :
    (∑ a, ∑ b, ∑ c, ∑ d, f1 a b c d) + (∑ a, ∑ b, ∑ c, ∑ d, f2 a b c d)
        + (∑ a, ∑ b, ∑ c, ∑ d, f3 a b c d)
      = ∑ a, ∑ b, ∑ c, ∑ d, (f1 a b c d + f2 a b c d + f3 a b c d) := by
  simp only [Finset.sum_add_distrib]

/-! ## `rot` preserves algebraic curvature tensors -/

/-- A change of frame preserves algebraic curvature tensors.  No orthogonality of `A` is needed. -/
theorem rt_rot_isAlgCurv (A : Matrix (Fin n) (Fin n) ℝ) {R : Curv4 n} (hR : IsAlgCurv R) :
    IsAlgCurv (rot A R) := by
  refine ⟨?_, ?_, ?_⟩
  · -- antisymmetry in the first pair
    intro i j k l
    have hkey : ∀ b a c d : Fin n, A j a * A i b * A k c * A l d * R a b c d
        = -(A i b * A j a * A k c * A l d * R b a c d) := by
      intro b a c d
      rw [hR.1 a b c d]
      ring
    have h2 : (∑ b, ∑ a, ∑ c, ∑ d, A j a * A i b * A k c * A l d * R a b c d)
        = ∑ b, ∑ a, ∑ c, ∑ d, -(A i b * A j a * A k c * A l d * R b a c d) := by
      apply Finset.sum_congr rfl; intro b _
      apply Finset.sum_congr rfl; intro a _
      apply Finset.sum_congr rfl; intro c _
      apply Finset.sum_congr rfl; intro d _
      exact hkey b a c d
    have h3 : (∑ b, ∑ a, ∑ c, ∑ d, -(A i b * A j a * A k c * A l d * R b a c d))
        = -(∑ a, ∑ b, ∑ c, ∑ d, A i a * A j b * A k c * A l d * R a b c d) := by
      simp only [Finset.sum_neg_distrib]
    calc rot A R j i k l
        = ∑ b, ∑ a, ∑ c, ∑ d, A j a * A i b * A k c * A l d * R a b c d := by
          simp only [rot]
          exact rt_sum4_swap12 _
      _ = ∑ b, ∑ a, ∑ c, ∑ d, -(A i b * A j a * A k c * A l d * R b a c d) := h2
      _ = -(∑ a, ∑ b, ∑ c, ∑ d, A i a * A j b * A k c * A l d * R a b c d) := h3
      _ = - rot A R i j k l := by simp only [rot]
  · -- pair symmetry, via the matrix regrouping of the two index pairs
    intro i j k l
    have hX : Matrix.transpose (Work.Diff.GE.curvMat R) = Work.Diff.GE.curvMat R := by
      ext x y
      obtain ⟨a, b⟩ := x
      obtain ⟨c, d⟩ := y
      simpa only [Matrix.transpose_apply, Work.Diff.GE.curvMat] using hR.2.1 a b c d
    have hsym : Matrix.transpose (Work.Diff.GE.curvMat (rot A R))
        = Work.Diff.GE.curvMat (rot A R) := by
      rw [Work.Diff.GE.curvMat_rot, Matrix.transpose_mul, Matrix.transpose_mul,
        Matrix.transpose_transpose, hX, Matrix.mul_assoc]
    have h1 : rot A R k l i j
        = Matrix.transpose (Work.Diff.GE.curvMat (rot A R)) (i, j) (k, l) := by
      rw [Matrix.transpose_apply]; rfl
    have h2 : Matrix.transpose (Work.Diff.GE.curvMat (rot A R)) (i, j) (k, l)
        = Work.Diff.GE.curvMat (rot A R) (i, j) (k, l) := by
      rw [hsym]
    have h3 : Work.Diff.GE.curvMat (rot A R) (i, j) (k, l) = rot A R i j k l := rfl
    exact h1.trans (h2.trans h3)
  · -- first Bianchi identity
    intro i j k l
    have hB2 : rot A R j k i l
        = ∑ a, ∑ b, ∑ c, ∑ d, A i a * A j b * A k c * A l d * R b c a d := by
      simp only [rot]
      nth_rewrite 1 [rt_sum4_cyc]
      apply Finset.sum_congr rfl; intro a _
      apply Finset.sum_congr rfl; intro b _
      apply Finset.sum_congr rfl; intro c _
      apply Finset.sum_congr rfl; intro d _
      ring
    have hB3 : rot A R k i j l
        = ∑ a, ∑ b, ∑ c, ∑ d, A i a * A j b * A k c * A l d * R c a b d := by
      simp only [rot]
      nth_rewrite 1 [rt_sum4_cyc']
      apply Finset.sum_congr rfl; intro a _
      apply Finset.sum_congr rfl; intro b _
      apply Finset.sum_congr rfl; intro c _
      apply Finset.sum_congr rfl; intro d _
      ring
    have hsum : rot A R i j k l + rot A R j k i l + rot A R k i j l
        = ∑ a, ∑ b, ∑ c, ∑ d, (A i a * A j b * A k c * A l d)
            * (R a b c d + R b c a d + R c a b d) := by
      rw [show rot A R i j k l
            = ∑ a, ∑ b, ∑ c, ∑ d, A i a * A j b * A k c * A l d * R a b c d from by
          simp only [rot],
          hB2, hB3, rt_sum_add3]
      apply Finset.sum_congr rfl; intro a _
      apply Finset.sum_congr rfl; intro b _
      apply Finset.sum_congr rfl; intro c _
      apply Finset.sum_congr rfl; intro d _
      ring
    rw [hsum]
    simp [hR.2.2]

/-! ## The action is a monoid action -/

/-- The matrix regrouping is injective. -/
theorem rt_curvMat_injective :
    Function.Injective (Work.Diff.GE.curvMat : Curv4 n → Matrix (Fin n × Fin n) (Fin n × Fin n) ℝ) := by
  intro R S h
  funext i j k l
  have h2 := congr_fun (congr_fun h (i, j)) (k, l)
  simpa only [Work.Diff.GE.curvMat] using h2

/-- The twofold Kronecker matrix is multiplicative. -/
theorem rt_kronAA_mul (A B : Matrix (Fin n) (Fin n) ℝ) :
    Work.Diff.GE.kronAA (A * B) = Work.Diff.GE.kronAA A * Work.Diff.GE.kronAA B := by
  simp only [Work.Diff.GE.kronAA]
  rw [← Matrix.mul_kronecker_mul A B A B]

/-- `rot` is multiplicative in the frame: `rot A (rot B R) = rot (A * B) R`. -/
theorem rt_rot_mul (A B : Matrix (Fin n) (Fin n) ℝ) (R : Curv4 n) :
    rot A (rot B R) = rot (A * B) R := by
  apply rt_curvMat_injective
  rw [Work.Diff.GE.curvMat_rot, Work.Diff.GE.curvMat_rot, Work.Diff.GE.curvMat_rot,
    rt_kronAA_mul, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

/-- `rot` of the identity frame is the identity: `rot 1 R = R`. -/
theorem rt_rot_one (R : Curv4 n) :
    rot (1 : Matrix (Fin n) (Fin n) ℝ) R = R := by
  apply rt_curvMat_injective
  rw [Work.Diff.GE.curvMat_rot]
  have h : Work.Diff.GE.kronAA (1 : Matrix (Fin n) (Fin n) ℝ) = 1 := by
    simp only [Work.Diff.GE.kronAA]
    exact Matrix.one_kronecker_one
  rw [h, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]

/-! ## The scalar curvature is frame-invariant -/

/-- For an orthogonal change of frame the scalar curvature is unchanged. -/
theorem rt_scalAlg_rot (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ) (R : Curv4 n) :
    scalAlg (rot A R) = scalAlg R := by
  have htr : ∀ S : Curv4 n, Matrix.trace (Work.Diff.GE.curvMat S) = scalAlg S := by
    intro S
    rw [Matrix.trace, scalAlg]
    exact Fintype.sum_prod_type (fun p : Fin n × Fin n => Work.Diff.GE.curvMat S p p)
  have hK : Matrix.transpose (Work.Diff.GE.kronAA A) * Work.Diff.GE.kronAA A = 1 :=
    Work.Diff.GE.kronAA_orth A hA
  rw [← htr (rot A R), ← htr R, Work.Diff.GE.curvMat_rot]
  rw [Matrix.trace_mul_cycle]
  rw [hK, Matrix.one_mul]

/-! ## The Ricci tensor transforms as a `(0,2)`-tensor -/

/-- Under an orthogonal change of frame the Ricci tensor transforms as a `(0,2)`-tensor. -/
theorem rt_ric_rot (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ) (R : Curv4 n) :
    ∀ i j : Fin n, ric (rot A R) i j = ∑ b, ∑ d, A i b * A j d * ric R b d := by
  intro i j
  have h1 : ric (rot A R) i j = Work.Diff.Evol.ricArr (rot A R) i j := rfl
  have h2 : Work.Diff.Evol.ricArr (rot A R) i j
      = ∑ e, A j e * (∑ c, A i c * Work.Diff.Evol.ricArr R c e) :=
    Work.Diff.GE.react.ricArr_rot A hA R i j
  have h3 : (∑ e, A j e * (∑ c, A i c * Work.Diff.Evol.ricArr R c e))
      = ∑ e, ∑ c, A j e * (A i c * Work.Diff.Evol.ricArr R c e) := by
    simp only [Finset.mul_sum]
  have h4 : (∑ e, ∑ c, A j e * (A i c * Work.Diff.Evol.ricArr R c e))
      = ∑ c, ∑ e, A j e * (A i c * Work.Diff.Evol.ricArr R c e) := Finset.sum_comm
  have h5 : (∑ c, ∑ e, A j e * (A i c * Work.Diff.Evol.ricArr R c e))
      = ∑ b, ∑ d, A i b * A j d * Work.Diff.Evol.ricArr R b d := by
    apply Finset.sum_congr rfl; intro b _
    apply Finset.sum_congr rfl; intro d _
    ring
  have h6 : (∑ b, ∑ d, A i b * A j d * Work.Diff.Evol.ricArr R b d)
      = ∑ b, ∑ d, A i b * A j d * ric R b d := by
    apply Finset.sum_congr rfl; intro b _
    apply Finset.sum_congr rfl; intro d _
    rfl
  exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans h6))))

/-- **Toolkit for the `O(n)`-action on algebraic curvature tensors.**  For `A ∈ O(n)` and an
algebraic curvature tensor `R`: `rot A R` is again algebraic; `rot` is a monoid action
(`rot A (rot B R) = rot (A * B) R`, `rot 1 R = R`, with `B` arbitrary); the Ricci tensor transforms
as a `(0,2)`-tensor; and the scalar curvature is invariant. -/
theorem rot_toolkit (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ) {R : Submission.Diff.Alg.Curv4 n}
    (hR : Submission.Diff.Alg.IsAlgCurv R) :
    Submission.Diff.Alg.IsAlgCurv (Submission.Diff.Alg.rot A R)
      ∧ Submission.Diff.Alg.rot A (Submission.Diff.Alg.rot B R)
          = Submission.Diff.Alg.rot (A * B) R
      ∧ Submission.Diff.Alg.rot (1 : Matrix (Fin n) (Fin n) ℝ) R = R
      ∧ (∀ i j : Fin n, Work.Diff.Alg.Pinch.ric (Submission.Diff.Alg.rot A R) i j
          = ∑ b, ∑ d, A i b * A j d * Work.Diff.Alg.Pinch.ric R b d)
      ∧ (Submission.Diff.Alg.scalAlg (Submission.Diff.Alg.rot A R)
          = Submission.Diff.Alg.scalAlg R) :=
  ⟨rt_rot_isAlgCurv A hR, rt_rot_mul A B R, rt_rot_one R, rt_ric_rot A hA R,
    rt_scalAlg_rot A hA R⟩

end Work.Diff.Alg.Pinch
