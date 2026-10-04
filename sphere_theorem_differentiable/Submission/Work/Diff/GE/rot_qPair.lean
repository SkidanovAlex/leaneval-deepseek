import Mathlib
import Submission.Diff.Grad

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Work.Diff.GE.rot_qPair`

`qPair` (i.e. `⟪R, Q(R)⟫` for Hamilton's quadratic term `Q`) is invariant under the natural
`O(n)`-action `rot A` on 4-index arrays.

The proof is a two-step reduction.

* `rqDot X Y = tr (Xᵀ * Y)` is the Frobenius pairing on `Mat2 n = Matrix (Fin n × Fin n) (Fin n × Fin n) ℝ`.
  Under conjugation by an orthogonal matrix `E` it is invariant: `rqDot_conj`.
* `qPair R` decomposes into three "matrix" invariants, according to the three ways of pairing the
  four indices `{1,2,3,4}` into two pairs:

  `qPair R = rqA1 R + 2 * rqA2 R - 2 * rqA3 R`

  with `rqA1 R = rqDot (rqM R) ((rqM R) * (rqM R)ᵀ)`, `rqA2 R = rqDot (rqN R) ((rqN R)*(rqN R)ᵀ)`
  and `rqA3 R = rqDot (rqP R) ((rqN R)*(rqN R)ᵀ)`, where `rqM`, `rqN`, `rqP` are the three
  groupings `(i,j)|(k,l)`, `(i,k)|(j,l)`, `(i,l)|(j,k)`.

Since `rot A` acts on each of these groupings as conjugation by `E = rqKr A = A ⊗ A`, and
`E` is orthogonal whenever `A` is, each of the three terms is invariant.
-/

set_option linter.unusedSimpArgs false

namespace Work.Diff.GE

open Finset Matrix
open Submission.Diff.Alg

variable {n : ℕ}

/-! ## The Frobenius pairing on `n² × n²` matrices -/

/-- `n² × n²` matrices over `ℝ`: the index type is `(Fin n × Fin n)`. -/
abbrev rqMat (n : ℕ) := Matrix (Fin n × Fin n) (Fin n × Fin n) ℝ

/-- Frobenius pairing `tr (Xᵀ * Y)`. -/
noncomputable def rqDot (X Y : rqMat n) : ℝ := Matrix.trace (Xᵀ * Y)

lemma rqDot_eq_sum (X Y : rqMat n) : rqDot X Y = ∑ p, ∑ q, X p q * Y p q := by
  rw [rqDot, Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]

/-- `A ⊗ A`, the orthogonal action of `A ∈ O(n)` on a single pair of indices. -/
noncomputable def rqKr (A : Matrix (Fin n) (Fin n) ℝ) : rqMat n :=
  Matrix.kroneckerMap (fun x y => x * y) A A

lemma rqKr_apply (A : Matrix (Fin n) (Fin n) ℝ) (p q : Fin n × Fin n) :
    rqKr A p q = A p.1 q.1 * A p.2 q.2 :=
  Matrix.kroneckerMap_apply (fun x y => x * y) A A p q

lemma rqKr_transpose (A : Matrix (Fin n) (Fin n) ℝ) : (rqKr A)ᵀ = rqKr Aᵀ := by
  simp only [rqKr, ← Matrix.kroneckerMap_transpose]

lemma rqKr_mul (A B : Matrix (Fin n) (Fin n) ℝ) : rqKr A * rqKr B = rqKr (A * B) := by
  simp only [rqKr, ← Matrix.mul_kronecker_mul]

lemma rqKr_one : rqKr (1 : Matrix (Fin n) (Fin n) ℝ) = 1 := by
  simp only [rqKr, Matrix.one_kronecker_one]

lemma rqKr_orth {A : Matrix (Fin n) (Fin n) ℝ} (hA : Aᵀ * A = 1) : (rqKr A)ᵀ * rqKr A = 1 := by
  rw [rqKr_transpose, rqKr_mul, hA, rqKr_one]

/-! ## Conjugation by an orthogonal matrix preserves the pairing -/

lemma rq_conj_transpose (E X : rqMat n) : (E * X * Eᵀ)ᵀ = E * Xᵀ * Eᵀ := by
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

lemma rq_conj_mul {E X Y : rqMat n} (hE : Eᵀ * E = 1) :
    (E * X * Eᵀ) * (E * Y * Eᵀ) = E * (X * Y) * Eᵀ := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Eᵀ E (Y * Eᵀ), hE, Matrix.one_mul]

lemma rq_conj_sq {E X : rqMat n} (hE : Eᵀ * E = 1) :
    (E * X * Eᵀ) * (E * X * Eᵀ)ᵀ = E * (X * Xᵀ) * Eᵀ := by
  rw [rq_conj_transpose, rq_conj_mul hE]

lemma rqDot_conj {E X Y : rqMat n} (hE : Eᵀ * E = 1) :
    rqDot (E * X * Eᵀ) (E * Y * Eᵀ) = rqDot X Y := by
  rw [rqDot, rq_conj_transpose, rq_conj_mul hE]
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc Eᵀ E (Xᵀ * Y), hE, Matrix.one_mul, rqDot]

/-! ## The three groupings of a 4-index array as an `n² × n²` matrix -/

/-- Grouping `(i,j)|(k,l)`. -/
noncomputable def rqM (R : Curv4 n) : rqMat n := fun p q => R p.1 p.2 q.1 q.2

/-- Grouping `(i,k)|(j,l)`. -/
noncomputable def rqN (R : Curv4 n) : rqMat n := fun p q => R p.1 q.1 p.2 q.2

/-- Grouping `(i,l)|(j,k)`. -/
noncomputable def rqP (R : Curv4 n) : rqMat n := fun p q => R p.1 q.1 q.2 p.2

/-! ## Sums of four indices: flattening to pairs and permutations -/

lemma rq_sum_fin4_flat {M : Type*} [AddCommMonoid M]
    (f : Fin n → Fin n → Fin n → Fin n → M) :
    (∑ x, ∑ y, ∑ z, ∑ w, f x y z w)
      = ∑ p : Fin n × Fin n, ∑ q : Fin n × Fin n, f p.1 p.2 q.1 q.2 := by
  simp only [Fintype.sum_prod_type]

lemma rq_sum6_flat {M : Type*} [AddCommMonoid M]
    (f : Fin n → Fin n → Fin n → Fin n → Fin n → Fin n → M) :
    (∑ x, ∑ y, ∑ z, ∑ w, ∑ u, ∑ v, f x y z w u v)
      = ∑ p : Fin n × Fin n, ∑ q : Fin n × Fin n, ∑ r : Fin n × Fin n,
          f p.1 p.2 q.1 q.2 r.1 r.2 := by
  simp only [Fintype.sum_prod_type]

lemma rq_sum4_swap23 {M : Type*} [AddCommMonoid M]
    (f : Fin n → Fin n → Fin n → Fin n → M) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ a, ∑ c, ∑ b, ∑ d, f a b c d := by
  apply Finset.sum_congr rfl; intro a _
  exact Finset.sum_comm

lemma rq_sum4_rot234 {M : Type*} [AddCommMonoid M]
    (f : Fin n → Fin n → Fin n → Fin n → M) :
    (∑ a, ∑ b, ∑ c, ∑ d, f a b c d) = ∑ a, ∑ d, ∑ b, ∑ c, f a b c d := by
  apply Finset.sum_congr rfl; intro a _
  calc (∑ b, ∑ c, ∑ d, f a b c d) = ∑ b, ∑ d, ∑ c, f a b c d := by
        apply Finset.sum_congr rfl; intro b _
        exact Finset.sum_comm
    _ = ∑ d, ∑ b, ∑ c, f a b c d := Finset.sum_comm

/-! ## The action of `rot` on the three groupings -/

lemma rqM_rot (A : Matrix (Fin n) (Fin n) ℝ) (R : Curv4 n) :
    rqM (rot A R) = rqKr A * rqM R * (rqKr A)ᵀ := by
  ext p q
  rw [Matrix.mul_assoc]
  simp only [rqM, rqKr, Matrix.mul_apply, Matrix.transpose_apply, Matrix.kroneckerMap_apply, rot,
    Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  apply Finset.sum_congr rfl; intro c _
  apply Finset.sum_congr rfl; intro d _
  ring

lemma rqN_rot (A : Matrix (Fin n) (Fin n) ℝ) (R : Curv4 n) :
    rqN (rot A R) = rqKr A * rqN R * (rqKr A)ᵀ := by
  ext p q
  rw [Matrix.mul_assoc]
  simp only [rqN, rqKr, Matrix.mul_apply, Matrix.transpose_apply, Matrix.kroneckerMap_apply, rot,
    Fintype.sum_prod_type, Finset.mul_sum]
  rw [rq_sum4_swap23 (f := fun a b c d => A p.1 a * A q.1 b * A p.2 c * A q.2 d * R a b c d)]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  apply Finset.sum_congr rfl; intro c _
  apply Finset.sum_congr rfl; intro d _
  ring

lemma rqP_rot (A : Matrix (Fin n) (Fin n) ℝ) (R : Curv4 n) :
    rqP (rot A R) = rqKr A * rqP R * (rqKr A)ᵀ := by
  ext p q
  rw [Matrix.mul_assoc]
  simp only [rqP, rqKr, Matrix.mul_apply, Matrix.transpose_apply, Matrix.kroneckerMap_apply, rot,
    Fintype.sum_prod_type, Finset.mul_sum]
  rw [rq_sum4_rot234 (f := fun a b c d => A p.1 a * A q.1 b * A q.2 c * A p.2 d * R a b c d)]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  apply Finset.sum_congr rfl; intro c _
  apply Finset.sum_congr rfl; intro d _
  ring

/-! ## Decomposition of `qPair` into three matrix invariants -/

/-- First contraction pattern: `∑ Rᵢⱼₖₗ Rᵢⱼₚq Rₖₗₚq`. -/
noncomputable def rqA1 (R : Curv4 n) : ℝ :=
  ∑ i, ∑ j, ∑ k, ∑ l, ∑ p, ∑ q, R i j k l * (R i j p q * R k l p q)

/-- Second contraction pattern: `∑ Rᵢⱼₖₗ Rᵢₚₖq Rⱼₚₗq`. -/
noncomputable def rqA2 (R : Curv4 n) : ℝ :=
  ∑ i, ∑ j, ∑ k, ∑ l, ∑ p, ∑ q, R i j k l * (R i p k q * R j p l q)

/-- Third contraction pattern: `∑ Rᵢⱼₖₗ Rᵢₚₗq Rⱼₚₖq`. -/
noncomputable def rqA3 (R : Curv4 n) : ℝ :=
  ∑ i, ∑ j, ∑ k, ∑ l, ∑ p, ∑ q, R i j k l * (R i p l q * R j p k q)

/-- Linearity of a sum over the three-term combination occurring in `Q`. -/
lemma rq_sum_linearity {ι : Type*} [Fintype ι] (f g h : ι → ℝ) :
    (∑ x, (f x + 2 * g x - 2 * h x)) = (∑ x, f x) + 2 * (∑ x, g x) - 2 * (∑ x, h x) := by
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- Pointwise expansion of `Rᵢⱼₖₗ * Q(R)ᵢⱼₖₗ` into the three contraction patterns. -/
lemma rq_pointwise (R : Curv4 n) (i j k l : Fin n) :
    R i j k l * Q R i j k l
      = (∑ p, ∑ q, R i j k l * (R i j p q * R k l p q))
        + 2 * (∑ p, ∑ q, R i j k l * (R i p k q * R j p l q))
        - 2 * (∑ p, ∑ q, R i j k l * (R i p l q * R j p k q)) := by
  simp only [Q, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_add, mul_sub, mul_assoc,
    ← Finset.mul_sum]
  ring

theorem rq_qPair_eq (R : Curv4 n) : qPair R = rqA1 R + 2 * rqA2 R - 2 * rqA3 R := by
  rw [qPair, rqA1, rqA2, rqA3]
  simp only [rq_pointwise, rq_sum_linearity]

theorem rqA1_eq (R : Curv4 n) : rqA1 R = rqDot (rqM R) (rqM R * (rqM R)ᵀ) := by
  rw [rqA1, rq_sum6_flat (f := fun a b c d e f => R a b c d * (R a b e f * R c d e f)),
    rqDot_eq_sum]
  simp only [rqM, Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum]

theorem rqA2_eq (R : Curv4 n) : rqA2 R = rqDot (rqN R) (rqN R * (rqN R)ᵀ) := by
  rw [rqA2, rq_sum4_swap23 (f := fun a b c d => ∑ p, ∑ q, R a b c d * (R a p c q * R b p d q))]
  rw [rq_sum6_flat (f := fun a b c d e f => R a c b d * (R a e b f * R c e d f))]
  rw [rqDot_eq_sum]
  simp only [rqN, Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum]

theorem rqA3_eq (R : Curv4 n) : rqA3 R = rqDot (rqP R) (rqN R * (rqN R)ᵀ) := by
  rw [rqA3, rq_sum4_rot234 (f := fun a b c d => ∑ p, ∑ q, R a b c d * (R a p d q * R b p c q))]
  rw [rq_sum6_flat (f := fun a b c d e f => R a c d b * (R a e b f * R c e d f))]
  rw [rqDot_eq_sum]
  simp only [rqP, rqN, Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum]

/-! ## The theorem -/

theorem rot_qPair {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ Matrix.orthogonalGroup (Fin n) ℝ) (R : Submission.Diff.Alg.Curv4 n) :
    Submission.Diff.Alg.qPair (Submission.Diff.Alg.rot A R) = Submission.Diff.Alg.qPair R := by
  have hAA : Aᵀ * A = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).mp hA
  have hE : (rqKr A)ᵀ * rqKr A = 1 := rqKr_orth hAA
  have h1 : rqDot (rqM (rot A R)) (rqM (rot A R) * (rqM (rot A R))ᵀ)
      = rqDot (rqM R) (rqM R * (rqM R)ᵀ) := by
    rw [rqM_rot, rq_conj_sq hE, rqDot_conj hE]
  have h2 : rqDot (rqN (rot A R)) (rqN (rot A R) * (rqN (rot A R))ᵀ)
      = rqDot (rqN R) (rqN R * (rqN R)ᵀ) := by
    rw [rqN_rot, rq_conj_sq hE, rqDot_conj hE]
  have h3 : rqDot (rqP (rot A R)) (rqN (rot A R) * (rqN (rot A R))ᵀ)
      = rqDot (rqP R) (rqN R * (rqN R)ᵀ) := by
    rw [rqP_rot, rqN_rot, rq_conj_sq hE, rqDot_conj hE]
  rw [rq_qPair_eq (rot A R), rq_qPair_eq R]
  rw [rqA1_eq (rot A R), rqA2_eq (rot A R), rqA3_eq (rot A R),
    rqA1_eq R, rqA2_eq R, rqA3_eq R]
  rw [h1, h2, h3]

end Work.Diff.GE
