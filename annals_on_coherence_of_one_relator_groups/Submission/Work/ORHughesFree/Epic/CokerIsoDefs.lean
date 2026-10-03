/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Auxiliary definitions for `Epic/exists_unit_of_coker_iso`

This file contains the small library of definitions and index-bookkeeping lemmas that the
proof of the strengthened Schanuel lemma `exists_unit_of_coker_iso` (and of its two auxiliary
row-space computations `Epic/range_rowMulLin_blk` and `Epic/range_rowMulLin_blkB`) uses:

* `CokerIso.sumProdEquiv` is the linear equivalence `R^n × R^{n'} ≃ R^{n+n'}` that identifies a
  pair of vectors with a single vector indexed by `Fin (n + n')`, splitting the index set in the
  two blocks `Fin n` and `Fin n'` by means of `finSumFinEquiv`;
* `CokerIso.rowMatrixOf` is the matrix attached to a linear map `R^a → R^b` (its `i`-th row is
  the image of the `i`-th standard basis vector), together with the fact that the row map
  `rowMulLin` and `rowMatrixOf` are mutually inverse;
* the remaining lemmas are elementary index computations about `finSumFinEquiv` and
  `RankAPI.swapFin`.
-/
import Mathlib
import Submission.Work.ORHughesFree.Epic.rk_blkM_defs
import Submission.Work.ORHughesFree.RankAPI.rk_mul_add_le

set_option autoImplicit false

namespace Work.ORHughesFree.Epic.CokerIso

open Matrix Work.ORHughesFree

variable {R : Type*}

/-! ## The linear equivalence `R^n × R^{n'} ≃ R^{n+n'}` -/

/-- The linear equivalence that identifies a pair `(x, y)` of vectors with the single vector
indexed by `Fin (n + n')` whose two halves are `x` and `y`, where the two halves are obtained by
splitting the index set with `finSumFinEquiv`. -/
def sumProdEquiv (R : Type*) [Semiring R] (n n' : ℕ) :
    ((Fin n → R) × (Fin n' → R)) ≃ₗ[R] (Fin (n + n') → R) where
  toFun p := fun k => Sum.elim p.1 p.2 (finSumFinEquiv.symm k)
  invFun v := (fun i => v (finSumFinEquiv (Sum.inl i)), fun j => v (finSumFinEquiv (Sum.inr j)))
  left_inv p := by
    ext i <;> simp
  right_inv v := by
    funext k
    cases h : finSumFinEquiv.symm k with
    | inl i => rw [← Equiv.apply_symm_apply finSumFinEquiv k, h]; simp
    | inr j => rw [← Equiv.apply_symm_apply finSumFinEquiv k, h]; simp
  map_add' p q := by
    funext k
    cases h : finSumFinEquiv.symm k with
    | inl i => rw [← Equiv.apply_symm_apply finSumFinEquiv k, h]; simp
    | inr j => rw [← Equiv.apply_symm_apply finSumFinEquiv k, h]; simp
  map_smul' c p := by
    funext k
    cases h : finSumFinEquiv.symm k with
    | inl i => rw [← Equiv.apply_symm_apply finSumFinEquiv k, h]; simp
    | inr j => rw [← Equiv.apply_symm_apply finSumFinEquiv k, h]; simp

theorem sumProdEquiv_apply_fst {R : Type*} [Semiring R] {n n' : ℕ}
    (p : (Fin n → R) × (Fin n' → R)) (i : Fin n) :
    sumProdEquiv R n n' p (finSumFinEquiv (Sum.inl i)) = p.1 i := by
  simp [sumProdEquiv]

theorem sumProdEquiv_apply_snd {R : Type*} [Semiring R] {n n' : ℕ}
    (p : (Fin n → R) × (Fin n' → R)) (j : Fin n') :
    sumProdEquiv R n n' p (finSumFinEquiv (Sum.inr j)) = p.2 j := by
  simp [sumProdEquiv]

theorem sumProdEquiv_symm_fst {R : Type*} [Semiring R] {n n' : ℕ}
    (v : Fin (n + n') → R) (i : Fin n) :
    ((sumProdEquiv R n n').symm v).1 i = v (finSumFinEquiv (Sum.inl i)) := by
  simp [sumProdEquiv]

theorem sumProdEquiv_symm_snd {R : Type*} [Semiring R] {n n' : ℕ}
    (v : Fin (n + n') → R) (j : Fin n') :
    ((sumProdEquiv R n n').symm v).2 j = v (finSumFinEquiv (Sum.inr j)) := by
  simp [sumProdEquiv]

/-! ## Index computations for `finSumFinEquiv` and `swapFin` -/

theorem swapFin_finSumFinEquiv_inl {n n' : ℕ} (i : Fin n) :
    Work.ORHughesFree.RankAPI.swapFin n n' (finSumFinEquiv (Sum.inl i)) =
      finSumFinEquiv (Sum.inr i) := by
  simp [Work.ORHughesFree.RankAPI.swapFin]

theorem swapFin_finSumFinEquiv_inr {n n' : ℕ} (j : Fin n') :
    Work.ORHughesFree.RankAPI.swapFin n n' (finSumFinEquiv (Sum.inr j)) =
      finSumFinEquiv (Sum.inl j) := by
  simp [Work.ORHughesFree.RankAPI.swapFin]

/-- Splitting `Fin (n + n')` with `finSumFinEquiv` after `swapFin` exchanges the two blocks. -/
theorem finSumFinEquiv_symm_swapFin {n n' : ℕ} (j : Fin (n + n')) :
    finSumFinEquiv.symm (Work.ORHughesFree.RankAPI.swapFin n n' j) =
      Sum.swap (finSumFinEquiv.symm j) := by
  cases h : finSumFinEquiv.symm j with
  | inl i => rw [← Equiv.apply_symm_apply finSumFinEquiv j, h]; simp [Work.ORHughesFree.RankAPI.swapFin]
  | inr i => rw [← Equiv.apply_symm_apply finSumFinEquiv j, h]; simp [Work.ORHughesFree.RankAPI.swapFin]

/-! ## Matrices attached to linear maps -/

theorem sum_smul_single [Semiring R] {a : ℕ} (v : Fin a → R) :
    v = ∑ i, v i • (Pi.single i 1 : Fin a → R) := by
  ext j
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    rw [Pi.single_apply, if_neg (Ne.symm hb), mul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

theorem rowMulLin_single [Ring R] {a b : ℕ} (M : Matrix (Fin a) (Fin b) R) (i : Fin a) :
    rowMulLin M (Pi.single i 1) = M i := by
  ext j
  show (∑ l, (Pi.single i (1 : R) : Fin a → R) l * M l j) = M i j
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    rw [Pi.single_apply, if_neg hb, zero_mul]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem rowMulLin_mul [Ring R] {a b c : ℕ} (M : Matrix (Fin a) (Fin b) R)
    (N : Matrix (Fin b) (Fin c) R) :
    rowMulLin (M * N) = (rowMulLin N).comp (rowMulLin M) := by
  refine LinearMap.ext fun v => ?_
  refine funext fun j => ?_
  show (∑ i, v i * (∑ k, M i k * N k j)) = ∑ k, (∑ i, v i * M i k) * N k j
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by rw [mul_assoc]

/-- The matrix of a linear map `R^a → R^b`: its `i`-th row is the image of the `i`-th standard
basis vector. -/
noncomputable def rowMatrixOf [Ring R] {a b : ℕ} (f : (Fin a → R) →ₗ[R] (Fin b → R)) :
    Matrix (Fin a) (Fin b) R :=
  fun i j => f (Pi.single i 1) j

theorem rowMulLin_rowMatrixOf [Ring R] {a b : ℕ} (f : (Fin a → R) →ₗ[R] (Fin b → R)) :
    rowMulLin (rowMatrixOf f) = f := by
  refine LinearMap.ext fun v => ?_
  refine funext fun j => ?_
  show (∑ i, v i * f (Pi.single i (1 : R)) j) = f v j
  conv_rhs => rw [sum_smul_single v]
  rw [map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem rowMatrixOf_rowMulLin [Ring R] {a b : ℕ} (M : Matrix (Fin a) (Fin b) R) :
    rowMatrixOf (rowMulLin M) = M := by
  ext i j
  simp only [rowMatrixOf]
  rw [rowMulLin_single]

theorem rowMatrixOf_id [Ring R] (b : ℕ) :
    rowMatrixOf (LinearMap.id : (Fin b → R) →ₗ[R] (Fin b → R)) = 1 := by
  ext i j
  simp [rowMatrixOf, Matrix.one_apply, Pi.single_apply, eq_comm]

theorem rowMatrixOf_comp [Ring R] {a b c : ℕ}
    (f : (Fin a → R) →ₗ[R] (Fin b → R)) (g : (Fin b → R) →ₗ[R] (Fin c → R)) :
    rowMatrixOf (g.comp f) = rowMatrixOf f * rowMatrixOf g := by
  rw [← rowMatrixOf_rowMulLin (rowMatrixOf f * rowMatrixOf g), rowMulLin_mul,
    rowMulLin_rowMatrixOf, rowMulLin_rowMatrixOf]

end Work.ORHughesFree.Epic.CokerIso
