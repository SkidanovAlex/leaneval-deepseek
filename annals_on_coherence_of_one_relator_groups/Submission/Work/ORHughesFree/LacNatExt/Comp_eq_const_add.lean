/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The constant decomposition of the companion matrix

The companion matrix `lacComp B d` of `1 + B·diag(t)` is written, block by block, as the sum of a
*constant* matrix `lacCmat d n` (with `1` in the top-left block and `-1` along the diagonal of the
trailing `d*n` block) and the image of a constant matrix `lacAmat B d` under multiplication by the
variable `t`.

This is the algebraic identity that lets the rank computation for `lacComp` be reduced to the rank
computation for constant matrices: for every `(i,j)` entry of `lacComp B d` there are `c, a : R` with
`lacComp B d i j = c·1 + a·t`.

The four blocks of the companion are matched against the four blocks of `lacCmat + lacAmat·t`:

* `(0,0)` : `1 + C_0·t = (1)·1 + C_0·t`;
* `(0,>0)` : `(C_1 t, … , C_d t) = 0·1 + (C_1, …, C_d)·t`;
* `(>0,0)` : the block column `(t·1, 0, …, 0) = 0·1 + (1,0,…,0)·t`;
* `(>0,>0)` : `-1 + t·N = (-1)·1 + N·t`.
-/
import Mathlib
import Submission.Work.ORHughesFree.LacNatExt.PolyTDefs

set_option autoImplicit false

namespace Work.ORHughesFree.NaturalExtension

open Matrix

/-! ## Interaction of the two basic embeddings with `0`, `1`, `-1` -/

/-- The constant embedding sends `0` to `0`. -/
lemma laccstElt_zero {R : Type*} [Ring R] : laccstElt (0 : R) = 0 := by simp [laccstElt]

/-- The constant embedding sends `-1` to `-1`. -/
lemma laccstElt_neg_one {R : Type*} [Ring R] : laccstElt (-1 : R) = -1 := by simp [laccstElt]

/-- The map `r ↦ r·t` sends `0` to `0`. -/
lemma lacmulTElt_zero {R : Type*} [Ring R] : lacmulTElt (0 : R) = 0 := by simp [lacmulTElt]

/-- The map `r ↦ r·t` sends `1` to the variable `t`. -/
lemma lacmulTElt_one {R : Type*} [Ring R] [MulSemiringAction (Multiplicative ℤ) R] :
    lacmulTElt (1 : R) = skewLaurentT := by simp [lacmulTElt, skewLaurentT]

/-- The identity matrix over `R` is carried by the constant embedding to the identity matrix over
`R[t^{±1};τ]`. -/
lemma lacmap_one_cstElt {R : Type*} [Ring R] {n : ℕ} :
    (1 : Matrix (Fin n) (Fin n) R).map laccstElt = 1 := by
  ext i j
  by_cases h : i = j <;> simp [Matrix.map_apply, Matrix.one_apply, h, laccstElt]

/-- Addition commutes with `Matrix.submatrix`: this is the applied form of `Matrix.submatrix_add`
(the two submatrices must be taken along the *same* reindexing). -/
lemma lacsubmatrix_add_apply {m n l o : Type*} {α : Type*} [Add α]
    (A B : Matrix m n α) (e₁ : l → m) (e₂ : o → n) :
    A.submatrix e₁ e₂ + B.submatrix e₁ e₂ = (A + B).submatrix e₁ e₂ := rfl

/-! ## The four block identities -/

/-- `(0,0)`-block: `1·1 + C_0·t = 1 + C_0·t`. -/
lemma lacblk11 {R : Type*} [Ring R] [MulSemiringAction (Multiplicative ℤ) R]
    {n : ℕ} (B : Matrix (Fin n) (Fin n) (SkewL R)) :
    (1 : Matrix (Fin n) (Fin n) R).map laccstElt + (lacCcoef B 0).map lacmulTElt = lacXB B := by
  rw [lacmap_one_cstElt]
  rfl

/-- `(0,>0)`-block: `0·1 + (C_1,…,C_d)·t = (C_1 t, …, C_d t)`. -/
lemma lacblk12 {R : Type*} [Ring R] [MulSemiringAction (Multiplicative ℤ) R]
    {n : ℕ} (B : Matrix (Fin n) (Fin n) (SkewL R)) (d : ℕ) :
    (0 : Matrix (Fin n) (Fin (d * n)) R).map laccstElt + (lacYBC B d).map lacmulTElt = lacYB B d := by
  rw [Matrix.map_zero laccstElt laccstElt_zero, zero_add]
  rfl

/-- `(>0,0)`-block: `0·1 + (1,0,…,0)·t = (t·1, 0, …, 0)`. -/
lemma lacblk21 {R : Type*} [Ring R] [MulSemiringAction (Multiplicative ℤ) R] (d n : ℕ) :
    (0 : Matrix (Fin (d * n)) (Fin n) R).map laccstElt + (lacZBC d n).map lacmulTElt = lacZB d n := by
  rw [Matrix.map_zero laccstElt laccstElt_zero, zero_add]
  ext q p
  rw [Matrix.map_apply, lacZBC, lacZB, lacTmat, apply_ite lacmulTElt, apply_ite lacmulTElt,
    Matrix.diagonal_apply]
  simp [lacmulTElt, skewLaurentT]

/-- `(>0,>0)`-block: `(-1)·1 + N·t = -1 + t·N`. -/
lemma lacblk22 {R : Type*} [Ring R] [MulSemiringAction (Multiplicative ℤ) R] (d n : ℕ) :
    (lacWBC d n).map laccstElt + (lacWTC d n).map lacmulTElt = lacWB (R := R) d n := by
  ext q q'
  rw [Matrix.add_apply, Matrix.map_apply, Matrix.map_apply, lacWBC, lacWTC, lacWB,
    apply_ite laccstElt, apply_ite laccstElt, apply_ite lacmulTElt, apply_ite lacmulTElt]
  simp only [laccstElt_zero, laccstElt_neg_one, lacmulTElt_zero, lacmulTElt_one]

/-! ## The decomposition of the companion matrix -/

theorem lacComp_eq_const_add {R : Type*} [Ring R] [MulSemiringAction (Multiplicative ℤ) R]
    {n : ℕ} (B : Matrix (Fin n) (Fin n) (SkewL R)) (d : ℕ) :
    lacComp B d = (lacCmat d n).map laccstElt + (lacAmat B d).map lacmulTElt := by
  rw [lacComp, lacCmat, lacAmat, ← Matrix.submatrix_map, ← Matrix.submatrix_map,
    Matrix.fromBlocks_map, Matrix.fromBlocks_map, lacsubmatrix_add_apply, Matrix.fromBlocks_add,
    lacblk11, lacblk12, lacblk21, lacblk22]

end Work.ORHughesFree.NaturalExtension
