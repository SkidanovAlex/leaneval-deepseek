/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The row space of the block matrix `blkB B`

For a matrix `B : m' × n'` over a ring `R` and a natural number `n`, the block matrix
`blkB B = [[B, 0], [0, 1_n]]`, with its two column blocks exchanged (see `rk_blkM_defs`),
has `m' + n` rows and `n + n'` columns.  This file computes its row space, as a submodule of
`R^{n+n'}`:

> `range (rowMulLin (blkB B)) = sumProdEquiv '' (⊤ × range (rowMulLin B))`,

i.e. it is the image, under the identification `R^n × R^{n'} ≃ R^{n+n'}`
(`CokerIso.sumProdEquiv`), of the product of all of `R^n` with the row space of `B`.  Indeed
the rows of `blkB B` indexed by the `Fin m'` block are the rows of `B` placed in the `Fin n'`
block of the target, while the rows indexed by the `Fin n` block are the standard basis
vectors of the `Fin n` block of the target.

This is the companion of `Epic/range_rowMulLin_blk_one`, where the roles of the two blocks
are exchanged; both are used in the strengthened Schanuel lemma
`Epic/exists_unit_of_coker_iso`.
-/
import Mathlib
import Submission.Work.ORHughesFree.Epic.CokerIsoDefs

set_option autoImplicit false

namespace Work.ORHughesFree.Epic

open Matrix

/-! ## Auxiliary computations with `finSumFinEquiv` -/

/-- Splitting a sum indexed by `Fin (a + b)` into the two blocks of `finSumFinEquiv`. -/
private lemma sum_fin_add {M : Type*} [AddCommMonoid M] {a b : ℕ} (f : Fin (a + b) → M) :
    ∑ i, f i = (∑ p : Fin a, f (finSumFinEquiv (Sum.inl p))) +
      (∑ q : Fin b, f (finSumFinEquiv (Sum.inr q))) := by
  rw [← Equiv.sum_comp (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b)) f, Fintype.sum_sum_type]

/-! ## The entries of `blkB B`

The four blocks of `blkB B`, computed in terms of the natural splitting of its rows
(`Fin m' ⊕ Fin n`, via `finSumFinEquiv`) and of its columns (`Fin n ⊕ Fin n'`, via
`finSumFinEquiv` after the exchange of blocks performed by `RankAPI.swapFin`). -/

private lemma blkB_entry_inl_inl {R : Type*} [Zero R] [One R] {m' n n' : ℕ}
    (B : Matrix (Fin m') (Fin n') R) (a : Fin m') (k : Fin n) :
    blkB B (finSumFinEquiv (Sum.inl a) : Fin (m' + n))
      (finSumFinEquiv (Sum.inl k) : Fin (n + n')) = 0 := by
  simp [blkB, Matrix.submatrix, Work.ORHughesFree.RankAPI.swapFin]

private lemma blkB_entry_inl_inr {R : Type*} [Zero R] [One R] {m' n n' : ℕ}
    (B : Matrix (Fin m') (Fin n') R) (a : Fin m') (ty : Fin n') :
    blkB B (finSumFinEquiv (Sum.inl a) : Fin (m' + n))
      (finSumFinEquiv (Sum.inr ty) : Fin (n + n')) = B a ty := by
  simp [blkB, Matrix.submatrix, Work.ORHughesFree.RankAPI.swapFin]

private lemma blkB_entry_inr_inl {R : Type*} [Zero R] [One R] {m' n n' : ℕ}
    (B : Matrix (Fin m') (Fin n') R) (k k' : Fin n) :
    blkB B (finSumFinEquiv (Sum.inr k) : Fin (m' + n))
      (finSumFinEquiv (Sum.inl k') : Fin (n + n')) = if k = k' then 1 else 0 := by
  simp [blkB, Matrix.submatrix, Work.ORHughesFree.RankAPI.swapFin, Matrix.one_apply]

private lemma blkB_entry_inr_inr {R : Type*} [Zero R] [One R] {m' n n' : ℕ}
    (B : Matrix (Fin m') (Fin n') R) (k : Fin n) (ty : Fin n') :
    blkB B (finSumFinEquiv (Sum.inr k) : Fin (m' + n))
      (finSumFinEquiv (Sum.inr ty) : Fin (n + n')) = 0 := by
  simp [blkB, Matrix.submatrix, Work.ORHughesFree.RankAPI.swapFin]

/-! ## The linear map `rowMulLin (blkB B)` -/

/-- Pointwise computation of the row map of `blkB B`: in the splitting
`R^{m'+n} ≃ R^{m'} × R^n` of its source and the splitting `R^{n+n'} ≃ R^n × R^{n'}` of its
target (both induced by `CokerIso.sumProdEquiv`), it is the map
`(u, x) ↦ (x, rowMulLin B u)`. -/
private lemma rowMulLin_blkB_apply_aux {R : Type*} [Ring R] {m' n n' : ℕ}
    (B : Matrix (Fin m') (Fin n') R) (v : Fin (m' + n) → R) :
    rowMulLin (blkB B) v =
      CokerIso.sumProdEquiv R n n'
        ((fun k : Fin n => v (finSumFinEquiv (Sum.inr k))),
         rowMulLin B (fun a : Fin m' => v (finSumFinEquiv (Sum.inl a)))) := by
  funext j
  show (∑ i : Fin (m' + n), v i * blkB B i j) = _
  cases h : finSumFinEquiv.symm j with
  | inl k =>
    have hj : j = (finSumFinEquiv (Sum.inl k) : Fin (n + n')) := by
      rw [← h, Equiv.apply_symm_apply]
    rw [hj]
    rw [sum_fin_add (a := m') (b := n)
      (fun i : Fin (m' + n) => v i * blkB B i
        (finSumFinEquiv (Sum.inl k) : Fin (n + n')))]
    simp [CokerIso.sumProdEquiv, blkB, Matrix.submatrix,
      Work.ORHughesFree.RankAPI.swapFin, Matrix.one_apply]
  | inr ty =>
    have hj : j = (finSumFinEquiv (Sum.inr ty) : Fin (n + n')) := by
      rw [← h, Equiv.apply_symm_apply]
    rw [hj]
    rw [sum_fin_add (a := m') (b := n)
      (fun i : Fin (m' + n) => v i * blkB B i
        (finSumFinEquiv (Sum.inr ty) : Fin (n + n')))]
    simp [CokerIso.sumProdEquiv, blkB, Matrix.submatrix,
      Work.ORHughesFree.RankAPI.swapFin, rowMulLin]

/-! ## The row space of `blkB B` -/

theorem range_rowMulLin_blkB {R : Type*} [Ring R] {m' n n' : ℕ}
    (B : Matrix (Fin m') (Fin n') R) :
    LinearMap.range (Work.ORHughesFree.Epic.rowMulLin (Work.ORHughesFree.Epic.blkB B))
      = Submodule.map (Work.ORHughesFree.Epic.CokerIso.sumProdEquiv R n n').toLinearMap
          (Submodule.prod ⊤ (LinearMap.range (Work.ORHughesFree.Epic.rowMulLin B))) := by
  ext w
  constructor
  · rintro ⟨v, rfl⟩
    rw [rowMulLin_blkB_apply_aux B v]
    refine Submodule.mem_map_of_mem ?_
    exact Submodule.mem_prod.2 ⟨Submodule.mem_top,
      ⟨fun a : Fin m' => v (finSumFinEquiv (Sum.inl a)), rfl⟩⟩
  · intro hw
    rw [Submodule.mem_map] at hw
    obtain ⟨p, hp, hpw⟩ := hw
    obtain ⟨-, hy⟩ := Submodule.mem_prod.1 hp
    obtain ⟨u, hu⟩ := hy
    set v := CokerIso.sumProdEquiv R m' n (u, p.1) with hv
    refine ⟨v, ?_⟩
    rw [← hpw, rowMulLin_blkB_apply_aux B v]
    have h1 : (fun k : Fin n => v (finSumFinEquiv (Sum.inr k))) = p.1 := by
      funext k
      rw [hv]
      simp [CokerIso.sumProdEquiv]
    have hlam : (fun a : Fin m' => v (finSumFinEquiv (Sum.inl a))) = u := by
      funext a
      rw [hv]
      simp [CokerIso.sumProdEquiv]
    have h2 : rowMulLin B (fun a : Fin m' => v (finSumFinEquiv (Sum.inl a))) = p.2 := by
      rw [hlam, hu]
    exact congrArg (CokerIso.sumProdEquiv R n n') (Prod.ext h1 h2)

end Work.ORHughesFree.Epic
