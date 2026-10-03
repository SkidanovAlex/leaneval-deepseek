/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ORBridgeLinnell area (one-relator coherence project)

# A ring carrying a faithful Sylvester rank function is directly finite

Let `rk` be a Sylvester matrix rank function on a ring `R` (with `rk 1 = 1`) which is
*faithful*: `rk (!![x]) = 0` forces `x = 0`.  Then `R` is directly finite:

`a * b = 1 → b * a = 1`.

The argument follows the standard "finite dimension function" pattern.

* `e := b * a` is idempotent and `rk (!![e]) = 1`: indeed `!![e] = !![b] * !![a]` bounds
  it above by `rk (!![b]) ≤ 1`, while `!![a] = !![a] * !![e]` bounds it below by
  `rk (!![a]) = 1` (which holds because `!![a] * !![b] = !![a * b] = !![1] = 1`).
* For **any** idempotent `p` with `rk (!![p]) = 1` one has `p = 1`.  The self-inverse unit
  `S = !![p, 1-p; 1-p, p]` conjugates `!![1, 0; 0, 0]` to `!![p, 0; 0, 1-p]`, and rank is
  invariant under conjugation by a unit, so

  `1 + rk (!![1-p]) = rk (!![p]) + rk (!![1-p]) = rk (!![p,0;0,1-p]) = rk (!![1,0;0,0]) = 1`

  (the middle equality is the block-diagonal axiom).  Hence `rk (!![1-p]) = 0` and
  faithfulness gives `1 - p = 0`, i.e. `p = 1`.

The same statement is proved for star projections in
`Submission.Work.ORVonNeumann.Regular.projection_rank_add`; here we only need the
ring-theoretic (star-free) version, so the file is self-contained.

## Main results

* `Work.ORBridgeLinnell.directlyFinite_of_faithful`
-/
import Mathlib
import Submission.Work.ORVonNeumann.SylvesterRank

set_option autoImplicit false

namespace Work.ORBridgeLinnell

open Work.ORVonNeumann

variable {R : Type*} [Ring R]

/-! ## Elementary matrix identities -/

/-- Product of two `1 × 1` "scalar" matrices. -/
private lemma single_mul_single (a b : R) :
    (!![a] : Matrix (Fin 1) (Fin 1) R) * !![b] = !![a * b] := by
  ext i j
  fin_cases i
  fin_cases j
  simp [Matrix.mul_apply]

/-- The `1 × 1` matrix `!![1]` is the identity matrix. -/
private lemma single_eq_one : (!![(1 : R)] : Matrix (Fin 1) (Fin 1) R) = 1 := by
  ext i j
  fin_cases i
  fin_cases j
  simp

/-- The `1 × 1` matrix `!![0]` is the zero matrix. -/
private lemma single_eq_zero : (!![(0 : R)] : Matrix (Fin 1) (Fin 1) R) = 0 := by
  ext i j
  fin_cases i
  fin_cases j
  simp

/-- The block diagonal of two `1 × 1` matrices is the corresponding explicit `2 × 2`
matrix. -/
private lemma blockDiag_fin_one (a b : R) :
    blockDiag (!![a] : Matrix (Fin 1) (Fin 1) R) (!![b] : Matrix (Fin 1) (Fin 1) R)
      = !![a, 0; 0, b] := by
  have h0 : (finSumFinEquiv (m := 1) (n := 1)).symm (0 : Fin 2) = Sum.inl (0 : Fin 1) :=
    finSumFinEquiv_symm_apply_castAdd (n := 1) (0 : Fin 1)
  have h1 : (finSumFinEquiv (m := 1) (n := 1)).symm (1 : Fin 2) = Sum.inr (0 : Fin 1) :=
    finSumFinEquiv_symm_apply_natAdd (m := 1) (0 : Fin 1)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blockDiag, Matrix.reindex_apply, h0, h1]

/-- The block-diagonal axiom, written out for two `1 × 1` blocks. -/
private lemma rank_diag_single (rk : SylvesterRankFunction R) (a b : R) :
    rk.rank (!![a, 0; 0, b] : Matrix (Fin 2) (Fin 2) R)
      = rk.rank (!![a] : Matrix (Fin 1) (Fin 1) R)
        + rk.rank (!![b] : Matrix (Fin 1) (Fin 1) R) := by
  rw [← blockDiag_fin_one a b, rk.rank_blockDiag]

/-! ## Rank is invariant under multiplication by units -/

/-- Left multiplication by an invertible square matrix does not change the rank. -/
private lemma rank_mul_of_isUnit_left (rk : SylvesterRankFunction R) {n m : ℕ}
    (U : Matrix (Fin n) (Fin n) R) (hU : IsUnit U) (A : Matrix (Fin n) (Fin m) R) :
    rk.rank (U * A) = rk.rank A := by
  obtain ⟨v, hv⟩ := hU.exists_left_inv
  refine le_antisymm (rk.rank_mul_le_right U A) ?_
  have h : v * (U * A) = A := by rw [← Matrix.mul_assoc, hv, Matrix.one_mul]
  calc rk.rank A = rk.rank (v * (U * A)) := by rw [h]
    _ ≤ rk.rank (U * A) := rk.rank_mul_le_right v (U * A)

/-- Right multiplication by an invertible square matrix does not change the rank. -/
private lemma rank_mul_of_isUnit_right (rk : SylvesterRankFunction R) {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) R) (U : Matrix (Fin m) (Fin m) R) (hU : IsUnit U) :
    rk.rank (A * U) = rk.rank A := by
  obtain ⟨v, hv⟩ := hU.exists_right_inv
  refine le_antisymm (rk.rank_mul_le_left A U) ?_
  have h : A * U * v = A := by rw [Matrix.mul_assoc, hv, Matrix.mul_one]
  calc rk.rank A = rk.rank (A * U * v) := by rw [h]
    _ ≤ rk.rank (A * U) := rk.rank_mul_le_left (A * U) v

/-- Two-sided conjugation by an invertible square matrix does not change the rank. -/
private lemma rank_conj_of_isUnit (rk : SylvesterRankFunction R) {n : ℕ}
    (U M : Matrix (Fin n) (Fin n) R) (hU : IsUnit U) :
    rk.rank (U * M * U) = rk.rank M := by
  rw [Matrix.mul_assoc, rank_mul_of_isUnit_left rk U hU (M * U),
    rank_mul_of_isUnit_right rk M U hU]

/-! ## The idempotent lemmas -/

/-- For an idempotent `p`, the `2 × 2` matrix `!![p, 1-p; 1-p, p]` is an involution. -/
private lemma idempotent_involution {p : R} (hp : p * p = p) :
    (!![p, 1 - p; 1 - p, p] : Matrix (Fin 2) (Fin 2) R) * !![p, 1 - p; 1 - p, p] = 1 := by
  have h1 : p * (1 - p) = 0 := by rw [mul_sub, mul_one, hp, sub_self]
  have h2 : (1 - p) * p = 0 := by rw [sub_mul, one_mul, hp, sub_self]
  have h3 : (1 - p) * (1 - p) = 1 - p := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hp]; abel
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hp, h1, h2, h3]

/-- For an idempotent `p`, conjugation of `!![1, 0; 0, 0]` by `!![p, 1-p; 1-p, p]`
produces `!![p, 0; 0, 1-p]`. -/
private lemma idempotent_conj {p : R} (hp : p * p = p) :
    (!![p, 1 - p; 1 - p, p] : Matrix (Fin 2) (Fin 2) R) * !![1, 0; 0, 0] *
      !![p, 1 - p; 1 - p, p] = !![p, 0; 0, 1 - p] := by
  have h1 : p * (1 - p) = 0 := by rw [mul_sub, mul_one, hp, sub_self]
  have h2 : (1 - p) * p = 0 := by rw [sub_mul, one_mul, hp, sub_self]
  have h3 : (1 - p) * (1 - p) = 1 - p := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hp]; abel
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hp, h1, h2, h3]

/-- An idempotent of rank `1` (with respect to a faithful rank function) equals `1`. -/
private lemma idempotent_rank_one_eq_one (rk : SylvesterRankFunction R) (h : rk.Faithful)
    {p : R} (hp : p * p = p) (hr : rk.rank (!![p] : Matrix (Fin 1) (Fin 1) R) = 1) :
    p = 1 := by
  have hrone : rk.rank (1 : Matrix (Fin 1) (Fin 1) R) = 1 := rk.rank_one
  set S : Matrix (Fin 2) (Fin 2) R := !![p, 1 - p; 1 - p, p] with hSdef
  have hS : S * S = 1 := by rw [hSdef]; exact idempotent_involution hp
  have hconj : S * !![1, 0; 0, 0] * S = !![p, 0; 0, 1 - p] := by
    rw [hSdef]; exact idempotent_conj hp
  have hunit : IsUnit S := ⟨⟨S, S, hS, hS⟩, rfl⟩
  have hL : rk.rank (!![p, 0; 0, 1 - p] : Matrix (Fin 2) (Fin 2) R)
      = rk.rank (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) R) := by
    rw [← hconj]
    exact rank_conj_of_isUnit rk S (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) R) hunit
  have hD : rk.rank (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) R) = 1 := by
    rw [rank_diag_single rk 1 0, single_eq_one, single_eq_zero, hrone]
    norm_num
  have hPd : rk.rank (!![p, 0; 0, 1 - p] : Matrix (Fin 2) (Fin 2) R)
      = 1 + rk.rank (!![1 - p] : Matrix (Fin 1) (Fin 1) R) := by
    rw [rank_diag_single rk p (1 - p), hr]
  have hsum : (1 : ℝ) + rk.rank (!![1 - p] : Matrix (Fin 1) (Fin 1) R) = 1 := by
    rw [← hPd, hL, hD]
  have hzero : rk.rank (!![1 - p] : Matrix (Fin 1) (Fin 1) R) = 0 := by linarith
  have hp0 : (1 : R) - p = 0 := h (1 - p) hzero
  exact (sub_eq_zero.mp hp0).symm

/-! ## The main theorem -/

theorem directlyFinite_of_faithful {R : Type*} [Ring R]
    (rk : Work.ORVonNeumann.SylvesterRankFunction R) (h : rk.Faithful) {a b : R}
    (hab : a * b = 1) : b * a = 1 := by
  have hrone : rk.rank (1 : Matrix (Fin 1) (Fin 1) R) = 1 := rk.rank_one
  -- `e := b * a` is idempotent
  have he : (b * a) * (b * a) = b * a := by
    rw [mul_assoc, ← mul_assoc a b a, hab, one_mul]
  -- `rk (!![a]) = 1`
  have hra : rk.rank (!![a] : Matrix (Fin 1) (Fin 1) R) = 1 := by
    have h1 : (1 : ℝ) ≤ rk.rank (!![a] : Matrix (Fin 1) (Fin 1) R) := by
      have h' := rk.rank_mul_le_left (!![a] : Matrix (Fin 1) (Fin 1) R)
        (!![b] : Matrix (Fin 1) (Fin 1) R)
      rw [single_mul_single, hab, single_eq_one, hrone] at h'
      exact h'
    have h2 : rk.rank (!![a] : Matrix (Fin 1) (Fin 1) R) ≤ 1 := by
      have h' := rk.rank_mul_le_right (!![a] : Matrix (Fin 1) (Fin 1) R)
        (1 : Matrix (Fin 1) (Fin 1) R)
      rw [Matrix.mul_one, hrone] at h'
      exact h'
    linarith
  -- `rk (!![b * a]) = 1`
  have hre : rk.rank (!![b * a] : Matrix (Fin 1) (Fin 1) R) = 1 := by
    refine le_antisymm ?_ ?_
    · have h' := rk.rank_mul_le_left (!![b] : Matrix (Fin 1) (Fin 1) R)
        (!![a] : Matrix (Fin 1) (Fin 1) R)
      rw [single_mul_single] at h'
      have h'' := rk.rank_mul_le_right (!![b] : Matrix (Fin 1) (Fin 1) R)
        (1 : Matrix (Fin 1) (Fin 1) R)
      rw [Matrix.mul_one, hrone] at h''
      exact le_trans h' h''
    · rw [← hra]
      have h' := rk.rank_mul_le_right (!![a] : Matrix (Fin 1) (Fin 1) R)
        (!![b * a] : Matrix (Fin 1) (Fin 1) R)
      have heq : (!![a] : Matrix (Fin 1) (Fin 1) R) * !![b * a] = !![a] := by
        rw [single_mul_single, show a * (b * a) = a from by rw [← mul_assoc, hab, one_mul]]
      rw [heq] at h'
      exact h'
  exact idempotent_rank_one_eq_one rk h he hre

end Work.ORBridgeLinnell
