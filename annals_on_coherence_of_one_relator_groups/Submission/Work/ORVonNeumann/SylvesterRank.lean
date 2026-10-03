/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ORVonNeumann area (N5 of the one-relator coherence project)

# Sylvester matrix rank functions

We formalise the notion of *Sylvester matrix rank function* on a ring, as used in
Jaikin-Zapirain–López-Álvarez, *The Atiyah conjecture for locally indicable groups*
(arXiv:1810.12135, §3.4).

A Sylvester matrix rank function on a ring `R` assigns to every matrix over `R` a
non-negative real number and satisfies

* `rk 0 = 0` and `rk 1 = 1`;
* `rk (A * B) ≤ min (rk A) (rk B)`;
* `rk (diag A B) = rk A + rk B`;
* `rk [[A, C], [0, B]] ≥ rk A + rk B`.

Non-negativity actually follows from the other axioms (see `SylvesterRankFunction.rank_nonneg`).

## Main definitions

* `Work.ORVonNeumann.SylvesterRankFunction` — the structure;
* `Work.ORVonNeumann.SylvesterRankFunction.rank` — evaluation;
* `Work.ORVonNeumann.SylvesterRankFunction.Faithful` — faithfulness on `1 × 1` matrices;
* `Work.ORVonNeumann.SylvesterRankFunction.map` — pull-back along a ring homomorphism.
-/
import Mathlib
import Submission.Work.ORVonNeumann.Basic

set_option autoImplicit false

universe u v

namespace Work.ORVonNeumann

open Matrix

variable {R : Type*} {S : Type*}

/-- The block diagonal matrix `diag A B`, with `Fin`-indexed blocks. -/
def blockDiag [Zero R] {n m p q : ℕ} (A : Matrix (Fin n) (Fin m) R) (B : Matrix (Fin p) (Fin q) R) :
    Matrix (Fin (n + p)) (Fin (m + q)) R :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A 0 0 B)

/-- The block matrix `[[A, C], [0, B]]`, with `Fin`-indexed blocks. -/
def blockUpper [Zero R] {n m p q : ℕ} (A : Matrix (Fin n) (Fin m) R) (C : Matrix (Fin n) (Fin q) R)
    (B : Matrix (Fin p) (Fin q) R) : Matrix (Fin (n + p)) (Fin (m + q)) R :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A C 0 B)

/-- A Sylvester matrix rank function on a ring `R`: a real-valued function on matrices over `R`
satisfying Jaikin-Zapirain's axioms (SMat1)–(SMat4). -/
structure SylvesterRankFunction (R : Type*) [Ring R] where
  /-- value of the rank function on an `n × m` matrix -/
  toFun : (n m : ℕ) → Matrix (Fin n) (Fin m) R → ℝ
  map_zero : ∀ n m : ℕ, toFun n m 0 = 0
  map_one : toFun 1 1 1 = 1
  mul_le : ∀ {n m k : ℕ} (A : Matrix (Fin n) (Fin m) R) (B : Matrix (Fin m) (Fin k) R),
    toFun n k (A * B) ≤ min (toFun n m A) (toFun m k B)
  blockDiag_add : ∀ {n m p q : ℕ} (A : Matrix (Fin n) (Fin m) R) (B : Matrix (Fin p) (Fin q) R),
    toFun (n + p) (m + q) (blockDiag A B) = toFun n m A + toFun p q B
  blockUpper_le : ∀ {n m p q : ℕ} (A : Matrix (Fin n) (Fin m) R) (C : Matrix (Fin n) (Fin q) R)
    (B : Matrix (Fin p) (Fin q) R),
    toFun n m A + toFun p q B ≤ toFun (n + p) (m + q) (blockUpper A C B)

namespace SylvesterRankFunction

variable [Ring R] [Ring S]

instance : CoeFun (SylvesterRankFunction R) (fun _ => (n m : ℕ) → Matrix (Fin n) (Fin m) R → ℝ) :=
  ⟨SylvesterRankFunction.toFun⟩

@[simp]
theorem toFun_eq_coe (rk : SylvesterRankFunction R) (n m : ℕ) : rk.toFun n m = rk n m := rfl

/-- Evaluation of a Sylvester rank function on a rectangular matrix. -/
def rank (rk : SylvesterRankFunction R) {n m : ℕ} (A : Matrix (Fin n) (Fin m) R) : ℝ :=
  rk n m A

@[simp]
theorem rank_zero (rk : SylvesterRankFunction R) (n m : ℕ) :
    rk.rank (0 : Matrix (Fin n) (Fin m) R) = 0 := rk.map_zero n m

@[simp]
theorem rank_one (rk : SylvesterRankFunction R) :
    rk.rank (1 : Matrix (Fin 1) (Fin 1) R) = 1 := rk.map_one

@[simp]
theorem toFun_zero (rk : SylvesterRankFunction R) (n m : ℕ) : rk n m (0 : Matrix (Fin n) (Fin m) R) = 0 :=
  rk.map_zero n m

@[simp]
theorem toFun_one (rk : SylvesterRankFunction R) : rk 1 1 (1 : Matrix (Fin 1) (Fin 1) R) = 1 :=
  rk.map_one

@[simp]
theorem rank_eq (rk : SylvesterRankFunction R) {n m : ℕ} (A : Matrix (Fin n) (Fin m) R) :
    rk.rank A = rk n m A := rfl

theorem rank_nonneg (rk : SylvesterRankFunction R) {n m : ℕ} (A : Matrix (Fin n) (Fin m) R) :
    0 ≤ rk.rank A := by
  have h : (0 : ℝ) ≤ min (rk.toFun n m A) 0 := by
    simpa using rk.mul_le A (0 : Matrix (Fin m) (Fin m) R)
  show (0 : ℝ) ≤ rk.toFun n m A
  rcases lt_or_ge (rk.toFun n m A) 0 with h' | h'
  · exact absurd h (not_le.mpr (min_lt_iff.mpr (Or.inl h')))
  · exact h'

theorem rank_mul_le_left (rk : SylvesterRankFunction R) {n m k : ℕ}
    (A : Matrix (Fin n) (Fin m) R) (B : Matrix (Fin m) (Fin k) R) :
    rk.rank (A * B) ≤ rk.rank A :=
  le_trans (rk.mul_le A B) (min_le_left _ _)

theorem rank_mul_le_right (rk : SylvesterRankFunction R) {n m k : ℕ}
    (A : Matrix (Fin n) (Fin m) R) (B : Matrix (Fin m) (Fin k) R) :
    rk.rank (A * B) ≤ rk.rank B :=
  le_trans (rk.mul_le A B) (min_le_right _ _)

theorem rank_blockDiag (rk : SylvesterRankFunction R) {n m p q : ℕ}
    (A : Matrix (Fin n) (Fin m) R) (B : Matrix (Fin p) (Fin q) R) :
    rk.rank (blockDiag A B) = rk.rank A + rk.rank B := rk.blockDiag_add A B

theorem rank_le_blockUpper (rk : SylvesterRankFunction R) {n m p q : ℕ}
    (A : Matrix (Fin n) (Fin m) R) (C : Matrix (Fin n) (Fin q) R) (B : Matrix (Fin p) (Fin q) R) :
    rk.rank A + rk.rank B ≤ rk.rank (blockUpper A C B) := rk.blockUpper_le A C B

/-- Reindexing commutes with `Matrix.map`. -/
theorem reindex_map (f : R →+* S) {n m p q : ℕ}
    (M : Matrix (Fin n ⊕ Fin p) (Fin m ⊕ Fin q) R) :
    (Matrix.reindex finSumFinEquiv finSumFinEquiv M).map f
      = Matrix.reindex finSumFinEquiv finSumFinEquiv (M.map f) := by
  ext i j
  simp [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.map_apply]

theorem blockDiag_map (f : R →+* S) {n m p q : ℕ}
    (A : Matrix (Fin n) (Fin m) R) (B : Matrix (Fin p) (Fin q) R) :
    (blockDiag A B).map f = blockDiag (A.map f) (B.map f) := by
  show (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A 0 0 B)).map f
    = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (A.map f) 0 0 (B.map f))
  simp only [reindex_map, Matrix.fromBlocks_map, Matrix.map_zero, RingHom.map_zero]

theorem blockUpper_map (f : R →+* S) {n m p q : ℕ}
    (A : Matrix (Fin n) (Fin m) R) (C : Matrix (Fin n) (Fin q) R) (B : Matrix (Fin p) (Fin q) R) :
    (blockUpper A C B).map f = blockUpper (A.map f) (C.map f) (B.map f) := by
  show (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A C 0 B)).map f
    = Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (A.map f) (C.map f) 0 (B.map f))
  simp only [reindex_map, Matrix.fromBlocks_map, Matrix.map_zero, RingHom.map_zero]

/-- Pull back a Sylvester rank function along a ring homomorphism. -/
def map (rk : SylvesterRankFunction S) (f : R →+* S) : SylvesterRankFunction R where
  toFun n m A := rk.toFun n m (A.map f)
  map_zero n m := by simp [Matrix.map_zero]
  map_one := by simp
  mul_le A B := by
    simpa [Matrix.map_mul] using rk.mul_le (A.map f) (B.map f)
  blockDiag_add A B := by
    rw [blockDiag_map]; exact rk.blockDiag_add _ _
  blockUpper_le A C B := by
    rw [blockUpper_map]; exact rk.blockUpper_le _ _ _

@[simp]
theorem map_apply (rk : SylvesterRankFunction S) (f : R →+* S)
    {n m : ℕ} (A : Matrix (Fin n) (Fin m) R) : (rk.map f).rank A = rk.rank (A.map f) := rfl

/-- A rank function is faithful if it does not vanish on a nonzero `1 × 1` matrix. -/
def Faithful (rk : SylvesterRankFunction R) : Prop :=
  ∀ x : R, rk.rank (!![x] : Matrix (Fin 1) (Fin 1) R) = 0 → x = 0

theorem Faithful.eq_zero_iff (rk : SylvesterRankFunction R) (h : rk.Faithful) (x : R) :
    rk.rank (!![x] : Matrix (Fin 1) (Fin 1) R) = 0 ↔ x = 0 :=
  ⟨h x, fun hx => by
    have h0 : (!![x] : Matrix (Fin 1) (Fin 1) R) = 0 := by rw [hx]; ext i j; simp
    rw [h0]
    simp⟩

end SylvesterRankFunction

end Work.ORVonNeumann
