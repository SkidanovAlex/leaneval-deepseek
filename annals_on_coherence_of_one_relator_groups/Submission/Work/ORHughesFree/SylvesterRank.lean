/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Sylvester matrix rank functions

Sets up the notion of *Sylvester matrix rank function* on a ring, in the sense of Malcolmson,
following [JZLA20, §2.4] (A. Jaikin-Zapirain and D. López-Álvarez, *The strong Atiyah and Lü\textbackslash{}ck
approximation conjectures for one-relator groups*, arXiv:1810.12135).

A Sylvester matrix rank function `rk` on a ring `R` assigns a non-negative real number to every
matrix over `R` and satisfies

* `rk 0 = 0` and `rk 1 = 1`;
* `rk (A * B) ≤ min (rk A) (rk B)`;
* `rk (A ⊕ B) = rk A + rk B`;
* `rk [[A, C], [0, B]] ≥ rk A + rk B`.

We work with matrices indexed by `Fin n`, so that block constructions have the expected shape.
-/
import Mathlib

set_option autoImplicit false

universe u

namespace Work.ORHughesFree

open Matrix

variable {R : Type u}

/-- The block diagonal matrix `diag(A, B)` with index types normalized to `Fin`. -/
def blockDiagFin [Zero R] {n m p q : ℕ}
    (A : Matrix (Fin n) (Fin m) R) (B : Matrix (Fin p) (Fin q) R) :
    Matrix (Fin (n + p)) (Fin (m + q)) R :=
  (Matrix.fromBlocks A 0 0 B).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

/-- The block upper triangular matrix `[[A, C], [0, B]]` with index types normalized to `Fin`. -/
def blockUpperFin [Zero R] {n m p q : ℕ}
    (A : Matrix (Fin n) (Fin m) R) (B : Matrix (Fin p) (Fin q) R)
    (C : Matrix (Fin n) (Fin q) R) :
    Matrix (Fin (n + p)) (Fin (m + q)) R :=
  (Matrix.fromBlocks A C 0 B).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

theorem blockDiagFin_map {R S : Type*} [Semiring R] [Semiring S] {n m p q : ℕ}
    (φ : R →+* S) (A : Matrix (Fin n) (Fin m) R) (B : Matrix (Fin p) (Fin q) R) :
    (blockDiagFin A B).map φ = blockDiagFin (A.map φ) (B.map φ) := by
  simp only [blockDiagFin]
  rw [← Matrix.submatrix_map, Matrix.fromBlocks_map, Matrix.map_zero ⇑φ φ.map_zero,
    Matrix.map_zero ⇑φ φ.map_zero]

theorem blockUpperFin_map {R S : Type*} [Semiring R] [Semiring S] {n m p q : ℕ}
    (φ : R →+* S) (A : Matrix (Fin n) (Fin m) R) (B : Matrix (Fin p) (Fin q) R)
    (C : Matrix (Fin n) (Fin q) R) :
    (blockUpperFin A B C).map φ = blockUpperFin (A.map φ) (B.map φ) (C.map φ) := by
  simp only [blockUpperFin]
  rw [← Matrix.submatrix_map, Matrix.fromBlocks_map, Matrix.map_zero ⇑φ φ.map_zero]

/-- The `1 × 1` matrix with the single entry `a`. -/
def oneByOne (a : R) : Matrix (Fin 1) (Fin 1) R := fun _ _ => a

/-- A **Sylvester matrix rank function** on a ring `R` ([JZLA20, §2.4]). -/
structure SylvesterRank (R : Type u) [Ring R] where
  /-- The rank of a matrix. -/
  rk : (n m : ℕ) → Matrix (Fin n) (Fin m) R → ℝ
  /-- Rank functions take non-negative values. -/
  rk_nonneg : ∀ (n m : ℕ) (A : Matrix (Fin n) (Fin m) R), 0 ≤ rk n m A
  /-- (SMat1) -/
  rk_zero : ∀ n m, rk n m 0 = 0
  /-- (SMat1) -/
  rk_one : rk 1 1 (1 : Matrix (Fin 1) (Fin 1) R) = 1
  /-- (SMat2) -/
  rk_mul_le_left : ∀ {n m k : ℕ} (A : Matrix (Fin n) (Fin m) R)
    (B : Matrix (Fin m) (Fin k) R), rk n k (A * B) ≤ rk n m A
  /-- (SMat2) -/
  rk_mul_le_right : ∀ {n m k : ℕ} (A : Matrix (Fin n) (Fin m) R)
    (B : Matrix (Fin m) (Fin k) R), rk n k (A * B) ≤ rk m k B
  /-- (SMat3) -/
  rk_blockDiag : ∀ {n m p q : ℕ} (A : Matrix (Fin n) (Fin m) R)
    (B : Matrix (Fin p) (Fin q) R),
    rk (n + p) (m + q) (blockDiagFin A B) = rk n m A + rk p q B
  /-- (SMat4) -/
  rk_blockUpper : ∀ {n m p q : ℕ} (A : Matrix (Fin n) (Fin m) R)
    (B : Matrix (Fin p) (Fin q) R) (C : Matrix (Fin n) (Fin q) R),
    rk n m A + rk p q B ≤ rk (n + p) (m + q) (blockUpperFin A B C)

namespace SylvesterRank

variable [Ring R] (rk : SylvesterRank R)

theorem nonneg {n m : ℕ} (A : Matrix (Fin n) (Fin m) R) : 0 ≤ rk.rk n m A :=
  rk.rk_nonneg n m A

/-- Rank is invariant under multiplying by a matrix admitting a left inverse. -/
theorem rk_eq_of_left_inverse_mul {n m k : ℕ} (X : Matrix (Fin n) (Fin m) R)
    (X' : Matrix (Fin m) (Fin n) R) (hX : X' * X = 1) (A : Matrix (Fin m) (Fin k) R) :
    rk.rk n k (X * A) = rk.rk m k A := by
  refine le_antisymm (rk.rk_mul_le_right X A) ?_
  have h : X' * (X * A) = A := by rw [← Matrix.mul_assoc, hX, Matrix.one_mul]
  calc rk.rk m k A = rk.rk m k (X' * (X * A)) := by rw [h]
    _ ≤ rk.rk n k (X * A) := rk.rk_mul_le_right X' (X * A)

/-- Rank is invariant under multiplying on the right by a matrix admitting a right inverse. -/
theorem rk_eq_of_mul_right_inverse {n m k : ℕ} (A : Matrix (Fin n) (Fin m) R)
    (Y : Matrix (Fin m) (Fin k) R) (Y' : Matrix (Fin k) (Fin m) R) (hY : Y * Y' = 1) :
    rk.rk n k (A * Y) = rk.rk n m A := by
  refine le_antisymm (rk.rk_mul_le_left A Y) ?_
  have h : A * Y * Y' = A := by rw [Matrix.mul_assoc, hY, Matrix.mul_one]
  calc rk.rk n m A = rk.rk n m (A * Y * Y') := by rw [h]
    _ ≤ rk.rk n k (A * Y) := rk.rk_mul_le_left (A * Y) Y'

end SylvesterRank

end Work.ORHughesFree
