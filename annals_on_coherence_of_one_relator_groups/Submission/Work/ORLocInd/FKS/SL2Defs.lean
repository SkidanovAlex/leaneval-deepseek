/-
# Ping-pong matrices in `SL(2, ℤ)` and their ping-pong sets

This file sets up the two parabolic matrices

* `Amat p = !![[1, p], [0, 1]]` and `Bmat p = !![[1, 0], [p, 1]]`

of `SL(2, ℤ)`, together with their conjugates `gmat p j = A ^ j * B * A ^ (-j)`, which are parabolic
with cusp `p * j`, and the ping-pong sets `pset p j` (the open unit disc around the cusp `p * j`
inside the upper half plane).

The key fact, proved in `SL2PingPong.lean`, is that `(gmat p j) ^ k` acts on `ℍ` by

  `z ↦ (z - p*j) / (p*k*(z - p*j) + 1) + p*j`,

so that `gmat p j ^ k` maps the complement of `pset p j` into `pset p j` for every `k ≠ 0`; the
`pset p j` are pairwise disjoint and admit a common exterior point.  The ping-pong lemma
(`PingPong.lean`) then shows that the elements `gmat p j` (`j : ℕ`) freely generate a free group
inside `SL(2, ℤ)`.
-/
import Mathlib

namespace Work.ORLocInd.FKS

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane
open scoped MatrixGroups

/-- `!![1, p; 0, 1]` as an element of `SL(2, ℤ)`. -/
def Amat (p : ℕ) : SL(2, ℤ) := ⟨!![(1 : ℤ), (p : ℤ); 0, 1], by simp [Matrix.det_fin_two]⟩

/-- `!![1, 0; p, 1]` as an element of `SL(2, ℤ)`. -/
def Bmat (p : ℕ) : SL(2, ℤ) := ⟨!![1, 0; (p : ℤ), 1], by simp [Matrix.det_fin_two]⟩

/-- The conjugate `A ^ j * B * (A ^ j)⁻¹` of `Bmat p`; it is parabolic with cusp `p * j`. -/
def gmat (p j : ℕ) : SL(2, ℤ) := Amat p ^ (j : ℤ) * Bmat p * (Amat p ^ (j : ℤ))⁻¹

/-- The ping-pong set of `gmat p j`: the open unit disc of `ℍ` centred at the cusp `p * j`. -/
def pset (p j : ℕ) : Set ℍ := {z | ‖(z : ℂ) - (p * j : ℂ)‖ < 1}

@[simp] lemma Amat_zero_zero (p : ℕ) : (Amat p) 0 0 = 1 := rfl
@[simp] lemma Amat_zero_one (p : ℕ) : (Amat p) 0 1 = (p : ℤ) := rfl
@[simp] lemma Amat_one_zero (p : ℕ) : (Amat p) 1 0 = 0 := rfl
@[simp] lemma Amat_one_one (p : ℕ) : (Amat p) 1 1 = 1 := rfl
@[simp] lemma Bmat_zero_zero (p : ℕ) : (Bmat p) 0 0 = 1 := rfl
@[simp] lemma Bmat_zero_one (p : ℕ) : (Bmat p) 0 1 = 0 := rfl
@[simp] lemma Bmat_one_zero (p : ℕ) : (Bmat p) 1 0 = (p : ℤ) := rfl
@[simp] lemma Bmat_one_one (p : ℕ) : (Bmat p) 1 1 = 1 := rfl

end Work.ORLocInd.FKS
