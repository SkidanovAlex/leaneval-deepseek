/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The `Multiplicative ℤ`-action on a matrix ring, and the amplified skew Laurent ring

Let `R` be a ring with a `MulSemiringAction (Multiplicative ℤ) R` (the twist `τ` of the skew
Laurent polynomial ring `R[t^{±1}; τ]`).  The pointwise ("entrywise") action

  `m • A = A.map (fun a => m • a)`

on `Matrix (Fin k) (Fin k) R` is again a `MulSemiringAction`: it is additive and multiplicative
because `τ` is a ring homomorphism (`smul_mul'`), and unital (`smul_one`).

This instance is *not* provided by Mathlib (only the pointwise `DistribSMul` is), and it is what
makes the skew monoid algebra `M_k(R)[t^{±1}; τ]` — the "amplification" of `R[t^{±1}; τ]` — a
genuine skew Laurent polynomial ring.  The header of `skewMatrixRingEquiv` notes that the
isomorphism `M_k(R)[t^{±1}; τ] ≃+* M_k(R[t^{±1}; τ])` had to be built through the non-unital
universal property precisely because this instance was missing; with the instance available the
amplification argument of [JZLA20, §3] can be run as in the source.

## Main results

* `matrixMulSemiringAction` : the instance;
* `matrixSmul_eq_map` : `m • A = A.map (fun a => m • a)`, definitionally.
-/
import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.Defs

set_option autoImplicit false

universe u

namespace Work.ORHughesFree.NaturalExtension

open Matrix

/-- The pointwise action of `Multiplicative ℤ` (the twist `τ`) on a matrix ring. -/
instance matrixMulSemiringAction {R : Type u} [Ring R] [MulSemiringAction (Multiplicative ℤ) R]
    (k : ℕ) : MulSemiringAction (Multiplicative ℤ) (Matrix (Fin k) (Fin k) R) :=
  { (inferInstance : DistribSMul (Multiplicative ℤ) (Matrix (Fin k) (Fin k) R)) with
    one_smul := by
      intro A
      ext i j
      simp
    mul_smul := by
      intro m n A
      ext i j
      simp [mul_smul]
    smul_one := by
      intro m
      ext i j
      by_cases h : i = j
      · subst h; simp
      · simp [h]
    smul_mul := by
      intro m A B
      ext i j
      simp only [Matrix.smul_apply, Matrix.mul_apply]
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun l _ => smul_mul' m (A i l) (B l j) }

/-- The action on matrices is the entrywise one. -/
theorem matrixSmul_eq_map {R : Type u} [Ring R] [MulSemiringAction (Multiplicative ℤ) R]
    (k : ℕ) (m : Multiplicative ℤ) (A : Matrix (Fin k) (Fin k) R) :
    m • A = A.map (fun a => m • a) := rfl

/-- The `(i,j)` entry of the twist of a matrix. -/
theorem matrixSmul_apply {R : Type u} [Ring R] [MulSemiringAction (Multiplicative ℤ) R]
    (k : ℕ) (m : Multiplicative ℤ) (A : Matrix (Fin k) (Fin k) R) (i j : Fin k) :
    (m • A) i j = m • A i j := rfl

end Work.ORHughesFree.NaturalExtension
