/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The `(i,j)` entry of `∑_k C_k t · diag(t^k)`

The `k`-th summand of the linearization target `lacMDiag` is the product `C_k·t · diag(t^k)`, where
`C_k = lacCcoef B k` is a constant matrix.  Since the second factor is diagonal, its `(i,j)` entry is
`(C_k)_{ij}·t · t^k = (C_k)_{ij}·t^{k+1}`, i.e. the single term `single (ofAdd (k+1)) (C_k)_{ij}`.

This file records that computation entrywise.
-/
import Mathlib
import Submission.Work.ORHughesFree.LacNatExt.PolyTDefs

namespace Work.ORHughesFree.NaturalExtension

/-- The variable `t` raised to the `k`-th power is the single monomial `t^k = single (ofAdd k) 1`. -/
lemma lacskewLaurentT_pow_eq_single {R : Type*} [Ring R] [MulSemiringAction (Multiplicative ℤ) R]
    (k : ℕ) :
    (skewLaurentT : SkewL R) ^ k =
      SkewMonoidAlgebra.single (Multiplicative.ofAdd (k : ℤ)) (1 : R) := by
  induction k with
  | zero => simp [skewLaurentT]
  | succ n ih =>
    rw [pow_succ, ih, skewLaurentT, SkewMonoidAlgebra.single_mul_single, ← ofAdd_add]
    simp

/-- Multiplying a `t`-coefficient by `t^k` just shifts the exponent:
`single (ofAdd 1) r * t^k = single (ofAdd (k+1)) r`. -/
lemma lacsingle_ofAdd_one_mul_skewLaurentT_pow {R : Type*} [Ring R]
    [MulSemiringAction (Multiplicative ℤ) R] (r : R) (k : ℕ) :
    SkewMonoidAlgebra.single (Multiplicative.ofAdd (1 : ℤ)) r * (skewLaurentT : SkewL R) ^ k =
      SkewMonoidAlgebra.single (Multiplicative.ofAdd ((k : ℤ) + 1)) r := by
  rw [lacskewLaurentT_pow_eq_single, SkewMonoidAlgebra.single_mul_single]
  have h : Multiplicative.ofAdd (1 : ℤ) * Multiplicative.ofAdd (k : ℤ)
      = Multiplicative.ofAdd ((k : ℤ) + 1) := by
    rw [← ofAdd_add, add_comm]
  rw [h]
  simp

theorem lacsum_AtC_diag_apply {R : Type*} [Ring R] [MulSemiringAction (Multiplicative ℤ) R] {n : ℕ}
    (B : Matrix (Fin n) (Fin n) (SkewL R)) (d : ℕ) (i j : Fin n) :
    (∑ k : Fin (d + 1), lacAtC (lacCcoef B (k : ℕ)) *
        (Matrix.diagonal (fun _ => (skewLaurentT : SkewL R) ^ (k : ℕ)) :
          Matrix (Fin n) (Fin n) (SkewL R))) i j
      = ∑ k : Fin (d + 1),
          SkewMonoidAlgebra.single (Multiplicative.ofAdd ((k : ℤ) + 1)) ((lacCcoef B (k : ℕ)) i j) := by
  rw [Matrix.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_diagonal]
  simp only [lacAtC, Matrix.map_apply, lacmulTElt]
  exact lacsingle_ofAdd_one_mul_skewLaurentT_pow _ _

end Work.ORHughesFree.NaturalExtension
