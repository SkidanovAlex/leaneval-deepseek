/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Flattening computations for the amplification argument

The amplification argument of [JZLA20, §3] compares the skew Laurent ring `R[t^{±1}; τ]` with its
`k`-fold amplification `M_k(R)[t^{±1}; τ]` (with τ acting entrywise, see
`matrixMulSemiringAction`).  The comparison is through the isomorphism
`M_k(R)[t^{±1}; τ] ≃+* M_k(R[t^{±1}; τ])` (`skewMatrixRingEquiv`) and the block flattening
`flattenBlocks : M_{a×b}(M_k(R)) → M_{ak × bk}(R)`.

For the natural-extension axioms of the *amplified* rank function one needs to know what the
flattening does to the two defining shapes:

* `flattenBlocks_map_single` : a constant block matrix (entries lifted to `M_k(R[t^{±1};τ])` by
  taking constant coefficients) flattens to the constant lift of the flattened matrix — this is
  the extension axiom `(a)`;
* `flattenBlocks_one` : the identity block matrix flattens to the identity;
* `flattenBlocks_diagonal_diagonal` : the amplified variable `t`, i.e. the diagonal matrix
  `diag(diag(skewLaurentT))`, flattens to `diag(skewLaurentT)` — the input needed for the
  `1 + C t` axiom `(b)`.

Together with `flattenBlocks_mul` these give
`flattenBlocks (1 + C · diag(diag(t))) = 1 + (flattenBlocks C) · diag(t)`, which turns the
amplified `1 + C t` into a polynomial `1 + A t` with `A` over `R`, so that
`rank_one_add_polyT` applies to the amplified rank function.
-/
import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension
import Submission.Work.ORHughesFree.NaturalExtension.Defs
import Submission.Work.ORHughesFree.MatrixBlocks
import Submission.Work.ORHughesFree.MatrixBlocks.flattenBlocks_mul
import Submission.Work.ORHughesFree.NaturalExtension.matrixMulSemiringAction

set_option autoImplicit false

universe u

namespace Work.ORHughesFree.NaturalExtension

open Matrix Work.ORHughesFree
open Work.ORHughesFree.MatrixBlocks

variable {R : Type u} [Ring R] [MulSemiringAction (Multiplicative ℤ) R]

omit [MulSemiringAction (Multiplicative ℤ) R] in
/-- **Flattening a constant block matrix.**  If the entries of a `a × b` block matrix over
`M_k(R)` are lifted to `M_k(R[t^{±1};τ])` by taking constant coefficients, the flattening is the
constant lift of the flattening. -/
theorem flattenBlocks_map_single {a b k : ℕ}
    (X : Matrix (Fin a) (Fin b) (Matrix (Fin k) (Fin k) R)) :
    flattenBlocks (X.map (fun A => A.map (SkewMonoidAlgebra.single (1 : Multiplicative ℤ)))) =
      (flattenBlocks X).map (SkewMonoidAlgebra.single (1 : Multiplicative ℤ)) := by
  ext i j
  simp [flattenBlocks, Matrix.map_apply]

omit [MulSemiringAction (Multiplicative ℤ) R] in
/-- The flattening of the identity block matrix is the identity. -/
theorem flattenBlocks_one {a k : ℕ} :
    flattenBlocks (1 : Matrix (Fin a) (Fin a) (Matrix (Fin k) (Fin k) R)) =
      (1 : Matrix (Fin (a * k)) (Fin (a * k)) R) := by
  ext i j
  simp only [flattenBlocks, Matrix.one_apply]
  by_cases h : i = j
  · subst h
    rw [if_pos rfl, if_pos rfl]
    simp
  · rw [if_neg h]
    by_cases h1 : (finProdFinEquiv.symm i).1 = (finProdFinEquiv.symm j).1
    · by_cases h2 : (finProdFinEquiv.symm i).2 = (finProdFinEquiv.symm j).2
      · exact absurd ((finProdFinEquiv (m := a) (n := k)).symm.injective
          (Prod.ext_iff.mpr ⟨h1, h2⟩)) h
      · rw [if_pos h1, Matrix.one_apply_ne h2]
    · rw [if_neg h1, Matrix.zero_apply]

omit [MulSemiringAction (Multiplicative ℤ) R] in
/-- **The diagonal matrix flattens to the diagonal matrix.**  At block size `a`, the diagonal block
matrix whose diagonal entries are the diagonal `k × k` matrices with constant entry `x` flattens to
the diagonal `(a*k) × (a*k)` matrix with entry `x`. -/
theorem flattenBlocks_diagonal_diagonal {a k : ℕ} (x : R) :
    flattenBlocks (Matrix.diagonal (fun _ : Fin a => Matrix.diagonal (fun _ : Fin k => x))) =
      Matrix.diagonal (fun _ : Fin (a * k) => x) := by
  ext i j
  simp only [flattenBlocks, Matrix.diagonal_apply]
  by_cases h : i = j
  · subst h
    rw [if_pos rfl, if_pos rfl]
    simp
  · rw [if_neg h]
    by_cases h1 : (finProdFinEquiv.symm i).1 = (finProdFinEquiv.symm j).1
    · by_cases h2 : (finProdFinEquiv.symm i).2 = (finProdFinEquiv.symm j).2
      · exact absurd ((finProdFinEquiv (m := a) (n := k)).symm.injective
          (Prod.ext_iff.mpr ⟨h1, h2⟩)) h
      · rw [if_pos h1, show Matrix.diagonal (fun _ : Fin k => x)
            (finProdFinEquiv.symm i).2 (finProdFinEquiv.symm j).2 = 0 from
          Matrix.diagonal_apply_ne _ h2]
    · rw [if_neg h1]
      simp

omit [MulSemiringAction (Multiplicative ℤ) R] in
/-- The flattening is additive (it is an entrywise operation). -/
theorem flattenBlocks_add {a b k : ℕ}
    (A B : Matrix (Fin a) (Fin b) (Matrix (Fin k) (Fin k) R)) :
    flattenBlocks (A + B) = flattenBlocks A + flattenBlocks B := by
  ext i j
  simp [flattenBlocks, Matrix.add_apply]

/-- **Flattening the amplified `1 + C·diag(t)`.**  With `t` denoting `diag(skewLaurentT)` in
`M_k(S)`, the flattening of `1 + C·diag(diag(t))` is `1 + (flattenBlocks C)·diag(skewLaurentT)`:
the amplified `1 + C t` becomes a polynomial `1 + A t` with `A` over `R`, so that
`rank_one_add_polyT` applies to the amplified rank function. -/
theorem flattenBlocks_one_add_mul_diagonal {a k : ℕ}
    (C : Matrix (Fin a) (Fin a) (Matrix (Fin k) (Fin k) (SkewL R))) :
    flattenBlocks ((1 : Matrix (Fin a) (Fin a) (Matrix (Fin k) (Fin k) (SkewL R))) +
        C * Matrix.diagonal (fun _ : Fin a =>
          Matrix.diagonal (fun _ : Fin k => (skewLaurentT : SkewL R)))) =
      (1 : Matrix (Fin (a * k)) (Fin (a * k)) (SkewL R)) +
        (flattenBlocks C) * Matrix.diagonal (fun _ : Fin (a * k) => (skewLaurentT : SkewL R)) := by
  rw [flattenBlocks_add, flattenBlocks_one, flattenBlocks_mul,
    flattenBlocks_diagonal_diagonal (skewLaurentT : SkewL R)]

end Work.ORHughesFree.NaturalExtension
