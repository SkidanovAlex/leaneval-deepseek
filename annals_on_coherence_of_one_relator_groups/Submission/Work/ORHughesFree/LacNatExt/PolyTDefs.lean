/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Definitions for the linearization of `1 + B·diag(t)`

This file sets up the objects used in the proof of `lacrank_one_add_polyT`:  for a matrix `B` over
`R[t^{±1};τ]` whose coefficients all have non-negative degree, the matrix `1 + B * diag(t)` (whose
`(i,j)` entry is `δ_{ij} + B_{ij}·t`) is shown to be unit-equivalent to the "companion" matrix
`lacComp`, a matrix of the form `C + A·diag(t)` with `C`, `A` constant, whose rank is therefore known
from the hypothesis on constant matrices.

Writing `B = ∑_k C_k t^k` with `C_k = coeffMat B k` (all coefficients of negative degree vanish),
the matrix `1 + B·diag(t)` equals `1 + ∑_k C_k t^{k+1}`, which is the Schur complement of the
`(1+d)`-block companion matrix
`[[1 + C_0 t, C_1 t, …, C_d t], [t·1, -1, 0 …], [0, t·1, -1, …], …]`
with respect to the trailing block `W = -1 + t·N` (`N` the downward shift), the classical
linearization of a matrix polynomial.

The index convention is the one of `Work.ORHughesFree.flattenBlocks`:  `q : Fin (d*n)` stands for
the pair `(q.divNat : Fin d, q.modNat : Fin n)` (block index, inner index).
-/
import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension
import Submission.Work.ORHughesFree.NaturalExtension.Defs
import Submission.Work.ORHughesFree.NaturalExtension.EltDeg
import Submission.Work.ORHughesFree.SylvesterRank
import Submission.Work.ORHughesFree.MatrixBlocks
import Submission.Work.ORHughesFree.MatrixBlocks.flattenBlocks_mul

set_option autoImplicit false

namespace Work.ORHughesFree.NaturalExtension

open Matrix

universe u

variable {R : Type u} [Ring R] [MulSemiringAction (Multiplicative ℤ) R]

noncomputable section

/-! ## Elementary coefficient bookkeeping -/

/-- The constant embedding `R → SkewL R`, `r ↦ r·1`. -/
def laccstElt (r : R) : SkewL R := SkewMonoidAlgebra.single 1 r

/-- The map `r ↦ r·t` (right multiplication by the variable `t`). -/
def lacmulTElt (r : R) : SkewL R := SkewMonoidAlgebra.single (Multiplicative.ofAdd 1) r

/-- The matrix whose `(i,j)` entry is `C i j * t`. -/
def lacAtC {n : ℕ} (C : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) (SkewL R) :=
  C.map lacmulTElt

/-- The scalar matrix with `t` on the diagonal. -/
def lacTmat (n : ℕ) : Matrix (Fin n) (Fin n) (SkewL R) := Matrix.diagonal (fun _ => skewLaurentT)

/-- The scalar matrix with `t^k` on the diagonal. -/
def lacTpow (n k : ℕ) : Matrix (Fin n) (Fin n) (SkewL R) :=
  Matrix.diagonal (fun _ => skewLaurentT ^ k)

/-- The `k`-th coefficient matrix of `B`. -/
def lacCcoef {n : ℕ} (B : Matrix (Fin n) (Fin n) (SkewL R)) (k : ℕ) : Matrix (Fin n) (Fin n) R :=
  coeffMat B (k : ℤ)

/-- The `D`-term linearization target `1 + ∑_{k<D} C_k t^{k+1}`. -/
def lacMDiag {n : ℕ} (B : Matrix (Fin n) (Fin n) (SkewL R)) (D : ℕ) :
    Matrix (Fin n) (Fin n) (SkewL R) :=
  1 + ∑ k : Fin D, lacAtC (lacCcoef B (k : ℕ)) * Matrix.diagonal (fun _ => skewLaurentT ^ (k : ℕ))

/-! ## The blocks of the companion -/

/-- The `(0,0)` block `1 + C_0 t` of the companion. -/
def lacXB {n : ℕ} (B : Matrix (Fin n) (Fin n) (SkewL R)) : Matrix (Fin n) (Fin n) (SkewL R) :=
  onePlusAt n (lacCcoef B 0)

/-- The block row `(C_1 t, …, C_d t)` of the companion. -/
def lacYB {n : ℕ} (B : Matrix (Fin n) (Fin n) (SkewL R)) (d : ℕ) :
    Matrix (Fin n) (Fin (d * n)) (SkewL R) :=
  fun p q => lacAtC (lacCcoef B ((q.divNat : ℕ) + 1)) p q.modNat

/-- The block column `(t·1, 0, …, 0)` of the companion. -/
def lacZB (d n : ℕ) : Matrix (Fin (d * n)) (Fin n) (SkewL R) :=
  fun q p => if (q.divNat : ℕ) = 0 then (lacTmat n) q.modNat p else 0

/-- The trailing block `-1 + t·N` of the companion (flattened). -/
def lacWB (d n : ℕ) : Matrix (Fin (d * n)) (Fin (d * n)) (SkewL R) :=
  fun q q' => show SkewL R from
    (if (q.divNat : ℕ) = (q'.divNat : ℕ) then
        (if q.modNat = q'.modNat then (-1 : SkewL R) else 0) else 0) +
      (if (q.divNat : ℕ) = (q'.divNat : ℕ) + 1 then
        (if q.modNat = q'.modNat then skewLaurentT else 0) else 0)

/-- The inverse `-∑_k t^k N^k` of `lacWB` (flattened). -/
def lacWiB (d n : ℕ) : Matrix (Fin (d * n)) (Fin (d * n)) (SkewL R) :=
  fun q q' => show SkewL R from
    if (q'.divNat : ℕ) ≤ (q.divNat : ℕ) then
      (if q.modNat = q'.modNat then -(skewLaurentT ^ ((q.divNat : ℕ) - (q'.divNat : ℕ))) else 0)
    else 0

/-! ## The companion matrix -/

/-- The companion matrix, as a matrix indexed by `Fin (n + d * n)`. -/
def lacComp {n : ℕ} (B : Matrix (Fin n) (Fin n) (SkewL R)) (d : ℕ) :
    Matrix (Fin (n + d * n)) (Fin (n + d * n)) (SkewL R) :=
  (fromBlocks (lacXB B) (lacYB B d) (lacZB d n) (lacWB (R := R) d n)).submatrix finSumFinEquiv.symm
    finSumFinEquiv.symm

/-! ## The constant decomposition of the companion -/

/-- The constant part `-1` of the trailing block. -/
def lacWBC (d n : ℕ) : Matrix (Fin (d * n)) (Fin (d * n)) R :=
  fun q q' => if (q.divNat : ℕ) = (q'.divNat : ℕ) then
    (if q.modNat = q'.modNat then (-1 : R) else 0) else 0

/-- The constant part `C` of the companion: `C = 1 ⊕ (-1)`. -/
def lacCmat (d n : ℕ) : Matrix (Fin (n + d * n)) (Fin (n + d * n)) R :=
  (fromBlocks (1 : Matrix (Fin n) (Fin n) R) 0 0 (lacWBC d n)).submatrix finSumFinEquiv.symm
    finSumFinEquiv.symm

/-- The constant matrix `C_1` of the companion block row. -/
def lacYBC {n : ℕ} (B : Matrix (Fin n) (Fin n) (SkewL R)) (d : ℕ) :
    Matrix (Fin n) (Fin (d * n)) R :=
  fun p q => (lacCcoef B ((q.divNat : ℕ) + 1)) p q.modNat

/-- The constant matrix `(1, 0, …, 0)` of the companion block column. -/
def lacZBC (d n : ℕ) : Matrix (Fin (d * n)) (Fin n) R :=
  fun q p => if (q.divNat : ℕ) = 0 then (if q.modNat = p then 1 else 0) else 0

/-- The constant matrix of the `t`-part of the trailing block (`N`, the downward shift). -/
def lacWTC (d n : ℕ) : Matrix (Fin (d * n)) (Fin (d * n)) R :=
  fun q q' => if (q.divNat : ℕ) = (q'.divNat : ℕ) + 1 then
    (if q.modNat = q'.modNat then 1 else 0) else 0

/-- The matrix `A` with `lacComp = lacCmat·1 + A·diag(t)`. -/
def lacAmat {n : ℕ} (B : Matrix (Fin n) (Fin n) (SkewL R)) (d : ℕ) :
    Matrix (Fin (n + d * n)) (Fin (n + d * n)) R :=
  (fromBlocks (lacCcoef B 0) (lacYBC B d) (lacZBC d n) (lacWTC d n)).submatrix finSumFinEquiv.symm
    finSumFinEquiv.symm

end

end Work.ORHughesFree.NaturalExtension
