/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Block description of the truncation defect `trunc i (A * B) - trunc i A * trunc i B`

The truncation `trunc i A` of a matrix over the skew Laurent polynomial ring
`U[t^{±1};τ] = SkewL U` is the "block Toeplitz" matrix of right multiplication by `A` on the
truncated module `(U[t;τ]/t^i U[t;τ])^n`.  Its entries are

`trunc i A (q, r) (j, u) = (t^r) • A_{u - r}_{q j}`,

where `q` is a row block, `r ∈ [0,i)` the row degree, `j` a column block and `u ∈ [0,i)` the
column degree (see `trunc_apply'`).

The product `trunc i A * trunc i B` is obtained by summing over the intermediate *degree*
`u ∈ [0,i)`, while the truncation `trunc i (A * B)` of the product corresponds to summing over
*all* intermediate degrees `u ∈ ℤ`.  Hence the defect

`trunc i (A*B) - trunc i A * trunc i B`

is the sum of the "row blocks" `truncBlkRow A i u * truncBlkCol B i u` over the intermediate
degrees `u` that are *not* in `[0,i)`.  There are two kinds of these:

* `u < 0`: this forces the row degree `r` to satisfy `r < lowerDeg A`, so the corresponding term
  lives on the `(n * lowerDeg A)` "low" rows;
* `u ≥ i`: this forces the column degree `s` to satisfy `s + lowerDeg B ≥ i`, so the corresponding
  term lives on the `(k * lowerDeg B)` "high" columns.

Consequently the defect has rank at most `n * lowerDeg A + k * lowerDeg B`, which is the content
of `rk_trunc_mul_sub_le`.

This file collects the definitions; the lemmas about them live in sibling modules.
-/
import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.Defs
import Submission.Work.ORHughesFree.MatrixBlocks.flattenBlocks_mul

set_option autoImplicit false

universe u

namespace Work.ORHughesFree.NaturalExtension

open Matrix

variable {U : Type u} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]

/-- The "row block at intermediate degree `u`" of the truncation.  Its `(q, j)` entry is the
`u`-th coefficient of `A`, twisted by `t^{q.modNat}`; equivalently
`truncBlkRow A i u q j = trunc i A q (finProdFinEquiv (j, u))` for `0 ≤ u < i`. -/
def truncBlkRow {n m : ℕ} (A : Matrix (Fin n) (Fin m) (SkewL U)) (i : ℕ) (u : ℤ) :
    Matrix (Fin (n * i)) (Fin m) U :=
  fun q j => (Multiplicative.ofAdd ((q.modNat : ℤ))) •
    (coeffMat A (u - (q.modNat : ℤ)) q.divNat j)

/-- The "column block at intermediate degree `u`" of the truncation.  Its `(j, p)` entry is the
coefficient of `B` at degree `p.modNat - u`, twisted by `t^u`; equivalently
`truncBlkCol B i u j p = trunc i B (finProdFinEquiv (j, u)) p` for `0 ≤ u < i`. -/
def truncBlkCol {m k : ℕ} (B : Matrix (Fin m) (Fin k) (SkewL U)) (i : ℕ) (u : ℤ) :
    Matrix (Fin m) (Fin (k * i)) U :=
  fun j p => (Multiplicative.ofAdd u) • (coeffMat B ((p.modNat : ℤ) - u) j p.divNat)

/-- The finite set of intermediate degrees that can possibly contribute to the defect: it is the
interval `[-lowerDeg A, i - 1 + lowerDeg B]`. -/
noncomputable def defectRange {n m k : ℕ} (A : Matrix (Fin n) (Fin m) (SkewL U))
    (B : Matrix (Fin m) (Fin k) (SkewL U)) (i : ℕ) : Finset ℤ :=
  Finset.Icc (-(lowerDeg A : ℤ)) (((i : ℤ) - 1) + (lowerDeg B : ℤ))

/-- The intermediate degrees in `[0, i)`, as a finset of integers. -/
noncomputable def truncRange (i : ℕ) : Finset ℤ :=
  (Finset.univ : Finset (Fin i)).image (fun v : Fin i => ((v : ℕ) : ℤ))

/-- The intermediate degrees that contribute to the *negative* boundary term of the defect:
the degrees `< 0` inside `defectRange`. -/
noncomputable def negRange {n m k : ℕ} (A : Matrix (Fin n) (Fin m) (SkewL U))
    (B : Matrix (Fin m) (Fin k) (SkewL U)) (i : ℕ) : Finset ℤ :=
  (defectRange A B i).filter fun u => u < 0

/-- The intermediate degrees that contribute to the *positive* boundary term of the defect:
the degrees `≥ i` inside `defectRange`. -/
noncomputable def posRange {n m k : ℕ} (A : Matrix (Fin n) (Fin m) (SkewL U))
    (B : Matrix (Fin m) (Fin k) (SkewL U)) (i : ℕ) : Finset ℤ :=
  (defectRange A B i).filter fun u => (i : ℤ) ≤ u

/-- The "low rows" of `Fin (n * i)`: the row blocks whose degree is `< a`.  Its image is exactly
`{q : Fin (n*i) | ((q.modNat : ℕ)) < a}` and it has domain `Fin (n * min a i)`. -/
def lowRowEmbed (n a i : ℕ) : Fin (n * min a i) → Fin (n * i) :=
  fun k =>
    finProdFinEquiv
      (k.divNat,
        ⟨(k.modNat : ℕ), lt_of_lt_of_le k.modNat.isLt (min_le_right a i)⟩)

/-- The "high columns" of `Fin (k * i)`: the column blocks whose degree `s` satisfies
`i ≤ b + s`.  Its image is exactly `{p : Fin (k*i) | i ≤ b + ((p.modNat : ℕ))}` and it has
domain `Fin (k * min b i)`. -/
def highColEmbed (k b i : ℕ) : Fin (k * min b i) → Fin (k * i) :=
  fun l =>
    finProdFinEquiv
      (l.divNat,
        ⟨(i - min b i) + (l.modNat : ℕ),
          by
            calc (i - min b i) + (l.modNat : ℕ) < (i - min b i) + min b i :=
                  Nat.add_lt_add_left l.modNat.isLt _
              _ = i := Nat.sub_add_cancel (min_le_right b i)⟩)

end Work.ORHughesFree.NaturalExtension
