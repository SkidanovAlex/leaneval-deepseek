/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The truncation construction for the natural extension

This file sets up the auxiliary notions used in the construction of the natural extension of a
Sylvester rank function `rk` on a ring `U` to the skew Laurent polynomial ring
`U[t^{±1};τ] = SkewMonoidAlgebra U (Multiplicative ℤ)`.

The construction is the "truncation" or "block Toeplitz" construction: for a matrix `A` over
`U[t^{±1};τ]` and a positive integer `i`, we consider the matrix `trunc i A` over `U` of the
`U`-linear map "right multiplication by `A`" on the truncated module
`(U[t;τ]/t^iU[t;τ])ⁿ`, expressed in the basis `{t^r e_p}`.  Concretely, writing
`A = ∑_k A_k t^k` with coefficient matrices `A_k`, the `(q,s),(p,r)` entry of `trunc i A` is the
`(p,q)` entry of `(t^r) • A_{s-r}`.

The rank function on `U[t^{±1};τ]` is then obtained as an ultralimit of the ranks of these
truncations divided by `i`.

## Main definitions

* `SkewL U` : the skew Laurent polynomial ring `U[t^{±1};τ]`;
* `coeffElt`, `coeffMat` : coefficient extraction;
* `lowerDeg`, `upperDeg` : degree bounds for matrices;
* `toep`, `trunc` : the truncation ("block Toeplitz") matrix;
* `diagInner`, `blockDiagFam` : block diagonal matrices with blocks indexed by an inner or an
  outer index, together with the identification used for constant matrices;
* `blim` : the ultralimit of a real-valued sequence along an ultrafilter.
-/
import Mathlib
import Submission.Work.ORHughesFree.SylvesterRank
import Submission.Work.ORHughesFree.MatrixBlocks.flattenBlocks_mul

set_option autoImplicit false

universe u

namespace Work.ORHughesFree.NaturalExtension

open Matrix

/-- The skew Laurent polynomial ring `U[t^{±1};τ]`, where the twist is encoded in a
`MulSemiringAction (Multiplicative ℤ) U`. -/
abbrev SkewL (U : Type u) [Zero U] := SkewMonoidAlgebra U (Multiplicative ℤ)

section Coeff

variable {U : Type u} [Zero U]

/-- The `k`-th coefficient of an element of `U[t^{±1};τ]`. -/
def coeffElt (a : SkewL U) (k : ℤ) : U :=
  (SkewMonoidAlgebra.coeff a) (Multiplicative.ofAdd k)

/-- The matrix of `k`-th coefficients of a matrix over `U[t^{±1};τ]`. -/
def coeffMat {n m : ℕ} (A : Matrix (Fin n) (Fin m) (SkewL U)) (k : ℤ) :
    Matrix (Fin n) (Fin m) U :=
  A.map (fun a => coeffElt a k)

theorem coeffMat_apply {n m : ℕ} (A : Matrix (Fin n) (Fin m) (SkewL U)) (k : ℤ) (i : Fin n)
    (j : Fin m) : coeffMat A k i j = coeffElt (A i j) k := rfl

/-- A bound `d` such that all coefficients `A_k` of `A` with `k < -d` vanish. -/
def lowerDeg {n m : ℕ} (A : Matrix (Fin n) (Fin m) (SkewL U)) : ℕ :=
  Finset.univ.sup fun p : Fin n × Fin m =>
    (SkewMonoidAlgebra.coeff (A p.1 p.2)).support.sup fun g => Int.toNat (- (Multiplicative.toAdd g))

/-- A bound `d` such that all coefficients `A_k` of `A` with `k > d` vanish. -/
def upperDeg {n m : ℕ} (A : Matrix (Fin n) (Fin m) (SkewL U)) : ℕ :=
  Finset.univ.sup fun p : Fin n × Fin m =>
    (SkewMonoidAlgebra.coeff (A p.1 p.2)).support.sup fun g => Int.toNat (Multiplicative.toAdd g)

theorem coeffElt_eq_zero_of_lt_lowerDeg {n m : ℕ} (A : Matrix (Fin n) (Fin m) (SkewL U))
    (i : Fin n) (j : Fin m) {k : ℤ} (h : k < - (lowerDeg A : ℤ)) : coeffElt (A i j) k = 0 := by
  by_contra hk
  have hmem : Multiplicative.ofAdd k ∈ (SkewMonoidAlgebra.coeff (A i j)).support := by
    simpa [coeffElt] using hk
  have h1 : Int.toNat (-k) ≤
      (SkewMonoidAlgebra.coeff (A i j)).support.sup
        (fun g => Int.toNat (- (Multiplicative.toAdd g))) := by
    simpa using Finset.le_sup (f := fun g => Int.toNat (- (Multiplicative.toAdd g))) hmem
  have h2 : (SkewMonoidAlgebra.coeff (A i j)).support.sup
        (fun g => Int.toNat (- (Multiplicative.toAdd g))) ≤ lowerDeg A := by
    refine Finset.le_sup (f := fun p : Fin n × Fin m =>
      (SkewMonoidAlgebra.coeff (A p.1 p.2)).support.sup
        (fun g => Int.toNat (- (Multiplicative.toAdd g)))) (Finset.mem_univ (i, j))
  have h3 : Int.toNat (-k) ≤ lowerDeg A := le_trans h1 h2
  have h4 : -k ≤ (lowerDeg A : ℤ) := Int.toNat_le.mp h3
  omega

theorem coeffElt_eq_zero_of_gt_upperDeg {n m : ℕ} (A : Matrix (Fin n) (Fin m) (SkewL U))
    (i : Fin n) (j : Fin m) {k : ℤ} (h : (upperDeg A : ℤ) < k) : coeffElt (A i j) k = 0 := by
  by_contra hk
  have hmem : Multiplicative.ofAdd k ∈ (SkewMonoidAlgebra.coeff (A i j)).support := by
    simpa [coeffElt] using hk
  have h1 : Int.toNat k ≤
      (SkewMonoidAlgebra.coeff (A i j)).support.sup
        (fun g => Int.toNat (Multiplicative.toAdd g)) := by
    simpa using Finset.le_sup (f := fun g => Int.toNat (Multiplicative.toAdd g)) hmem
  have h2 : (SkewMonoidAlgebra.coeff (A i j)).support.sup
        (fun g => Int.toNat (Multiplicative.toAdd g)) ≤ upperDeg A := by
    refine Finset.le_sup (f := fun p : Fin n × Fin m =>
      (SkewMonoidAlgebra.coeff (A p.1 p.2)).support.sup
        (fun g => Int.toNat (Multiplicative.toAdd g))) (Finset.mem_univ (i, j))
  have h3 : Int.toNat k ≤ upperDeg A := le_trans h1 h2
  have h4 : k ≤ (upperDeg A : ℤ) := Int.toNat_le.mp h3
  omega

theorem coeffMat_eq_zero_of_lt_lowerDeg {n m : ℕ} (A : Matrix (Fin n) (Fin m) (SkewL U))
    {k : ℤ} (h : k < - (lowerDeg A : ℤ)) : coeffMat A k = 0 := by
  ext i j
  exact coeffElt_eq_zero_of_lt_lowerDeg A i j h

theorem coeffMat_eq_zero_of_gt_upperDeg {n m : ℕ} (A : Matrix (Fin n) (Fin m) (SkewL U))
    {k : ℤ} (h : (upperDeg A : ℤ) < k) : coeffMat A k = 0 := by
  ext i j
  exact coeffElt_eq_zero_of_gt_upperDeg A i j h

end Coeff

section Trunc

variable {U : Type u} [AddMonoid U] [SMulZeroClass (Multiplicative ℤ) U]

/-- The (block Toeplitz) matrix over `U` giving the matrix of "right multiplication by `A`" on the
truncated module `(U[t;τ]/t^iU[t;τ])ⁿ` with respect to the `U`-bases `{t^r}`: the entry at the
row `(q, r)` (block `q`, coefficient degree `r`) and column `(p, s)` is the `(q, p)` entry of
`(t^r) • A_{s-r}`.

Note the *order* of the factors: with this (row) convention the truncation is multiplicative up to
a boundary term, `trunc i (A * B) = trunc i A * trunc i B + E`, which is what the whole
construction relies on.  (The transposed convention would multiply the factors in the opposite
order, which is only correct when `U` is commutative.) -/
def toep {n m : ℕ} (i : ℕ) (A : Matrix (Fin n) (Fin m) (SkewL U)) :
    Matrix (Fin n × Fin i) (Fin m × Fin i) U :=
  fun p q => ((Multiplicative.ofAdd ((p.2 : ℤ))) • (coeffMat A ((q.2 : ℤ) - (p.2 : ℤ)))) p.1 q.1

/-- The truncation `trunc i A`, indexed by `Fin (n * i)` rows and `Fin (m * i)` columns. -/
def trunc {n m : ℕ} (i : ℕ) (A : Matrix (Fin n) (Fin m) (SkewL U)) :
    Matrix (Fin (n * i)) (Fin (m * i)) U :=
  Matrix.reindex (finProdFinEquiv (m := n) (n := i)) (finProdFinEquiv (m := m) (n := i))
    (toep i A)

theorem trunc_apply {n m : ℕ} (i : ℕ) (A : Matrix (Fin n) (Fin m) (SkewL U))
    (q : Fin (n * i)) (p : Fin (m * i)) :
    trunc i A q p =
      ((Multiplicative.ofAdd ((q.modNat : ℤ))) •
        (coeffMat A ((p.modNat : ℤ) - (q.modNat : ℤ)))) q.divNat p.divNat := by
  simp [trunc, toep, Matrix.reindex_apply]

theorem trunc_apply' {n m : ℕ} (i : ℕ) (A : Matrix (Fin n) (Fin m) (SkewL U))
    (q : Fin n) (r : Fin i) (p : Fin m) (s : Fin i) :
    trunc i A (finProdFinEquiv (q, r)) (finProdFinEquiv (p, s)) =
      ((Multiplicative.ofAdd (((r : ℕ) : ℤ))) • (coeffMat A (((s : ℕ) : ℤ) - ((r : ℕ) : ℤ)))) q p := by
  rw [trunc_apply]
  simp [Work.ORHughesFree.MatrixBlocks.finProdFinEquiv_fst,
    Work.ORHughesFree.MatrixBlocks.finProdFinEquiv_snd]

end Trunc

section ZeroMat

variable {U : Type u} [AddMonoid U] [SMulZeroClass (Multiplicative ℤ) U]

theorem coeffMat_zero {n m : ℕ} (k : ℤ) :
    coeffMat (0 : Matrix (Fin n) (Fin m) (SkewL U)) k = 0 := by
  ext i j
  simp [coeffMat, coeffElt]

theorem trunc_zero {n m : ℕ} (i : ℕ) :
    trunc i (0 : Matrix (Fin n) (Fin m) (SkewL U)) = 0 := by
  ext q p
  simp [trunc_apply, coeffMat_zero]

end ZeroMat

section Blocks

variable {U : Type u} [Zero U]

/-- A block diagonal matrix whose blocks are indexed by the *inner* index of a `Fin (a * k)`-type:
the entry at `(x, y)` is the `(x.divNat, y.divNat)` entry of `B x.modNat` when
`x.modNat = y.modNat`, and `0` otherwise. -/
def diagInner {a b k : ℕ} (B : Fin k → Matrix (Fin a) (Fin b) U) :
    Matrix (Fin (a * k)) (Fin (b * k)) U :=
  fun x y => if x.modNat = y.modNat then B x.modNat x.divNat y.divNat else 0

/-- A block diagonal matrix with blocks indexed by the *outer* index: for `x : Fin (k * a)` we
have `x.divNat : Fin k` and `x.modNat : Fin a`. -/
def blockDiagFam {a b k : ℕ} (B : Fin k → Matrix (Fin a) (Fin b) U) :
    Matrix (Fin (k * a)) (Fin (k * b)) U :=
  fun x y => if x.divNat = y.divNat then B x.divNat x.modNat y.modNat else 0

end Blocks

/-- The ultralimit of a real-valued sequence along an ultrafilter, given by the order-theoretic
formula `sup {r | {i | r ≤ f i} ∈ ω}`. -/
noncomputable def blim (ω : Ultrafilter ℕ) (f : ℕ → ℝ) : ℝ :=
  sSup {r : ℝ | {i | r ≤ f i} ∈ ω}

/-- There is an ultrafilter on `ℕ` containing all cofinite sets. -/
theorem exists_ultrafilter_le_atTop :
    ∃ ω : Ultrafilter ℕ, (ω : Filter ℕ) ≤ Filter.atTop :=
  Filter.exists_ultrafilter_le Filter.atTop

end Work.ORHughesFree.NaturalExtension
