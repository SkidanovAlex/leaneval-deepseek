/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Rank–nullity for Sylvester rank functions on von Neumann regular rings

Let `M : Matrix (Fin n) (Fin m) R` and `K : Matrix (Fin m) (Fin q) R` over a von Neumann
regular ring `R`, with `M * K = 0` and with the kernel of `v ↦ M.mulVec v` contained in the
column space of `K` (hypothesis `hgen`); thus `R^q --K--> R^m --M--> R^n` is exact in the middle.
Then for every Sylvester matrix rank function `rk` on `R`,

  `rk M + rk K = m`,

the `m` being the dimension of the middle term `R^m`.

The two halves of the equality are of very different natures:

* `rk M + rk K ≤ m` is the Sylvester law of nullity `rk A + rk B ≤ rk (A * B) + m`
  (`RankAPI.rk_mul_add_le`) together with `M * K = 0`;
* `m ≤ rk M + rk K` uses the exactness and the von Neumann regularity of `R`.  Since `R` is
  regular, the matrix `K` has a weak inverse `T` with `K * T * K = K` (the private lemma
  `exists_mul_mul_eq_self'` below; the same statement is available in the shared library as
  `RegularRing.exists_mul_mul_eq_self`), so `E := K * T` is a "projection onto the column space
  of `K`": `E * K = K` and `E = K * T`; in particular `rk E = rk K`.  Likewise `G := M * U` with
  `M * U * M = M`.  The exactness makes `im K = ker M`, which is the hypothesis needed by
  `RegularRing.exists_mul_eq_one_sub` to produce `S` with `S * M = 1 - E`, whence
  `rk (1 - E) ≤ rk M`.  Finally `m = rk (1 - E + E) ≤ rk (1 - E) + rk E` by subadditivity of `rk`
  (`RankAPI.rk_add_le`), and putting the three estimates together gives the result.

Note that nothing here requires `E` to be idempotent: all the rank bookkeeping uses only
`E * K = K`, `K * T = E` and `M * K = 0`.
-/
import Mathlib
import Submission.Work.ORHughesFree.SylvesterRank
import Submission.Work.ORHughesFree.StarRegular
import Submission.Work.ORHughesFree.RankAPI.rk_add_le
import Submission.Work.ORHughesFree.RankAPI.rk_mul_add_le
import Submission.Work.ORHughesFree.RankAPI.rk_one_fin
import Submission.Work.ORHughesFree.RegularRing.exists_mul_eq_one_sub
import Submission.Work.ORVonNeumann.Regular.matrix_vonNeumannRegular

set_option autoImplicit false

namespace Work.ORHughesFree.NaturalExtension

open Work.ORHughesFree

/-- **Every matrix over a von Neumann regular ring has a weak inverse**: for a (not necessarily
square) matrix `A : Matrix (Fin n) (Fin m) R` over a von Neumann regular ring there is
`U : Matrix (Fin m) (Fin n) R` with `A * U * A = A`.

Apply `Work.ORVonNeumann.Regular.exists_idempotent_of_vectors` to the family of *rows* of `A`:
it produces an idempotent `P : Matrix (Fin m) (Fin m) R` with `∀ u, u ᵥ* P ∈ span (range rows)`
and `∀ i, row_i A ᵥ* P = row_i A`, the latter being exactly `A * P = A`.  The former, applied to
the standard basis vectors, shows that every row of `P` is a combination of the rows of `A`, so
`X * A = P` for some `X`; then `A * X * A = A * (X * A) = A * P = A`. -/
private theorem exists_mul_mul_eq_self' {R : Type*} [Ring R] [VonNeumannRegularRing R] {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) R) : ∃ U : Matrix (Fin m) (Fin n) R, A * U * A = A := by
  have hreg : Work.ORVonNeumann.VonNeumannRegular R :=
    fun x => (inferInstance : VonNeumannRegularRing R).exists_mul_inverse x
  obtain ⟨P, _hPP, hspan, hfix⟩ :=
    Work.ORVonNeumann.Regular.exists_idempotent_of_vectors (R := R) hreg m n (fun i j => A i j)
  -- the columns of `A` are fixed: `A * P = A`
  have hAP : A * P = A := by
    ext i j
    have h := congrFun (hfix i) j
    simp only [Matrix.vecMul_apply, Matrix.col_apply, dotProduct, Matrix.mul_apply] at h ⊢
    exact h
  -- every row of `P` is a combination of the rows of `A`
  have hrow : ∀ l : Fin m, ∃ c : Fin n → R, ∑ i, c i • (fun j => A i j) = P l := by
    intro l
    have h := (Submodule.mem_span_range_iff_exists_fun R).mp (hspan (Pi.single l 1))
    rwa [Work.ORVonNeumann.Regular.row_eq_single_vecMul P l] at h
  choose c hc using hrow
  set X : Matrix (Fin m) (Fin n) R := fun l i => c l i with hX
  have hXA : X * A = P := by
    ext l j
    rw [Matrix.mul_apply, hX]
    have h := congrFun (hc l) j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    simpa using h
  exact ⟨X, by rw [Matrix.mul_assoc, hXA, hAP]⟩

/--
**Rank–nullity for an exact sequence of matrices over a von Neumann regular ring.**

If `M * K = 0` and every vector killed by `M` is a value of `K` (so that
`R^q --K--> R^m --M--> R^n` is exact in the middle), then `rk M + rk K = m`.
-/
theorem rk_add_rk_of_ker {R : Type*} [Ring R] [VonNeumannRegularRing R] (rk : SylvesterRank R)
    {n m q : ℕ} (M : Matrix (Fin n) (Fin m) R) (K : Matrix (Fin m) (Fin q) R)
    (hMK : M * K = 0)
    (hgen : ∀ v : Fin m → R, M.mulVec v = 0 → ∃ c : Fin q → R, v = K.mulVec c) :
    rk.rk n m M + rk.rk m q K = (m : ℝ) := by
  -- Weak inverses of `K` and of `M`, and the two "projections" they provide.
  obtain ⟨T, hT⟩ := exists_mul_mul_eq_self' K
  obtain ⟨U, hU⟩ := exists_mul_mul_eq_self' M
  have hEK : (K * T) * K = K := hT
  have hGM : (M * U) * M = M := hU
  -- `E := K * T` fixes every vector of `ker M = im K`.
  have hker : ∀ v : Fin m → R, M.mulVec v = 0 → (K * T).mulVec v = v := by
    intro v hv
    obtain ⟨c, hc⟩ := hgen v hv
    rw [hc, show (K * T).mulVec (K.mulVec c) = ((K * T) * K).mulVec c from
      Matrix.mulVec_mulVec c (K * T) K, hEK]
  -- Hence `1 - E` factors through `M`.
  obtain ⟨S, hS⟩ := RegularRing.exists_mul_eq_one_sub M (K * T) (M * U) hGM ⟨U, rfl⟩ hker
  -- `rk E = rk K`.
  have hrkE : rk.rk m m (K * T) = rk.rk m q K := by
    refine le_antisymm (rk.rk_mul_le_left K T) ?_
    calc rk.rk m q K = rk.rk m q ((K * T) * K) := by rw [hEK]
      _ ≤ rk.rk m m (K * T) := rk.rk_mul_le_left (K * T) K
  -- `rk (1 - E) ≤ rk M`.
  have hle : rk.rk m m (1 - K * T) ≤ rk.rk n m M := by
    rw [← hS]
    exact rk.rk_mul_le_right S M
  -- `m = rk 1 ≤ rk (1 - E) + rk E` by subadditivity.
  have hge : (m : ℝ) ≤ rk.rk m m (1 - K * T) + rk.rk m m (K * T) := by
    have h := RankAPI.rk_add_le rk (1 - K * T) (K * T)
    rw [show (1 - K * T) + (K * T) = (1 : Matrix (Fin m) (Fin m) R) from sub_add_cancel _ _,
      RankAPI.rk_one_fin rk m] at h
    exact h
  -- and `rk M + rk K ≤ rk (M * K) + m = m` by the Sylvester law of nullity.
  have hle' : rk.rk n m M + rk.rk m q K ≤ (m : ℝ) := by
    have h := RankAPI.rk_mul_add_le rk M K
    rw [hMK, rk.rk_zero] at h
    linarith
  refine le_antisymm hle' ?_
  linarith

end Work.ORHughesFree.NaturalExtension
