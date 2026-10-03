/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The truncation of `I + A t` has full rank

For a Sylvester rank function `rk` on a ring `U`, a matrix `A` over `U` and a positive integer `i`,
the truncation `trunc i (onePlusAt n A)` of the matrix `I + A t` over `U[t^{±1};τ]` has rank
exactly `n * i`:

`rk (trunc i (onePlusAt n A)) = i * n`.

This is the exact-rank form of the `A t`-part of [JZLA20, Proposition 3.5]: since
`coeffMat (onePlusAt n A) 0 = 1` and `coeffMat (onePlusAt n A) 1 = A`, the truncation is the
identity plus a matrix `N` whose only nonzero entries shift the "degree" `Fin.modNat : Fin i` up
by one.  Such a matrix is nilpotent of order `i` (`pow_eq_zero_of_colDeg_shift`, a combinatorial
fact about `Fin (n * i)`), so `1 + N = trunc i (onePlusAt n A)` is invertible over `U`; a square
matrix over a ring admitting a one-sided inverse has maximal rank, and the rank of the identity is
`n * i` (`RankAPI.rk_one_fin`).
-/
import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.Defs
import Submission.Work.ORHughesFree.NaturalExtension
import Submission.Work.ORHughesFree.RankAPI.rk_one_fin
import Submission.Work.ORHughesFree.NaturalExtension.pow_eq_zero_of_colDeg_shift

namespace Work.ORHughesFree.NaturalExtension

open Matrix

section Coeff

/-- Coefficient extraction is additive on `U[t^{±1};τ]`. -/
lemma rk_trunc_onePlusAt_coeffElt_add {U : Type} [AddMonoid U] (a b : SkewL U) (k : ℤ) :
    coeffElt (a + b) k = coeffElt a k + coeffElt b k := by
  simp [coeffElt, SkewMonoidAlgebra.coeff_add]

/-- The `k`-th coefficient of the unit of `U[t^{±1};τ]`. -/
lemma rk_trunc_onePlusAt_coeffElt_one {U : Type} [AddMonoidWithOne U] (k : ℤ) :
    coeffElt (1 : SkewL U) k = if k = 0 then (1 : U) else 0 := by
  by_cases h : k = 0
  · subst h
    simp [coeffElt, SkewMonoidAlgebra.coeff_one]
  · simp [coeffElt, SkewMonoidAlgebra.coeff_one, h]

/-- The `k`-th coefficient of the monomial `t · u` of `U[t^{±1};τ]`. -/
lemma rk_trunc_onePlusAt_coeffElt_single {U : Type} [AddMonoid U] (u : U) (k : ℤ) :
    coeffElt (SkewMonoidAlgebra.single (Multiplicative.ofAdd (1 : ℤ)) u) k =
      if k = 1 then u else 0 := by
  have h : coeffElt (SkewMonoidAlgebra.single (Multiplicative.ofAdd (1 : ℤ)) u) k =
      if (1 : ℤ) = k then u else 0 := by
    simp [coeffElt, SkewMonoidAlgebra.coeff_single, Finsupp.single_apply,
      Multiplicative.ofAdd.injective.eq_iff]
  rw [h]
  exact if_congr eq_comm rfl rfl

/-- The coefficients of the entries of the matrix `onePlusAt n A = 1 + A·t` over `U[t^{±1};τ]`:
the `(p, q)` entry of the identity for `k = 0`, the `(p, q)` entry of `A` for `k = 1`, and `0`
otherwise. -/
lemma rk_trunc_onePlusAt_coeffMat {U : Type} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]
    {n : ℕ} (A : Matrix (Fin n) (Fin n) U) (k : ℤ) (p q : Fin n) :
    coeffMat (onePlusAt n A) k p q =
      (if k = 0 then (if p = q then (1 : U) else 0) else 0) + (if k = 1 then A p q else 0) := by
  rw [coeffMat_apply, Work.ORHughesFree.onePlusAt, Matrix.add_apply, Matrix.one_apply,
    Matrix.map_apply, rk_trunc_onePlusAt_coeffElt_add, rk_trunc_onePlusAt_coeffElt_single]
  by_cases hpq : p = q
  · subst hpq
    simp [rk_trunc_onePlusAt_coeffElt_one]
  · simp [hpq, coeffElt]

end Coeff

/-- The diagonal (degree-shift zero) part of the truncation of `onePlusAt n A` is the identity
matrix: the entries with `y.modNat = x.modNat` and `x.divNat = y.divNat` are the unique `1` of the
identity, and all other entries of that part vanish. -/
lemma trunc_onePlusAt_diag_part {U : Type} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]
    {n i : ℕ} (x y : Fin (n * i)) :
    (Multiplicative.ofAdd ((x.modNat : ℕ) : ℤ)) •
      (if ((y.modNat : ℤ) - (x.modNat : ℤ)) = 0 then
        (if x.divNat = y.divNat then (1 : U) else 0) else 0)
      = (if x = y then 1 else 0) := by
  have hk0 : ((y.modNat : ℤ) - (x.modNat : ℤ)) = 0 ↔ y.modNat = x.modNat := by
    rw [sub_eq_zero, Int.ofNat_inj, Fin.ext_iff]
  have hxy : x = y ↔ (x.divNat = y.divNat ∧ x.modNat = y.modNat) := by
    constructor
    · intro h; subst h; exact ⟨rfl, rfl⟩
    · intro ⟨h1, h2⟩
      have h3 : finProdFinEquiv.symm x = finProdFinEquiv.symm y := by
        rw [finProdFinEquiv_symm_apply, finProdFinEquiv_symm_apply, h1, h2]
      exact finProdFinEquiv.symm.injective h3
  by_cases h : x = y
  · subst h; simp [smul_one]
  · have hzero : (if ((y.modNat : ℤ) - (x.modNat : ℤ)) = 0 then
        (if x.divNat = y.divNat then (1 : U) else 0) else 0) = 0 := by
      by_cases hk : ((y.modNat : ℤ) - (x.modNat : ℤ)) = 0
      · rw [if_pos hk, if_neg]
        intro hdiv
        exact h ((hxy).mpr ⟨hdiv, (hk0.mp hk).symm⟩)
      · rw [if_neg hk]
    rw [hzero, smul_zero, if_neg h]

/-- The `(x, y)` entry of the "off-diagonal" part `trunc i (onePlusAt n A) - 1` of the truncation
of `I + A t`: it is the `(x, y)` entry of `A` twisted by `t^{x.modNat}`, and it can be nonzero only
when the degree `y.modNat` of the column is exactly one more than the degree `x.modNat` of the
row.  (Equivalently: `trunc i (onePlusAt n A) = 1 + N` where `N` shifts the degree up by one, so
that `N` is nilpotent of order `i`.) -/
lemma trunc_onePlusAt_sub_one_apply {U : Type} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]
    {n : ℕ} (A : Matrix (Fin n) (Fin n) U) (i : ℕ) (x y : Fin (n * i)) :
    (trunc i (onePlusAt n A) - 1) x y =
      (Multiplicative.ofAdd ((x.modNat : ℕ) : ℤ)) •
        (if ((y.modNat : ℤ) = (x.modNat : ℤ) + 1) then A x.divNat y.divNat else 0) := by
  have hcoeff :
      coeffElt ((onePlusAt n A) x.divNat y.divNat) ((y.modNat : ℤ) - (x.modNat : ℤ))
      = (if ((y.modNat : ℤ) - (x.modNat : ℤ)) = 0 then
            (if x.divNat = y.divNat then (1 : U) else 0) else 0)
        + (if ((y.modNat : ℤ) - (x.modNat : ℤ)) = 1 then A x.divNat y.divNat else 0) :=
    rk_trunc_onePlusAt_coeffMat A _ x.divNat y.divNat
  have hcond :
      (((y.modNat : ℤ) - (x.modNat : ℤ)) = 1) ↔ ((y.modNat : ℤ) = (x.modNat : ℤ) + 1) := by
    omega
  rw [Matrix.sub_apply, trunc_apply i (onePlusAt n A) x y, Matrix.smul_apply, coeffMat_apply,
    hcoeff]
  rw [Matrix.one_apply, smul_add, trunc_onePlusAt_diag_part]
  rw [if_congr hcond rfl rfl]
  rw [add_sub_cancel_left]

theorem rk_trunc_onePlusAt {U : Type} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]
    (rk : SylvesterRank U) {n : ℕ} (A : Matrix (Fin n) (Fin n) U) (i : ℕ) :
    rk.rk (n * i) (n * i) (trunc i (onePlusAt n A)) = (i : ℝ) * n := by
  -- Write `M = 1 + N`.  The matrix `N` is supported on the entries that raise the degree by one,
  -- so `N ^ i = 0`; hence `M` is invertible, and a square matrix admitting a one-sided inverse has
  -- maximal rank `n * i`, which is `i * n`.
  set N : Matrix (Fin (n * i)) (Fin (n * i)) U := trunc i (onePlusAt n A) - 1 with hN
  have hT : trunc i (onePlusAt n A) = 1 + N := by rw [hN]; abel
  have hshift : ∀ x y : Fin (n * i), N x y ≠ 0 → (y.modNat : ℕ) = (x.modNat : ℕ) + 1 := by
    intro x y h
    by_cases hc : ((y.modNat : ℤ) = (x.modNat : ℤ) + 1)
    · omega
    · rw [hN, trunc_onePlusAt_sub_one_apply, if_neg hc, smul_zero] at h
      exact absurd rfl h
  have hnil : N ^ i = 0 := pow_eq_zero_of_colDeg_shift N hshift
  have hunit : IsUnit (1 + N) := IsNilpotent.isUnit_one_add ⟨i, hnil⟩
  have h1 : rk.rk (n * i) (n * i) ((1 + N) * 1) =
      rk.rk (n * i) (n * i) (1 : Matrix (Fin (n * i)) (Fin (n * i)) U) :=
    SylvesterRank.rk_eq_of_left_inverse_mul rk (1 + N)
      (↑(hunit.unit⁻¹) : Matrix (Fin (n * i)) (Fin (n * i)) U) (IsUnit.val_inv_mul hunit) 1
  rw [Matrix.mul_one] at h1
  rw [hT, h1, Work.ORHughesFree.RankAPI.rk_one_fin rk (n * i)]
  push_cast
  ring

end Work.ORHughesFree.NaturalExtension
