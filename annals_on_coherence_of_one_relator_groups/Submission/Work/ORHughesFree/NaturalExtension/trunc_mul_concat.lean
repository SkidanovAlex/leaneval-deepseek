/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The truncation of a product is the concatenation of its blocks

For matrices `A : Matrix (Fin n) (Fin m) (SkewL U)` and `B : Matrix (Fin m) (Fin k) (SkewL U)`
over the skew Laurent polynomial ring `U[t^{±1};τ] = SkewL U`, the truncation of the product is
the sum of the outer products of the row block `truncBlkRow A i u` with the column block
`truncBlkCol B i u`, over all intermediate degrees `u` in the *defect range*
`[-lowerDeg A, i - 1 + lowerDeg B]`:

`trunc i (A * B) = ∑ u ∈ defectRange A B i, truncBlkRow A i u * truncBlkCol B i u`.

The range is exactly the set of intermediate degrees `u` for which the block product can be
nonzero; outside it one of the two factors vanishes (see `truncBlk_mul_eq_zero`).  The proof is
entrywise: the `(x, y)` entry of `trunc i (A * B)` is

`(t^{x.modNat}) • (A * B)_{y.modNat - x.modNat}[x.divNat, y.divNat]`,

and expanding the coefficient of the product `A * B` (via `coeffMat_mul_bdd`, i.e. the coefficient
formula `(A * B)_w = ∑_v A_v · (t^v B_{w-v})`) turns it into the sum of the entrywise block
products over the degrees `v` occurring in `A`, shifted by `x.modNat`.  Reindexing by `x.modNat`
(a `Finset.Icc` shift) and observing that both the shifted range and the defect range differ only
by terms on which the summand vanishes gives the claim.
-/
import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.TruncDefect
import Submission.Work.ORHughesFree.NaturalExtension.coeffMat_mul_bdd

set_option autoImplicit false

namespace Work.ORHughesFree.NaturalExtension

open Matrix

/-- The `(x, l)` entry of the row block at intermediate degree `u + r`, where `r = x.modNat`. -/
lemma truncBlkRow_apply_add {U : Type} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]
    {n m : ℕ} (A : Matrix (Fin n) (Fin m) (SkewL U)) (i : ℕ) (u : ℤ)
    (x : Fin (n * i)) (l : Fin m) :
    truncBlkRow A i (u + (x.modNat : ℤ)) x l =
      (Multiplicative.ofAdd ((x.modNat : ℤ))) • coeffElt (A x.divNat l) u := by
  have h : (u + (x.modNat : ℤ)) - (x.modNat : ℤ) = u := by ring
  simp only [truncBlkRow, coeffMat_apply, h]

/-- The `(l, y)` entry of the column block at intermediate degree `u + r`, for any shift `r`. -/
lemma truncBlkCol_apply_add {U : Type} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]
    {m k : ℕ} (B : Matrix (Fin m) (Fin k) (SkewL U)) (i : ℕ) (u r : ℤ)
    (l : Fin m) (y : Fin (k * i)) :
    truncBlkCol B i (u + r) l y =
      (Multiplicative.ofAdd (u + r)) • coeffElt (B l y.divNat) ((y.modNat : ℤ) - r - u) := by
  have h : (y.modNat : ℤ) - (u + r) = (y.modNat : ℤ) - r - u := by ring
  simp only [truncBlkCol, coeffMat_apply, h]

/-- Entrywise form of the block decomposition: the `(x, y)` entry of `trunc i (A * B)` is the sum
of the entrywise block products over the degrees `v` occurring in `A` (i.e. `v ∈ [-lowerDeg A,
upperDeg A]`), shifted by `x.modNat`. -/
theorem trunc_mul_apply_eq_sum {U : Type} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]
    {n m k : ℕ} (A : Matrix (Fin n) (Fin m) (SkewL U)) (B : Matrix (Fin m) (Fin k) (SkewL U))
    (i : ℕ) (x : Fin (n * i)) (y : Fin (k * i)) :
    trunc i (A * B) x y =
      ∑ v ∈ Finset.Icc (-(lowerDeg A : ℤ)) (upperDeg A : ℤ),
        (truncBlkRow A i (v + (x.modNat : ℤ)) * truncBlkCol B i (v + (x.modNat : ℤ))) x y := by
  classical
  rw [trunc_apply, coeffMat_mul_bdd, Matrix.smul_apply, Matrix.sum_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [Matrix.mul_apply, Finset.smul_sum, Matrix.mul_apply]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [truncBlkRow_apply_add, truncBlkCol_apply_add]
  simp only [Matrix.smul_apply, coeffMat_apply, smul_mul']
  rw [smul_smul, ← ofAdd_add, add_comm]

/-- Shifting the summation variable of an `Icc`-sum by a constant. -/
theorem sum_Icc_add_right {N : Type*} [AddCommMonoid N] (φ : ℤ → N) (lo hi r : ℤ) :
    ∑ v ∈ Finset.Icc lo hi, φ (v + r) = ∑ u ∈ Finset.Icc (lo + r) (hi + r), φ u := by
  classical
  have himg : (Finset.Icc lo hi).image (fun v : ℤ => v + r) = Finset.Icc (lo + r) (hi + r) := by
    ext u
    simp only [Finset.mem_image, Finset.mem_Icc]
    constructor
    · rintro ⟨v, hv, rfl⟩; exact ⟨by omega, by omega⟩
    · intro h; exact ⟨u - r, ⟨by omega, by omega⟩, by omega⟩
  rw [← himg]
  exact (Finset.sum_image (f := φ) (s := Finset.Icc lo hi) (g := fun v : ℤ => v + r)
    (by intro a _ b _ h; change a + r = b + r at h; omega)).symm

theorem trunc_mul_concat {U : Type} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]
    {n m k : ℕ} (A : Matrix (Fin n) (Fin m) (SkewL U)) (B : Matrix (Fin m) (Fin k) (SkewL U))
    (i : ℕ) :
    trunc i (A * B) =
      ∑ u ∈ defectRange A B i, truncBlkRow A i u * truncBlkCol B i u := by
  ext x y
  rw [Matrix.sum_apply]
  rw [trunc_mul_apply_eq_sum A B i x y]
  set r : ℤ := (x.modNat : ℤ) with hr
  let φ : ℤ → U := fun u => (truncBlkRow A i u * truncBlkCol B i u) x y
  change (∑ v ∈ Finset.Icc (-(lowerDeg A : ℤ)) (upperDeg A : ℤ), φ (v + r))
      = ∑ u ∈ defectRange A B i, φ u
  have hr0 : 0 ≤ r := by rw [hr]; exact Int.natCast_nonneg _
  have hrlt : r ≤ (i : ℤ) - 1 := by
    rw [hr]; have := x.modNat.isLt; omega
  set M : ℤ := ((i : ℤ) - 1) + max (upperDeg A : ℤ) (lowerDeg B : ℤ) with hM
  have hM1 : (upperDeg A : ℤ) + r ≤ M := by
    rw [hM]
    have : (upperDeg A : ℤ) ≤ max (upperDeg A : ℤ) (lowerDeg B : ℤ) := le_max_left _ _
    omega
  have hM2 : ((i : ℤ) - 1) + (lowerDeg B : ℤ) ≤ M := by
    rw [hM]
    have : (lowerDeg B : ℤ) ≤ max (upperDeg A : ℤ) (lowerDeg B : ℤ) := le_max_right _ _
    omega
  -- The summand vanishes below the shifted range and above it.
  have hφA : ∀ u : ℤ, u - r < -(lowerDeg A : ℤ) → φ u = 0 := by
    intro u hu
    change (truncBlkRow A i u * truncBlkCol B i u) x y = 0
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero (fun l _ => ?_)
    have h1 : truncBlkRow A i u x l =
        (Multiplicative.ofAdd ((x.modNat : ℤ))) • coeffElt (A x.divNat l)
          (u - (x.modNat : ℤ)) := by
      simp only [truncBlkRow, coeffMat_apply]
    rw [h1, coeffElt_eq_zero_of_lt_lowerDeg A x.divNat l (by rw [← hr]; exact hu),
      smul_zero, zero_mul]
  have hφA' : ∀ u : ℤ, (upperDeg A : ℤ) < u - r → φ u = 0 := by
    intro u hu
    change (truncBlkRow A i u * truncBlkCol B i u) x y = 0
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero (fun l _ => ?_)
    have h1 : truncBlkRow A i u x l =
        (Multiplicative.ofAdd ((x.modNat : ℤ))) • coeffElt (A x.divNat l)
          (u - (x.modNat : ℤ)) := by
      simp only [truncBlkRow, coeffMat_apply]
    rw [h1, coeffElt_eq_zero_of_gt_upperDeg A x.divNat l (by rw [← hr]; exact hu),
      smul_zero, zero_mul]
  have hφB : ∀ u : ℤ, (y.modNat : ℤ) - u < -(lowerDeg B : ℤ) → φ u = 0 := by
    intro u hu
    change (truncBlkRow A i u * truncBlkCol B i u) x y = 0
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero (fun l _ => ?_)
    have h1 : truncBlkCol B i u l y =
        (Multiplicative.ofAdd u) • coeffElt (B l y.divNat) ((y.modNat : ℤ) - u) := by
      simp only [truncBlkCol, coeffMat_apply]
    rw [h1, coeffElt_eq_zero_of_lt_lowerDeg B l y.divNat hu, smul_zero, mul_zero]
  have hzero1 : ∀ u ∈ Finset.Icc (-(lowerDeg A : ℤ)) M,
      u ∉ Finset.Icc (-(lowerDeg A : ℤ) + r) ((upperDeg A : ℤ) + r) → φ u = 0 := by
    intro u _ hnot
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hnot
    rcases hnot with hlt | hgt
    · exact hφA u (by omega)
    · exact hφA' u (by omega)
  have hzero2 : ∀ u ∈ Finset.Icc (-(lowerDeg A : ℤ)) M, u ∉ defectRange A B i → φ u = 0 := by
    intro u hu hnot
    rw [Finset.mem_Icc] at hu
    have hy : (y.modNat : ℤ) ≤ (i : ℤ) - 1 := by have := y.modNat.isLt; omega
    simp only [defectRange, Finset.mem_Icc, not_and_or, not_le, not_le] at hnot
    rcases hnot with hlt | hgt
    · omega
    · exact hφB u (by omega)
  have hsub1 : Finset.Icc (-(lowerDeg A : ℤ) + r) ((upperDeg A : ℤ) + r)
      ⊆ Finset.Icc (-(lowerDeg A : ℤ)) M := by
    intro u hu
    rw [Finset.mem_Icc] at hu ⊢
    exact ⟨by omega, by omega⟩
  have hsub2 : defectRange A B i ⊆ Finset.Icc (-(lowerDeg A : ℤ)) M := by
    intro u hu
    simp only [defectRange, Finset.mem_Icc] at hu
    rw [Finset.mem_Icc]
    exact ⟨hu.1, by omega⟩
  have hf1 := sum_Icc_add_right φ (-(lowerDeg A : ℤ)) (upperDeg A : ℤ) r
  have hf2 : (∑ u ∈ Finset.Icc (-(lowerDeg A : ℤ) + r) ((upperDeg A : ℤ) + r), φ u)
      = ∑ u ∈ Finset.Icc (-(lowerDeg A : ℤ)) M, φ u :=
    Finset.sum_subset hsub1 hzero1
  have hf3 : (∑ u ∈ defectRange A B i, φ u)
      = ∑ u ∈ Finset.Icc (-(lowerDeg A : ℤ)) M, φ u :=
    Finset.sum_subset hsub2 hzero2
  exact hf1.trans (hf2.trans hf3.symm)

end Work.ORHughesFree.NaturalExtension
