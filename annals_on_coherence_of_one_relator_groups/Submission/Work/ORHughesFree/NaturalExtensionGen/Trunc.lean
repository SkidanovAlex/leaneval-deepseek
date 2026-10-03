/-
Generated universe-`u` copies of the universe-0 lemmas needed for the
universe-polymorphic natural extension theorem.
-/

import Submission.Work.ORHughesFree.NaturalExtension.Defs
import Submission.Work.ORHughesFree.NaturalExtension.TruncDefect
import Submission.Work.ORHughesFree.NaturalExtension.EltDeg
import Submission.Work.ORHughesFree.NaturalExtension.lowRowEmbed_spec
import Submission.Work.ORHughesFree.NaturalExtension.highColEmbed_spec
import Submission.Work.ORHughesFree.NaturalExtension.rk_le_card_of_rowSupport
import Submission.Work.ORHughesFree.NaturalExtension.rk_le_card_of_colSupport
import Submission.Work.ORHughesFree.RankAPI.rk_add_le

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

namespace Work.ORHughesFree.NaturalExtensionGen.Trunc

open Matrix
open Work.ORHughesFree.NaturalExtension

/- copy of NaturalExtension/coeffMat_mul_bdd.lean -/

open Matrix

/-- Auxiliary rewriting rule: `ofAdd` of a difference of integers is the corresponding quotient in
`Multiplicative ℤ`. -/
theorem ofAdd_sub_toAdd (a : Multiplicative ℤ) (w : ℤ) :
    Multiplicative.ofAdd (w - Multiplicative.toAdd a) = a⁻¹ * Multiplicative.ofAdd w := by
  rw [ofAdd_sub, ofAdd_toAdd, div_eq_mul_inv, mul_comm]

/-- The `w`-th coefficient of a product `f * g`, written as a sum over the degrees occurring
in `f`. -/
theorem coeffElt_mul_support {U : Type u} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]
    (f g : SkewL U) (w : ℤ) :
    coeffElt (f * g) w =
      ∑ v ∈ f.support.image Multiplicative.toAdd,
        coeffElt f v * (Multiplicative.ofAdd v • coeffElt g (w - v)) := by
  rw [coeffElt, SkewMonoidAlgebra.coeff_mul_left, Finsupp.sum]
  rw [Finset.sum_image (s := f.support) (g := Multiplicative.toAdd)
      (f := fun v => coeffElt f v * (Multiplicative.ofAdd v • coeffElt g (w - v)))
      (fun x _ y _ h => Multiplicative.toAdd.injective h)]
  apply Finset.sum_congr rfl
  intro a _
  simp only [coeffElt, ofAdd_toAdd, ofAdd_sub_toAdd]

/-- The degrees occurring in `f` lie in the interval cut out by any pair of degree bounds. -/
theorem image_toAdd_support_subset_Icc {U : Type u} [AddMonoid U] (f : SkewL U) {L K : ℕ}
    (hL : lowDeg f ≤ L) (hK : upDeg f ≤ K) :
    f.support.image Multiplicative.toAdd ⊆ Finset.Icc (-(L : ℤ)) (K : ℤ) := by
  intro v hv
  rw [Finset.mem_image] at hv
  obtain ⟨a, ha, rfl⟩ := hv
  have ha' := support_subset_Icc_image f hL hK ha
  rw [Finset.mem_image] at ha'
  obtain ⟨u, hu, hua⟩ := ha'
  rw [← hua]
  simpa using hu

/-- Coefficient formula for a product of two elements of `U[t^{±1};τ]`, summed over an interval
containing all degrees occurring in the left factor. -/
theorem coeffElt_mul_bdd {U : Type u} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]
    (f g : SkewL U) (w : ℤ) {L K : ℕ} (hL : lowDeg f ≤ L) (hK : upDeg f ≤ K) :
    coeffElt (f * g) w =
      ∑ v ∈ Finset.Icc (-(L : ℤ)) (K : ℤ),
        coeffElt f v * (Multiplicative.ofAdd v • coeffElt g (w - v)) := by
  rw [coeffElt_mul_support]
  refine Finset.sum_subset (image_toAdd_support_subset_Icc f hL hK) ?_
  intro v _ hvnot
  have h1 : Multiplicative.ofAdd v ∉ f.support := by
    intro hmem
    exact hvnot (Finset.mem_image.mpr ⟨v, hmem, rfl⟩)
  simp only [coeffElt]
  rw [Finsupp.notMem_support_iff.mp h1, zero_mul]

/-- Coefficient extraction at a fixed degree is additive. -/
def coeffEltAddHom {U : Type u} [AddCommMonoid U] (w : ℤ) : SkewL U →+ U where
  toFun f := coeffElt f w
  map_zero' := by simp [coeffElt]
  map_add' f g := by simp [coeffElt, SkewMonoidAlgebra.coeff_add]

/-- Coefficient extraction commutes with finite sums. -/
theorem coeffElt_sum {U : Type u} [AddCommMonoid U] {ι : Type} (s : Finset ι)
    (f : ι → SkewL U) (w : ℤ) :
    coeffElt (∑ i ∈ s, f i) w = ∑ i ∈ s, coeffElt (f i) w :=
  map_sum (coeffEltAddHom w) f s

/-- The lower degree of an entry of a matrix is bounded by the lower degree of the matrix. -/
theorem lowDeg_le_lowerDeg {U : Type u} [AddMonoid U] {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) (SkewL U)) (i : Fin n) (j : Fin m) :
    lowDeg (A i j) ≤ lowerDeg A :=
  Finset.le_sup (f := fun p : Fin n × Fin m =>
      (SkewMonoidAlgebra.coeff (A p.1 p.2)).support.sup
        (fun g => Int.toNat (-(Multiplicative.toAdd g)))) (Finset.mem_univ (i, j))

/-- The upper degree of an entry of a matrix is bounded by the upper degree of the matrix. -/
theorem upDeg_le_upperDeg {U : Type u} [AddMonoid U] {n m : ℕ}
    (A : Matrix (Fin n) (Fin m) (SkewL U)) (i : Fin n) (j : Fin m) :
    upDeg (A i j) ≤ upperDeg A :=
  Finset.le_sup (f := fun p : Fin n × Fin m =>
      (SkewMonoidAlgebra.coeff (A p.1 p.2)).support.sup
        (fun g => Int.toNat (Multiplicative.toAdd g))) (Finset.mem_univ (i, j))

theorem coeffMat_mul_bdd {U : Type u} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]
    {n m k : ℕ} (A : Matrix (Fin n) (Fin m) (SkewL U)) (B : Matrix (Fin m) (Fin k) (SkewL U))
    (w : ℤ) :
    coeffMat (A * B) w =
      ∑ v ∈ Finset.Icc (-(lowerDeg A : ℤ)) (upperDeg A : ℤ),
        coeffMat A v * ((Multiplicative.ofAdd v) • coeffMat B (w - v)) := by
  classical
  ext i j
  rw [coeffMat_apply, Matrix.mul_apply]
  rw [coeffElt_sum]
  rw [Matrix.sum_apply]
  simp only [Matrix.mul_apply, Matrix.smul_apply, coeffMat_apply]
  have hterm : ∀ p : Fin m, coeffElt (A i p * B p j) w =
      ∑ v ∈ Finset.Icc (-(lowerDeg A : ℤ)) (upperDeg A : ℤ),
        coeffElt (A i p) v * ((Multiplicative.ofAdd v) • coeffElt (B p j) (w - v)) :=
    fun p => coeffElt_mul_bdd (A i p) (B p j) w (lowDeg_le_lowerDeg A i p)
      (upDeg_le_upperDeg A i p)
  simp only [hterm]
  rw [Finset.sum_comm]

/- copy of NaturalExtension/trunc_mul_eq_sum.lean -/

/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The block decomposition of the product of two truncations

For matrices `A : Matrix (Fin n) (Fin m) (SkewL U)` and `B : Matrix (Fin m) (Fin k) (SkewL U)`
over the skew Laurent polynomial ring, the product `trunc i A * trunc i B` of the truncations is
the sum over the *intermediate degrees* `v ∈ [0, i)` of the outer products of the row block
`truncBlkRow A i v` with the column block `truncBlkCol B i v`.

Both sides are, entrywise, a sum over the intermediate index `(j, v) ∈ Fin m × Fin i`; the only
content is the reindexing of the summation from `Fin (m * i)` to `Fin m × Fin i` via
`finProdFinEquiv`, together with the definitional unfolding of the truncation and of the two
block matrices.
-/


open Matrix

theorem trunc_mul_eq_sum {U : Type u} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]
    {n m k : ℕ} (A : Matrix (Fin n) (Fin m) (SkewL U)) (B : Matrix (Fin m) (Fin k) (SkewL U))
    (i : ℕ) :
    trunc i A * trunc i B =
      ∑ v : Fin i, truncBlkRow A i ((v : ℕ) : ℤ) * truncBlkCol B i ((v : ℕ) : ℤ) := by
  ext x y
  simp only [Matrix.mul_apply, Matrix.sum_apply]
  -- The common summand, written with the intermediate index split as `(j, w) ∈ Fin m × Fin i`.
  have hterm : ∀ (j : Fin m) (w : Fin i),
      trunc i A x (finProdFinEquiv (j, w)) * trunc i B (finProdFinEquiv (j, w)) y
        = truncBlkRow A i ((w : ℕ) : ℤ) x j * truncBlkCol B i ((w : ℕ) : ℤ) j y := by
    intro j w
    rw [trunc_apply, trunc_apply, truncBlkRow, truncBlkCol,
      Work.ORHughesFree.MatrixBlocks.finProdFinEquiv_fst,
      Work.ORHughesFree.MatrixBlocks.finProdFinEquiv_snd]
    simp [Matrix.smul_apply]
  -- Reindex the summation over `Fin (m * i)` on the left as a double sum over `Fin m × Fin i`.
  rw [← Equiv.sum_comp finProdFinEquiv
        (fun u : Fin (m * i) => trunc i A x u * trunc i B u y)]
  rw [Fintype.sum_prod_type]
  -- Swap the order of summation on the right, and match the summands.
  rw [show (∑ c : Fin i, ∑ j : Fin m,
        truncBlkRow A i ((c : ℕ) : ℤ) x j * truncBlkCol B i ((c : ℕ) : ℤ) j y)
      = ∑ j : Fin m, ∑ c : Fin i,
        truncBlkRow A i ((c : ℕ) : ℤ) x j * truncBlkCol B i ((c : ℕ) : ℤ) j y
      from Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun c _ => hterm j c

/- copy of NaturalExtension/truncBlkRow_neg_eq_zero.lean -/

theorem truncBlkRow_neg_eq_zero {U : Type u} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]
    {n m : ℕ} (A : Matrix (Fin n) (Fin m) (SkewL U)) (i : ℕ) {u : ℤ} (hu : u < 0)
    {q : Fin (n * i)} (hq : lowerDeg A ≤ (q.modNat : ℕ)) (j : Fin m) :
    truncBlkRow A i u q j = 0 := by
  simp only [truncBlkRow, coeffMat_apply]
  have h : u - (q.modNat : ℤ) < -(lowerDeg A : ℤ) := by
    have h1 : (lowerDeg A : ℤ) ≤ (q.modNat : ℤ) := by exact_mod_cast hq
    omega
  rw [coeffElt_eq_zero_of_lt_lowerDeg A _ _ h, smul_zero]

/- copy of NaturalExtension/truncBlkCol_ge_eq_zero.lean -/

theorem truncBlkCol_ge_eq_zero {U : Type u} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]
    {m k : ℕ} (B : Matrix (Fin m) (Fin k) (SkewL U)) (i : ℕ) {u : ℤ} (hu : (i : ℤ) ≤ u)
    {p : Fin (k * i)} (hp : lowerDeg B + (p.modNat : ℕ) < i) (j : Fin m) :
    truncBlkCol B i u j p = 0 := by
  rw [truncBlkCol]
  -- The relevant coefficient degree `p.modNat - u` lies below `-lowerDeg B`, hence vanishes.
  have hk : ((p.modNat : ℤ) - u) < -(lowerDeg B : ℤ) := by
    have h2 : (lowerDeg B : ℤ) + (p.modNat : ℤ) < (i : ℤ) := by
      omega
    omega
  rw [coeffMat_apply, coeffElt_eq_zero_of_lt_lowerDeg B j p.divNat hk, smul_zero]

/- copy of NaturalExtension/trunc_mul_concat.lean -/

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



open Matrix

/-- The `(x, l)` entry of the row block at intermediate degree `u + r`, where `r = x.modNat`. -/
lemma truncBlkRow_apply_add {U : Type u} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]
    {n m : ℕ} (A : Matrix (Fin n) (Fin m) (SkewL U)) (i : ℕ) (u : ℤ)
    (x : Fin (n * i)) (l : Fin m) :
    truncBlkRow A i (u + (x.modNat : ℤ)) x l =
      (Multiplicative.ofAdd ((x.modNat : ℤ))) • coeffElt (A x.divNat l) u := by
  have h : (u + (x.modNat : ℤ)) - (x.modNat : ℤ) = u := by ring
  simp only [truncBlkRow, coeffMat_apply, h]

/-- The `(l, y)` entry of the column block at intermediate degree `u + r`, for any shift `r`. -/
lemma truncBlkCol_apply_add {U : Type u} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]
    {m k : ℕ} (B : Matrix (Fin m) (Fin k) (SkewL U)) (i : ℕ) (u r : ℤ)
    (l : Fin m) (y : Fin (k * i)) :
    truncBlkCol B i (u + r) l y =
      (Multiplicative.ofAdd (u + r)) • coeffElt (B l y.divNat) ((y.modNat : ℤ) - r - u) := by
  have h : (y.modNat : ℤ) - (u + r) = (y.modNat : ℤ) - r - u := by ring
  simp only [truncBlkCol, coeffMat_apply, h]

/-- Entrywise form of the block decomposition: the `(x, y)` entry of `trunc i (A * B)` is the sum
of the entrywise block products over the degrees `v` occurring in `A` (i.e. `v ∈ [-lowerDeg A,
upperDeg A]`), shifted by `x.modNat`. -/
theorem trunc_mul_apply_eq_sum {U : Type u} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]
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

theorem trunc_mul_concat {U : Type u} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]
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

/- copy of NaturalExtension/rk_trunc_mul_sub_le.lean -/

/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Rank bound for the truncation defect `trunc i (A * B) - trunc i A * trunc i B`

This file proves `rk_trunc_mul_sub_le`: for a Sylvester rank function `rk` on a ring `U`, matrices
`A`, `B` over the skew Laurent polynomial ring `SkewL U` and any `i : ℕ`,

`rk (trunc i (A * B) - trunc i A * trunc i B) ≤ k * lowerDeg B + n * lowerDeg A`.

The truncation `trunc i A` is the block Toeplitz matrix of right multiplication by `A` on the
truncated module `(U[t;τ]/t^i U[t;τ])^n`.  Its product with `trunc i B` keeps only the
intermediate degrees `u ∈ [0,i)`, whereas `trunc i (A*B)` corresponds to summing over *all*
intermediate degrees `u ∈ ℤ`; the difference is analysed in `TruncDefect.lean`.  There are two
kinds of surplus degrees:

* `u < 0`: the corresponding summand `truncBlkRow A i u * truncBlkCol B i u` can only be nonzero
  on the rows `q` with `(q.modNat : ℕ) < lowerDeg A` — at most `n * lowerDeg A` rows;
* `u ≥ i`: it can only be nonzero on the columns `p` with `i ≤ lowerDeg B + (p.modNat : ℕ)` —
  at most `k * lowerDeg B` columns.

The rank is subadditive, bounded by the number of rows / columns of the support, and the two
bounds add up to the stated estimate.
-/



open Matrix

/-- Membership in the finset `truncRange i = {0, …, i-1}` of intermediate degrees. -/
theorem mem_truncRange {i : ℕ} {u : ℤ} : u ∈ truncRange i ↔ 0 ≤ u ∧ u < (i : ℤ) := by
  rw [truncRange, Finset.mem_image]
  constructor
  · rintro ⟨v, -, hv⟩
    subst hv
    refine ⟨Int.natCast_nonneg _, ?_⟩
    exact_mod_cast v.isLt
  · rintro ⟨h0, hlt⟩
    refine ⟨⟨u.toNat, ?_⟩, Finset.mem_univ _, ?_⟩
    · have h1 : (u.toNat : ℤ) = u := Int.toNat_of_nonneg h0
      have h2 : (u.toNat : ℤ) < (i : ℤ) := by rw [h1]; exact hlt
      exact_mod_cast h2
    · exact Int.toNat_of_nonneg h0

theorem rk_trunc_mul_sub_le {U : Type u} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]
    (rk : SylvesterRank U) {n m k : ℕ}
    (A : Matrix (Fin n) (Fin m) (SkewL U)) (B : Matrix (Fin m) (Fin k) (SkewL U)) (i : ℕ) :
    rk.rk (n * i) (k * i) (trunc i (A * B) - trunc i A * trunc i B) ≤
      (k : ℝ) * (lowerDeg B : ℝ) + (n : ℝ) * (lowerDeg A : ℝ) := by
  classical
  rcases Nat.eq_zero_or_pos i with hi | hi
  · subst hi
    have h0 : (trunc 0 (A * B) - trunc 0 A * trunc 0 B :
        Matrix (Fin (n * 0)) (Fin (k * 0)) U) = 0 := by
      ext q p
      exact absurd q.isLt (by simp)
    rw [h0, rk.rk_zero]
    positivity
  · set F : ℤ → Matrix (Fin (n * i)) (Fin (k * i)) U :=
      fun u => truncBlkRow A i u * truncBlkCol B i u with hF
    have hconcat : trunc i (A * B) = ∑ u ∈ defectRange A B i, F u := trunc_mul_concat A B i
    have hmul : trunc i A * trunc i B = ∑ u ∈ truncRange i, F u := by
      rw [trunc_mul_eq_sum A B i, truncRange]
      exact (Finset.sum_image (f := F) (s := (Finset.univ : Finset (Fin i)))
        (g := fun v : Fin i => ((v : ℕ) : ℤ))
        (fun a _ b _ hab =>
          Fin.ext (Int.ofNat.inj (show ((a : ℕ) : ℤ) = ((b : ℕ) : ℤ) from hab)))).symm
    have hP : (defectRange A B i).filter (fun u : ℤ => 0 ≤ u ∧ u < (i : ℤ)) = truncRange i := by
      ext u
      rw [Finset.mem_filter, mem_truncRange]
      constructor
      · rintro ⟨-, h⟩; exact h
      · intro h
        refine ⟨?_, h⟩
        rw [defectRange, Finset.mem_Icc]
        omega
    have hfilter : (defectRange A B i).filter (fun x : ℤ => ¬ (0 ≤ x ∧ x < (i : ℤ)))
        = negRange A B i ∪ posRange A B i := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_union, negRange, posRange]
      constructor
      · rintro ⟨hB, hn⟩
        by_cases hx : x < 0
        · exact Or.inl ⟨hB, hx⟩
        · refine Or.inr ⟨hB, ?_⟩
          by_contra hx2
          exact hn ⟨by omega, by omega⟩
      · rintro (⟨hB, hx⟩ | ⟨hB, hx⟩)
        · exact ⟨hB, by omega⟩
        · exact ⟨hB, by omega⟩
    have hdisj : Disjoint (negRange A B i) (posRange A B i) := by
      rw [Finset.disjoint_left]
      intro u hu1 hu2
      rw [negRange, Finset.mem_filter] at hu1
      rw [posRange, Finset.mem_filter] at hu2
      omega
    have hE : trunc i (A * B) - trunc i A * trunc i B
        = (∑ u ∈ negRange A B i, F u) + (∑ u ∈ posRange A B i, F u) := by
      rw [hconcat, hmul, ← hP]
      have h := Finset.sum_filter_add_sum_filter_not (defectRange A B i)
        (fun u : ℤ => 0 ≤ u ∧ u < (i : ℤ)) F
      rw [hfilter, Finset.sum_union hdisj] at h
      rw [← h]
      abel
    have hlow : ∀ q : Fin (n * i), q ∉ Set.range (lowRowEmbed n (lowerDeg A) i) →
        ∀ p : Fin (k * i), (∑ u ∈ negRange A B i, F u) q p = 0 := by
      intro q hq p
      have hq' : ¬ ((q.modNat : ℕ) < lowerDeg A) := fun h =>
        hq (((lowRowEmbed_spec n (lowerDeg A) i).2 q).mpr h)
      have hqa : lowerDeg A ≤ (q.modNat : ℕ) := by omega
      rw [Matrix.sum_apply]
      refine Finset.sum_eq_zero fun u hu => ?_
      simp only [hF]
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun j _ => ?_
      have hu' : u < 0 := by
        have hmem : u ∈ negRange A B i := hu
        rw [negRange, Finset.mem_filter] at hmem
        exact hmem.2
      rw [truncBlkRow_neg_eq_zero A i hu' hqa j, zero_mul]
    have hhigh : ∀ p : Fin (k * i), p ∉ Set.range (highColEmbed k (lowerDeg B) i) →
        ∀ q : Fin (n * i), (∑ u ∈ posRange A B i, F u) q p = 0 := by
      intro p hp q
      have hp' : ¬ (i ≤ lowerDeg B + (p.modNat : ℕ)) := fun h =>
        hp (((highColEmbed_spec k (lowerDeg B) i).2 p).mpr h)
      have hpb : lowerDeg B + (p.modNat : ℕ) < i := by omega
      rw [Matrix.sum_apply]
      refine Finset.sum_eq_zero fun u hu => ?_
      simp only [hF]
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun j _ => ?_
      have hu' : (i : ℤ) ≤ u := by
        have hmem : u ∈ posRange A B i := hu
        rw [posRange, Finset.mem_filter] at hmem
        exact hmem.2
      rw [truncBlkCol_ge_eq_zero B i hu' hpb j, mul_zero]
    have hElow : rk.rk (n * i) (k * i) (∑ u ∈ negRange A B i, F u) ≤
        ((n * min (lowerDeg A) i : ℕ) : ℝ) :=
      rk_le_card_of_rowSupport rk (lowRowEmbed n (lowerDeg A) i)
        (lowRowEmbed_spec n (lowerDeg A) i).1 _ hlow
    have hEhigh : rk.rk (n * i) (k * i) (∑ u ∈ posRange A B i, F u) ≤
        ((k * min (lowerDeg B) i : ℕ) : ℝ) :=
      rk_le_card_of_colSupport rk (highColEmbed k (lowerDeg B) i)
        (highColEmbed_spec k (lowerDeg B) i).1 _ hhigh
    have hmain : rk.rk (n * i) (k * i) (trunc i (A * B) - trunc i A * trunc i B)
        ≤ rk.rk (n * i) (k * i) (∑ u ∈ negRange A B i, F u)
          + rk.rk (n * i) (k * i) (∑ u ∈ posRange A B i, F u) := by
      rw [hE]
      exact RankAPI.rk_add_le rk _ _
    have h1 : ((n * min (lowerDeg A) i : ℕ) : ℝ) ≤ (n : ℝ) * (lowerDeg A : ℝ) := by
      rw [Nat.cast_mul]
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast min_le_left (lowerDeg A) i)
        (Nat.cast_nonneg n)
    have h2 : ((k * min (lowerDeg B) i : ℕ) : ℝ) ≤ (k : ℝ) * (lowerDeg B : ℝ) := by
      rw [Nat.cast_mul]
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast min_le_left (lowerDeg B) i)
        (Nat.cast_nonneg k)
    calc rk.rk (n * i) (k * i) (trunc i (A * B) - trunc i A * trunc i B)
        ≤ _ + _ := hmain
      _ ≤ ((n * min (lowerDeg A) i : ℕ) : ℝ) + ((k * min (lowerDeg B) i : ℕ) : ℝ) :=
          add_le_add hElow hEhigh
      _ ≤ (n : ℝ) * (lowerDeg A : ℝ) + (k : ℝ) * (lowerDeg B : ℝ) := by linarith
      _ = (k : ℝ) * (lowerDeg B : ℝ) + (n : ℝ) * (lowerDeg A : ℝ) := by ring

end Work.ORHughesFree.NaturalExtensionGen.Trunc
