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
import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.Defs
import Submission.Work.ORHughesFree.NaturalExtension.TruncDefect
import Submission.Work.ORHughesFree.SylvesterRank
import Submission.Work.ORHughesFree.RankAPI.rk_add_le
import Submission.Work.ORHughesFree.RankAPI.rk_le_left
import Submission.Work.ORHughesFree.RankAPI.rk_le_right
import Submission.Work.ORHughesFree.RankAPI.rk_submatrix
import Submission.Work.ORHughesFree.NaturalExtension.trunc_mul_eq_sum
import Submission.Work.ORHughesFree.NaturalExtension.trunc_mul_concat
import Submission.Work.ORHughesFree.NaturalExtension.truncBlkRow_neg_eq_zero
import Submission.Work.ORHughesFree.NaturalExtension.truncBlkCol_ge_eq_zero
import Submission.Work.ORHughesFree.NaturalExtension.rk_le_card_of_rowSupport
import Submission.Work.ORHughesFree.NaturalExtension.rk_le_card_of_colSupport
import Submission.Work.ORHughesFree.NaturalExtension.lowRowEmbed_spec
import Submission.Work.ORHughesFree.NaturalExtension.highColEmbed_spec

set_option autoImplicit false

namespace Work.ORHughesFree.NaturalExtension

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

theorem rk_trunc_mul_sub_le {U : Type} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]
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

end Work.ORHughesFree.NaturalExtension
