import Mathlib

/-!
# Double-counting identity for subset pairs

For a finite set `X` and naturals `u v`, summing a function `F(U∪V)` over pairs
`(U,V)` with `|U| = u`, `U ⊆ X`, `|V| = v`, `V ⊆ X\U` equals `C(u+v,u)` times the
sum over `(u+v)`-subsets `W`.
-/
open Finset
open scoped BigOperators

namespace Submission.PairSum

variable {α : Type*} [DecidableEq α]

/-- subsets of `X` of cardinality `w` -/
def cardSubsets (X : Finset α) (w : ℕ) : Finset (Finset α) := X.powersetCard w

/-- the double-counting coefficient identity `C(n,u+v)·C(u+v,u) = C(n,u)·C(n-u,v)`. -/
lemma choose_mul_eq {n u v : ℕ} (huv : u + v ≤ n) :
    n.choose (u + v) * (u + v).choose u = n.choose u * (n - u).choose v := by
  have _ := huv
  have h := Nat.choose_mul (n := n) (k := u + v) (s := u) (by omega : u ≤ u + v)
  simpa [Nat.add_sub_cancel_left] using h

/-- membership facts: V ∈ cardSubsets (X\U) v implies V ⊆ X, disjoint from U. -/
lemma cardSubsets_sdiff_mem {X U V : Finset α} {v : ℕ} (hV : V ∈ cardSubsets (X \ U) v) :
    V ⊆ X ∧ Disjoint U V := by
  have hV' : V ⊆ X \ U ∧ V.card = v := by
    simpa [cardSubsets] using (Finset.mem_powersetCard.mp hV)
  constructor
  · exact hV'.1.trans Finset.sdiff_subset
  · exact (Finset.subset_sdiff.mp hV'.1).2.symm

/-- `(U∪V).card = u + v` and `U ∩ V = ∅` from membership. -/
lemma union_card {X U V : Finset α} {u v : ℕ}
    (hU : U ∈ cardSubsets X u) (hV : V ∈ cardSubsets (X \ U) v) :
    (U ∪ V).card = u + v := by
  have hU' : U ⊆ X ∧ U.card = u := by
    simpa [cardSubsets] using (Finset.mem_powersetCard.mp hU)
  have hV' : V ⊆ X \ U ∧ V.card = v := by
    simpa [cardSubsets] using (Finset.mem_powersetCard.mp hV)
  rw [Finset.card_union_of_disjoint (cardSubsets_sdiff_mem hV).2, hU'.2, hV'.2]

/-- A `(u+v)`-subset `W` decomposes as `U ∪ V` with `V = W \ U`. -/
lemma decompose {X W U : Finset α} {u v : ℕ}
    (hW : W ∈ cardSubsets X (u + v)) (hU : U ∈ cardSubsets W u) :
    U ∈ cardSubsets X u ∧ (W \ U) ∈ cardSubsets (X \ U) v := by
  have hW' : W ⊆ X ∧ W.card = u + v := by
    simpa [cardSubsets] using (Finset.mem_powersetCard.mp hW)
  have hU' : U ⊆ W ∧ U.card = u := by
    simpa [cardSubsets] using (Finset.mem_powersetCard.mp hU)
  constructor
  · rw [cardSubsets, Finset.mem_powersetCard]
    exact ⟨hU'.1.trans hW'.1, hU'.2⟩
  · rw [cardSubsets, Finset.mem_powersetCard]
    constructor
    · exact Finset.sdiff_subset_sdiff hW'.1 (subset_refl U)
    · rw [Finset.card_sdiff_of_subset hU'.1, hW'.2, hU'.2, Nat.add_sub_cancel_left]

/-- Main identity. -/
lemma pair_sum_eq {X : Finset α} {u v : ℕ} {F : Finset α → ℝ}
    (hsub : v ≤ X.card - u) (hG : ∀ ⦃U V W : Finset α⦄, W = U ∪ V →
      F W = F (U ∪ V)) :
    (∑ U ∈ cardSubsets X u, ∑ V ∈ cardSubsets (X \ U) v, F (U ∪ V)) =
      (u + v).choose u * (∑ W ∈ cardSubsets X (u + v), F W) := by
  have _ := hsub
  have _ := hG
  let sA := (cardSubsets X u).sigma (fun U : Finset α => cardSubsets (X \ U) v)
  let sB := (cardSubsets X (u + v)).sigma (fun W : Finset α => cardSubsets W u)
  have hLHS : (∑ U ∈ cardSubsets X u, ∑ V ∈ cardSubsets (X \ U) v, F (U ∪ V)) =
        (∑ p ∈ sA, F (p.1 ∪ p.2)) := by
    dsimp [sA]
    symm
    rw [Finset.sum_sigma]
  have hAB : (∑ p ∈ sA, F (p.1 ∪ p.2)) = (∑ q ∈ sB, F q.1) := by
    -- bijection ⟨U,V⟩ ↦ ⟨U∪V,U⟩ with inverse ⟨W,U⟩ ↦ ⟨U,W\U⟩
    refine Finset.sum_bij' (s := sA) (t := sB) (f := fun p => F (p.1 ∪ p.2)) (g := fun q => F q.1)
      (fun p hp => ⟨p.1 ∪ p.2, p.1⟩)
      (fun q hq => ⟨q.2, q.1 \ q.2⟩)
      ?hi ?hj ?negL ?negR ?hsum
    · intro p hp
      rw [Finset.mem_sigma] at hp
      rw [Finset.mem_sigma]
      have hp1 : p.1 ⊆ X ∧ p.1.card = u := by
        simpa [cardSubsets] using (Finset.mem_powersetCard.mp hp.1)
      have hp2 : p.2 ⊆ X \ p.1 ∧ p.2.card = v := by
        simpa [cardSubsets] using (Finset.mem_powersetCard.mp hp.2)
      constructor
      · rw [cardSubsets, Finset.mem_powersetCard]
        constructor
        · exact Finset.union_subset hp1.1 (hp2.1.trans Finset.sdiff_subset)
        · rw [Finset.card_union_of_disjoint (cardSubsets_sdiff_mem hp.2).2, hp1.2, hp2.2]
      · rw [cardSubsets, Finset.mem_powersetCard]
        exact ⟨Finset.subset_union_left, hp1.2⟩
    · intro q hq
      rw [Finset.mem_sigma] at hq
      rw [Finset.mem_sigma]
      have hq1 : q.1 ⊆ X ∧ q.1.card = u + v := by
        simpa [cardSubsets] using (Finset.mem_powersetCard.mp hq.1)
      have hq2 : q.2 ⊆ q.1 ∧ q.2.card = u := by
        simpa [cardSubsets] using (Finset.mem_powersetCard.mp hq.2)
      constructor
      · rw [cardSubsets, Finset.mem_powersetCard]
        exact ⟨hq2.1.trans hq1.1, hq2.2⟩
      · rw [cardSubsets, Finset.mem_powersetCard]
        constructor
        · exact Finset.sdiff_subset_sdiff hq1.1 (subset_refl q.2)
        · rw [Finset.card_sdiff_of_subset hq2.1, hq1.2, hq2.2, Nat.add_sub_cancel_left]
    · intro p hp
      rw [Finset.mem_sigma] at hp
      have hd : Disjoint p.1 p.2 := (cardSubsets_sdiff_mem hp.2).2
      dsimp
      congr 1
      exact Finset.union_sdiff_cancel_left hd
    · intro q hq
      rw [Finset.mem_sigma] at hq
      have hq2mem : q.2 ⊆ q.1 ∧ q.2.card = u := by
        simpa [cardSubsets] using (Finset.mem_powersetCard.mp hq.2)
      dsimp
      congr 1
      exact Finset.union_sdiff_of_subset hq2mem.1
    · intro p hp
      rfl
  have hB : (∑ q ∈ sB, F q.1) =
        (u + v).choose u * (∑ W ∈ cardSubsets X (u + v), F W) := by
    calc
      (∑ q ∈ sB, F q.1)
          = ∑ W ∈ cardSubsets X (u + v), ∑ U ∈ cardSubsets W u, F W := by
              rw [Finset.sum_sigma]
      _ = ∑ W ∈ cardSubsets X (u + v), (cardSubsets W u).card • F W := by
              apply Finset.sum_congr rfl
              intro W hW
              exact Finset.sum_const (F W)
      _ = ∑ W ∈ cardSubsets X (u + v), ((u + v).choose u : ℝ) * F W := by
              apply Finset.sum_congr rfl
              intro W hW
              have hWcard : W.card = u + v := (Finset.mem_powersetCard.mp hW).2
              change (W.powersetCard u).card • F W = ((u + v).choose u : ℝ) * F W
              rw [Finset.card_powersetCard, hWcard]
              rw [nsmul_eq_mul]
      _ = (u + v).choose u * (∑ W ∈ cardSubsets X (u + v), F W) := by
              rw [← Finset.mul_sum]
  calc
    (∑ U ∈ cardSubsets X u, ∑ V ∈ cardSubsets (X \ U) v, F (U ∪ V))
        = (∑ p ∈ sA, F (p.1 ∪ p.2)) := hLHS
    _ = (∑ q ∈ sB, F q.1) := hAB
    _ = (u + v).choose u * (∑ W ∈ cardSubsets X (u + v), F W) := hB

end Submission.PairSum
