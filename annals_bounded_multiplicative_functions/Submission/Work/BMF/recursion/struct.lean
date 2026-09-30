import Mathlib
import Submission.Work.BMF.recursion.Defs
import Submission.Work.BMF.recursion.card_pair_fibre_sum
import Submission.Work.BMF.recursion.exists_perm_pair
import Submission.Work.BMF.recursion.powerSums_perm

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The case (a) / case (b) split of Wooley's recursion

Structural lemmas for `Work.BMF.recursion_step`:
the matching-pair set is partitioned by whether the "head" is distinct, the mixed part is estimated
by AM-GM over the fibres of the moment map, and the non-distinct part by a union bound.
-/

open Finset
open scoped BigOperators
open LeanEval.NumberTheory.VinogradovMeanValue
open Submission.Vinogradov (powerSums powerSums_eq_iff_matches)

namespace Work.BMF.recursion

noncomputable section

lemma J_eq_solSet (S k Q : ℕ) : J S k Q = ((solSet S k Q).card : ℝ) := rfl

/-- The matching condition is equivalent to equality of moment vectors. -/
lemma matches_iff {S k Q : ℕ} (p : PairSpace S Q) :
    Matches S k Q p ↔ powerSums k p.1 = powerSums k p.2 :=
  (powerSums_eq_iff_matches (k := k) p.1 p.2).symm

/-- The two "mixed" parts of the solution set have the same cardinality (swap the two tuples). -/
lemma mem_solSet {S k Q : ℕ} {p : PairSpace S Q} :
    p ∈ solSet S k Q ↔ Matches S k Q p := by
  simp [solSet]

lemma card_mixed_swap (S k Q : ℕ) (hkS : k ≤ S) :
    headMix2 S k Q hkS = headMix S k Q hkS := by
  classical
  rw [headMix2, headMix]
  apply le_antisymm
  · refine Finset.card_le_card_of_injOn (fun p : PairSpace S Q => (p.2, p.1)) ?_ ?_
    · intro p hp
      obtain ⟨h1, h2a, h2b⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr
        ⟨mem_solSet.mpr (matches_symm (mem_solSet.mp h1)), h2b, h2a⟩
    · intro p hp q hq hpq
      exact Prod.ext (congrArg Prod.snd hpq) (congrArg Prod.fst hpq)
  · refine Finset.card_le_card_of_injOn (fun p : PairSpace S Q => (p.2, p.1)) ?_ ?_
    · intro p hp
      obtain ⟨h1, h2a, h2b⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr
        ⟨mem_solSet.mpr (matches_symm (mem_solSet.mp h1)), h2b, h2a⟩
    · intro p hp q hq hpq
      exact Prod.ext (congrArg Prod.snd hpq) (congrArg Prod.fst hpq)

/-- Cast of a filtered cardinality as a sum of indicators. -/
lemma card_filter_cast (S k Q : ℕ) (P : PairSpace S Q → Prop) [DecidablePred P] :
    (((solSet S k Q).filter P).card : ℝ)
      = ∑ p ∈ solSet S k Q, (if P p then (1 : ℝ) else 0) := by
  rw [Finset.card_filter]
  push_cast
  exact Finset.sum_congr rfl (fun p _ => by split <;> simp)

/-- Partition of the solution count into the three head-distinctness cases. -/
lemma solSet_card_split (S k Q : ℕ) (hkS : k ≤ S) :
    ((solSet S k Q).card : ℝ)
      = (S1pair S k Q hkS : ℝ) + (mixedPair S k Q hkS : ℝ) + (S2pair S k Q hkS : ℝ) := by
  classical
  have hfun : ∀ p ∈ solSet S k Q, (1 : ℝ)
      = (if HD hkS p.1 ∧ HD hkS p.2 then (1 : ℝ) else 0)
        + (if (HD hkS p.1 ∧ ¬ HD hkS p.2) ∨ (¬ HD hkS p.1 ∧ HD hkS p.2) then (1 : ℝ) else 0)
        + (if ¬ HD hkS p.1 ∧ ¬ HD hkS p.2 then (1 : ℝ) else 0) := by
    intro p _
    by_cases a : HD hkS p.1 <;> by_cases b : HD hkS p.2 <;> simp [a, b]
  have h1 : ((solSet S k Q).card : ℝ)
      = ∑ p ∈ solSet S k Q, ((if HD hkS p.1 ∧ HD hkS p.2 then (1 : ℝ) else 0)
        + (if (HD hkS p.1 ∧ ¬ HD hkS p.2) ∨ (¬ HD hkS p.1 ∧ HD hkS p.2) then (1 : ℝ) else 0)
        + (if ¬ HD hkS p.1 ∧ ¬ HD hkS p.2 then (1 : ℝ) else 0)) := by
    rw [show ((solSet S k Q).card : ℝ) = ∑ p ∈ solSet S k Q, (1 : ℝ) by
      rw [Finset.card_eq_sum_ones]; simp]
    exact Finset.sum_congr rfl hfun
  rw [h1, Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [← card_filter_cast S k Q (fun p : PairSpace S Q => HD hkS p.1 ∧ HD hkS p.2),
      ← card_filter_cast S k Q
        (fun p : PairSpace S Q => (HD hkS p.1 ∧ ¬ HD hkS p.2) ∨ (¬ HD hkS p.1 ∧ HD hkS p.2)),
      ← card_filter_cast S k Q (fun p : PairSpace S Q => ¬ HD hkS p.1 ∧ ¬ HD hkS p.2)]
  simp only [S1pair, mixedPair, S2pair]

end

end Work.BMF.recursion
