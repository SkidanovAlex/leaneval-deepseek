import Mathlib
import Submission.Work.EKLC6Core.returnTimeDefs

namespace Work.EKLC6Core

open MeasureTheory Set
open scoped ENNReal

/-- The family of first-hit sets `firstHitSet T Ω ·` of a measurable self-map of a probability
space consists of measurable sets, is pairwise disjoint, and the sums of the real measures of any
finite initial segment are bounded by `1`.

This is the elementary entrance-tower fact behind Kac's inequality: the `n`-th first-hit set
collects the points whose first visit to `Ω` occurs exactly at time `n`, so distinct levels are
disjoint, and a finite union of disjoint levels lies in the whole space of measure `1`. -/
theorem firstHitSet_measurable_and_sum_le_one {X : Type*} [MeasurableSpace X]
    {μ : MeasureTheory.Measure X} [MeasureTheory.IsProbabilityMeasure μ] {T : X → X}
    (hmp : MeasureTheory.MeasurePreserving T μ μ) {Ω : Set X} (hΩ : MeasurableSet Ω) :
    (∀ n : ℕ, MeasurableSet (Work.EKLC6Core.firstHitSet T Ω n)) ∧
      Set.PairwiseDisjoint Set.univ (Work.EKLC6Core.firstHitSet T Ω) ∧
      (∀ N : ℕ, ∑ n ∈ Finset.range N, μ.real (Work.EKLC6Core.firstHitSet T Ω n) ≤ 1) := by
  have hT : Measurable T := hmp.measurable
  -- ### Measurability of every level
  have hmeas : ∀ n : ℕ, MeasurableSet (firstHitSet T Ω n) := by
    intro n
    unfold firstHitSet
    exact (hΩ.preimage (hT.iterate n)).inter
      (MeasurableSet.biInter (s := Finset.range n) ((Finset.range n).countable_toSet)
        (fun b _ => (hΩ.preimage (hT.iterate b)).compl))
  -- ### Pairwise disjointness of distinct levels
  have hpd : Set.PairwiseDisjoint Set.univ (firstHitSet T Ω) := by
    rw [pairwiseDisjoint_iff]
    intro i _ j _ hij
    rcases hij with ⟨x, hx⟩
    rw [mem_inter_iff, mem_firstHitSet, mem_firstHitSet] at hx
    obtain ⟨hxi, hxj⟩ := hx
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact (hxj.2 i hlt) hxi.1
    · exact (hxi.2 j hlt) hxj.1
  refine ⟨hmeas, hpd, ?_⟩
  -- ### The finite sums are bounded by `1`
  intro N
  have hdisj : PairwiseDisjoint (Finset.range N : Set ℕ) (firstHitSet T Ω) :=
    hpd.subset (by intro x _; exact mem_univ x)
  have hfin : ∀ b ∈ Finset.range N, μ (firstHitSet T Ω b) ≠ ∞ := by
    intro b _
    exact ne_top_of_le_ne_top (by simp) (measure_mono (subset_univ _))
  rw [← measureReal_biUnion_finset hdisj (fun b _ => hmeas b) hfin]
  calc μ.real (⋃ b ∈ Finset.range N, firstHitSet T Ω b)
      ≤ μ.real Set.univ := measureReal_mono (subset_univ _) (by simp)
    _ = 1 := by simp [Measure.real]

end Work.EKLC6Core
