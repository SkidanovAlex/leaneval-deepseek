import Mathlib
import Submission.Work.MassTransferenceAlt.Basic

namespace Work.MassTransferenceAlt.Greedy

open Work.MassTransferenceAlt

/-- **Greedy disjoint subfamily.** For a finite family of closed intervals with
nonnegative radii there is a pairwise disjoint subfamily such that every interval of the
family is contained in the threefold dilation of a member of the subfamily. -/
theorem exists_disjoint_subfamily (x r : ℕ → ℝ) (s : Finset ℕ) (hr : ∀ i ∈ s, 0 ≤ r i) :
    ∃ G : Finset ℕ, G ⊆ s ∧
      (∀ i ∈ G, ∀ j ∈ G, i ≠ j → Disjoint (Work.MassTransferenceAlt.Iv (x i) (r i)) (Work.MassTransferenceAlt.Iv (x j) (r j))) ∧
      (∀ i ∈ s, ∃ j ∈ G, Work.MassTransferenceAlt.Iv (x i) (r i) ⊆ Work.MassTransferenceAlt.Iv (x j) (3 * r j)) := by
  classical
  -- Greedy: repeatedly take an interval of maximal radius among those that are disjoint
  -- from all previously selected ones.  Every discarded interval then meets a selected
  -- one of no smaller radius, hence is covered by its threefold dilation.
  have key : ∀ n, ∀ s : Finset ℕ, s.card = n → (∀ i ∈ s, 0 ≤ r i) →
      ∃ G : Finset ℕ, G ⊆ s ∧
        (∀ i ∈ G, ∀ j ∈ G, i ≠ j → Disjoint (Iv (x i) (r i)) (Iv (x j) (r j))) ∧
        (∀ i ∈ s, ∃ j ∈ G, Iv (x i) (r i) ⊆ Iv (x j) (3 * r j)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s hcard hrs
      rcases s.eq_empty_or_nonempty with hs | hsne
      · subst hs
        exact ⟨∅, Finset.empty_subset _, by simp, by simp⟩
      · -- pick an index of maximal radius
        obtain ⟨j, hjs, hjmax⟩ := Finset.exists_max_image s r hsne
        -- the intervals of `s` that are disjoint from the chosen one
        set T := s.filter (fun i => Disjoint (Iv (x i) (r i)) (Iv (x j) (r j))) with hT
        have hTsub : T ⊆ s := Finset.filter_subset _ _
        have hjT : j ∉ T := by
          intro hj
          rw [hT, Finset.mem_filter] at hj
          obtain ⟨hj1, hj2⟩ := hj
          obtain ⟨z, hz⟩ := Iv_nonempty (hrs j hjs)
          exact (Set.disjoint_left.mp hj2) hz hz
        have hTcard : T.card < s.card := by
          refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hTsub, ?_⟩)
          intro hEq
          rw [hEq] at hjT
          exact hjT hjs
        obtain ⟨G', hG'subT, hG'disj, hG'cov⟩ :=
          ih T.card (hcard ▸ hTcard) T rfl (fun i hi => hrs i (hTsub hi))
        refine ⟨insert j G', ?_, ?_, ?_⟩
        · -- the subfamily sits inside `s`
          intro i hi
          rw [Finset.mem_insert] at hi
          rcases hi with rfl | hi
          · exact hjs
          · exact hTsub (hG'subT hi)
        · -- pairwise disjointness
          intro i hi k hk hik
          rw [Finset.mem_insert] at hi hk
          rcases hi with rfl | hi
          · rcases hk with rfl | hk
            · exact absurd rfl hik
            · exact disjoint_comm.mp (Finset.mem_filter.mp (hG'subT hk)).2
          · rcases hk with rfl | hk
            · exact (Finset.mem_filter.mp (hG'subT hi)).2
            · exact hG'disj i hi k hk hik
        · -- covering
          intro i his
          by_cases hiT : i ∈ T
          · obtain ⟨k, hkG', hsub⟩ := hG'cov i hiT
            exact ⟨k, Finset.mem_insert_of_mem hkG', hsub⟩
          · -- `i` meets the maximal interval `j`, and `r i ≤ r j`
            have hnd : ¬ Disjoint (Iv (x i) (r i)) (Iv (x j) (r j)) := by
              intro hd
              exact hiT (by rw [hT]; exact Finset.mem_filter.mpr ⟨his, hd⟩)
            refine ⟨j, Finset.mem_insert_self j G', ?_⟩
            obtain ⟨z, hzi, hzj⟩ := Set.not_disjoint_iff.mp hnd
            rw [mem_Iv] at hzi hzj
            have hdist : |x i - x j| ≤ r i + r j := by
              calc |x i - x j| = |(x i - z) + (z - x j)| := by ring_nf
                _ ≤ |x i - z| + |z - x j| := abs_add_le _ _
                _ ≤ r i + r j := by
                    have h1 : |x i - z| = |z - x i| := abs_sub_comm _ _
                    linarith
            have hri : r i ≤ r j := hjmax i his
            refine Iv_subset_Iv ?_
            linarith
  exact key s.card s rfl hr

end Work.MassTransferenceAlt.Greedy
