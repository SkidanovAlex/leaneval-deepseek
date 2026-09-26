import Mathlib
import Submission.Work.Smooth.SphereJordan.LocalArc.ArcRange
import Submission.Work.Smooth.SphereJordan.LocalArc.MaximalArcRange
import Submission.Work.Smooth.SphereJordan.LocalArc.SecondCountable

/-!
# The chain bound for arc ranges

`chain_bound_of_nested`: if every increasing *sequence* of arc ranges through `x₀` is contained in
an arc range through `x₀` (the nested case), then every *chain* of arc ranges through `x₀` has an
arc-range upper bound.  The reduction uses second countability
(`secondCountableTopology_of_isLocallyArc`) and Lindelöf: the union of the chain is covered by
countably many of its members (`TopologicalSpace.isOpen_iUnion_countable`), which are enumerated
and turned into an increasing sequence by taking finite maxima along the chain.

Together with `exists_isMaximal_of_chain_bounds` this reduces the classification to the nested case
alone.
-/

namespace Work.Smooth.SphereJordan.LocalArc

open Set Function Filter

open scoped Topology

noncomputable section

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]

/-- **The maximum of a non-empty finite subfamily of a chain exists.** -/
theorem exists_max_of_finset_subset {c : Set (Set X)} (hchain : IsChain (· ⊆ ·) c)
    {s : Finset (Set X)} (hs : ∀ U ∈ s, U ∈ c) (hne : s.Nonempty) :
    ∃ U ∈ s, ∀ U' ∈ s, U' ⊆ U := by
  induction s using Finset.induction with
  | empty => exact absurd hne Finset.not_nonempty_empty
  | insert a s' ha ih =>
      rcases s'.eq_empty_or_nonempty with h | h
      · refine ⟨a, Finset.mem_insert_self a s', fun U' hU' => ?_⟩
        have hUa : U' = a := by simpa [h] using hU'
        rw [hUa]
      · obtain ⟨M, hM, hmax⟩ := ih (fun U hU => hs U (Finset.mem_insert_of_mem hU)) h
        rcases eq_or_ne a M with haeq | hne
        · refine ⟨a, Finset.mem_insert_self a s', fun U' hU' => ?_⟩
          rcases Finset.mem_insert.mp hU' with rfl | hU''
          · exact subset_rfl
          · rw [haeq]; exact hmax U' hU''
        · rcases hchain (hs a (Finset.mem_insert_self a s'))
            (hs M (Finset.mem_insert_of_mem hM)) hne with hsub | hsub
          · refine ⟨M, Finset.mem_insert_of_mem hM, fun U' hU' => ?_⟩
            rcases Finset.mem_insert.mp hU' with rfl | hU''
            · exact hsub
            · exact hmax U' hU''
          · refine ⟨a, Finset.mem_insert_self a s', fun U' hU' => ?_⟩
            rcases Finset.mem_insert.mp hU' with rfl | hU''
            · exact subset_rfl
            · exact (hmax U' hU'').trans hsub

/-- **A finite union of elements of a chain of arc ranges is an arc range.** -/
theorem isArcRange_biUnion_finset {x₀ : X} {c : Set (Set X)} (hchain : IsChain (· ⊆ ·) c)
    (hc : ∀ U ∈ c, IsArcRange x₀ U) {s : Finset (Set X)} (hs : ∀ U ∈ s, U ∈ c)
    (hne : s.Nonempty) : IsArcRange x₀ (⋃ U ∈ s, U) := by
  obtain ⟨U, hU, hmax⟩ := exists_max_of_finset_subset hchain hs hne
  have heq : (⋃ U' ∈ s, U') = U := by
    refine subset_antisymm (Set.iUnion₂_subset fun U' hU' => hmax U' hU') ?_
    exact Set.subset_iUnion₂ (s := fun U' (_ : U' ∈ s) => U') U hU
  rw [heq]
  exact hc U (hs U hU)

/-- **The chain bound follows from the nested case.** -/
theorem chain_bound_of_nested (H : Work.Smooth.SphereJordan.IsLocallyArc X) (x₀ : X)
    (hnested : ∀ U : ℕ → Set X, (∀ n, IsArcRange x₀ (U n)) → Monotone U →
      ∃ V : Set X, IsArcRange x₀ V ∧ ∀ n, U n ⊆ V) :
    ∀ c : Set (Set X), (∀ U ∈ c, IsArcRange x₀ U) → IsChain (· ⊆ ·) c →
      ∃ ub : Set X, IsArcRange x₀ ub ∧ ∀ U ∈ c, U ⊆ ub := by
  haveI := secondCountableTopology_of_isLocallyArc H
  intro c hc hchain
  have hbase : IsArcRange x₀ (Work.Smooth.SphereJordan.chartOf H x₀).V :=
    ⟨(Work.Smooth.SphereJordan.chartOf H x₀).map,
      (Work.Smooth.SphereJordan.chartOf H x₀).continuous_map,
      (Work.Smooth.SphereJordan.chartOf H x₀).injective_map,
      Work.Smooth.SphereJordan.ArcChart.map_zero _,
      Work.Smooth.SphereJordan.ArcChart.range_map _⟩
  rcases c.eq_empty_or_nonempty with rfl | hcne
  · exact ⟨_, hbase, by simp⟩
  obtain ⟨T, hTcount, hTcover⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun U : c => (U : Set X)) (fun U => (hc U.1 U.2).isOpen H)
  have hTne : T.Nonempty := by
    obtain ⟨U, hU⟩ := hcne
    have hxU : x₀ ∈ U := (hc U hU).mem
    have h1 : x₀ ∈ ⋃ i ∈ T, (i : Set X) := by
      rw [hTcover]
      exact Set.mem_iUnion.mpr ⟨⟨U, hU⟩, hxU⟩
    simp only [Set.mem_iUnion] at h1
    obtain ⟨i, hi, -⟩ := h1
    exact ⟨i, hi⟩
  obtain ⟨f, hf⟩ := hTcount.exists_eq_range hTne
  let g : ℕ → Set X := fun n => (f n : Set X)
  let V : ℕ → Set X := fun n => ⋃ U ∈ (Finset.range (n + 1)).image g, U
  have hg : ∀ n, IsArcRange x₀ (g n) := fun n => hc (f n).1 (f n).2
  have hV : ∀ n, IsArcRange x₀ (V n) := by
    intro n
    refine isArcRange_biUnion_finset hchain (fun U hU => hc U hU) (fun U hU => ?_)
      ⟨g 0, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (Nat.succ_pos n), rfl⟩⟩
    obtain ⟨k, -, hkg⟩ := Finset.mem_image.mp hU
    rw [← hkg]
    exact (f k).2
  have hmono : Monotone V := by
    intro n m hnm
    refine Set.iUnion₂_subset fun U hU => Set.subset_iUnion₂_of_subset U ?_ subset_rfl
    exact Finset.image_subset_image (f := g) (Finset.range_mono (Nat.succ_le_succ hnm)) hU
  obtain ⟨Vtop, hVtop, hVtopsub⟩ := hnested V hV hmono
  refine ⟨Vtop, hVtop, fun U hU => ?_⟩
  have h1 : U ⊆ ⋃ i ∈ T, (i : Set X) := by
    rw [hTcover]
    exact Set.subset_iUnion (fun i : c => (i : Set X)) ⟨U, hU⟩
  have h2 : (⋃ i ∈ T, (i : Set X)) ⊆ ⋃ n, V n := by
    refine Set.iUnion₂_subset fun i hi => ?_
    rw [hf] at hi
    obtain ⟨k, hk⟩ := hi
    rw [← hk]
    exact (Set.subset_iUnion₂ (s := fun W (_ : W ∈ (Finset.range (k + 1)).image g) => W)
        (g k) (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (Nat.lt_succ_self k), rfl⟩)).trans
      (Set.subset_iUnion V k)
  exact h1.trans (h2.trans (Set.iUnion_subset hVtopsub))

/-- **The classification from the nested case.** -/
theorem circle_param_of_nested (H : Work.Smooth.SphereJordan.IsLocallyArc X) [PreconnectedSpace X]
    (x₀ : X)
    (hnested : ∀ U : ℕ → Set X, (∀ n, IsArcRange x₀ (U n)) → Monotone U →
      ∃ V : Set X, IsArcRange x₀ V ∧ ∀ n, U n ⊆ V) :
    ∃ γ : ℝ → X, Continuous γ ∧ Function.Periodic γ (2 * Real.pi) ∧
      Set.InjOn γ (Set.Ico 0 (2 * Real.pi)) ∧ Set.range γ = Set.univ :=
  circle_param_of_exists_maximal H (exists_isMaximal_of_chain_bounds x₀
    (chain_bound_of_nested H x₀ hnested))

end

end Work.Smooth.SphereJordan.LocalArc
