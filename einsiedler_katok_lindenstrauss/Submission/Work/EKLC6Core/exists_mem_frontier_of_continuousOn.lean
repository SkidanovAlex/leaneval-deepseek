import Mathlib

namespace Work.EKLC6Core

/-- A continuous path `γ : ℝ → X`, continuous on `[0,1]`, that starts inside a set `S` and ends
outside it must meet the frontier of `S`. -/
theorem exists_mem_frontier_of_continuousOn {X : Type*} [TopologicalSpace X] {γ : ℝ → X}
    {S : Set X} (hγ : ContinuousOn γ (Set.Icc (0 : ℝ) 1)) (h0 : γ 0 ∈ S) (h1 : γ 1 ∉ S) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ frontier S := by
  -- Suppose the path avoids the frontier of `S`.
  by_contra hcon
  push Not at hcon
  -- The image of `[0,1]` under `γ` is (pre)connected.
  have hA : IsPreconnected (γ '' Set.Icc (0 : ℝ) 1) := isPreconnected_Icc.image γ hγ
  -- It is contained in the two disjoint open sets `interior S` and `interior Sᶜ`.
  have hsub : γ '' Set.Icc (0 : ℝ) 1 ⊆ interior S ∪ interior Sᶜ := by
    rintro x ⟨t, ht, rfl⟩
    rw [← compl_frontier_eq_union_interior]
    exact hcon t ht
  have hdisj : Disjoint (interior S) (interior Sᶜ) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact (interior_subset hx') (interior_subset hx)
  -- A connected set lying in a disjoint union of two open sets lies in one of them.
  rcases hA.subset_or_subset isOpen_interior isOpen_interior hdisj hsub with hcase | hcase
  -- If it lies in `interior S`, the endpoint lies in `S`: contradiction.
  · exact h1 (interior_subset (hcase ⟨1, by norm_num, rfl⟩))
  -- If it lies in `interior Sᶜ`, the starting point lies outside `S`: contradiction.
  · exact (interior_subset (hcase ⟨0, by norm_num, rfl⟩)) h0

end Work.EKLC6Core
