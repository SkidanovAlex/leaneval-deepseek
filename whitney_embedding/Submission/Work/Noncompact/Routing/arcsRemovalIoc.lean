import Mathlib
import Submission.Work.Noncompact.Routing.arcs_removal
import Submission.Work.Noncompact.CompressionTube.spike_removal

/-!
# Arc removal when the arc is only inside `C` off its initial point

`Work.Noncompact.Routing.isPreconnected_sdiff_arc_Ioc`: the complement of an arc in an open
preconnected `C` of an `n`-manifold (`n ≥ 2`) is preconnected *provided the arc lies in `C` on
`Ioc 0 1`* — its initial point `γ 0` may lie on `∂C`.  This is the form the routing needs: the
piece's trace in the next corridor is a *half-open* arc whose initial point is the junction's germ
endpoint, which is removed separately.

The proof is the case split of the review:
* if `γ 0 ∈ C` the whole arc is in `C` and the existing `isPreconnected_sdiff_image_arc` applies;
* if `γ 0 ∉ C`, then `C ∩ γ '' Icc = C ∩ γ '' Ioc`, so
  `C \ γ '' Icc = C \ γ '' Ioc` and `Work.Noncompact.CompressionTube.spike_removal` (PROVED)
  applies with `σ := γ`.
-/

namespace Work.Noncompact.Routing

open Set Topology

/-- **Arc removal with the initial point possibly on the boundary.** -/
theorem isPreconnected_sdiff_arc_Ioc {n : ℕ} (hn : 2 ≤ n) {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {C : Set M} (hC : IsOpen C) (hCc : IsPreconnected C) {γ : ℝ → M} (hγ : Continuous γ)
    (hinj : Set.InjOn γ (Set.Icc (0:ℝ) 1))
    (hγC : ∀ t : ℝ, t ∈ Set.Ioc (0:ℝ) 1 → γ t ∈ C) :
    IsPreconnected (C \ γ '' Set.Icc (0:ℝ) 1) := by
  by_cases h0 : γ 0 ∈ C
  · have hγC' : ∀ t ∈ Set.Icc (0:ℝ) 1, γ t ∈ C := by
      intro t ht
      rcases eq_or_lt_of_le ht.1 with h | h
      · rw [← h]; exact h0
      · exact hγC t ⟨h, ht.2⟩
    exact isPreconnected_sdiff_image_arc hn hC hCc hγ hinj hγC'
  · have hsub : γ '' Set.Ioc (0:ℝ) 1 ⊆ C := fun x ⟨t, ht, htx⟩ => htx ▸ hγC t ht
    have hset : C \ γ '' Set.Icc (0:ℝ) 1 = C \ γ '' Set.Ioc (0:ℝ) 1 := by
      apply Set.Subset.antisymm
      · intro x hx
        refine ⟨hx.1, fun hmem => hx.2 ?_⟩
        exact Set.image_mono (Set.Ioc_subset_Icc_self) hmem
      · intro x hx
        refine ⟨hx.1, fun hmem => hx.2 ?_⟩
        obtain ⟨t, ht, hxt⟩ := hmem
        have ht0 : (0:ℝ) < t := by
          rcases eq_or_lt_of_le ht.1 with h | h
          · have hγ0 : γ 0 ∈ C := by
              rw [h, hxt]
              exact hx.1
            exact absurd hγ0 h0
          · exact h
        exact ⟨t, ⟨ht0, ht.2⟩, hxt⟩
    rw [hset]
    exact Work.Noncompact.CompressionTube.spike_removal hn hC hCc hγ hinj hsub h0

end Work.Noncompact.Routing
