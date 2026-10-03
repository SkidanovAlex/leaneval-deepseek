import Mathlib

/-!
# Positive distance between a compact set and a disjoint closed set

If `A` is compact, `B` is closed and `A ∩ B = ∅`, then `dist a b` is bounded below by a
positive constant on `A × B`.  The proof minimises the continuous function
`a ↦ infDist a B` over the compact set `A`: on `A` this function is strictly positive
because `A` avoids the closed set `B`, and `infDist a B ≤ dist a b` for `b ∈ B`.
-/

namespace Work.PlanarSC

theorem exists_pos_le_dist_of_isCompact_of_isClosed {A B : Set ℂ} (hA : IsCompact A)
    (hB : IsClosed B) (hd : Disjoint A B) :
    ∃ e : ℝ, 0 < e ∧ ∀ a ∈ A, ∀ b ∈ B, e ≤ dist a b := by
  rcases B.eq_empty_or_nonempty with hB0 | hBne
  · refine ⟨1, one_pos, fun a _ b hb => absurd hb ?_⟩
    simp [hB0]
  · obtain ⟨e, he0, he⟩ := hA.exists_forall_le' (a := (0 : ℝ)) (f := fun a => Metric.infDist a B)
      (Metric.continuous_infDist_pt B).continuousOn
      (fun a ha => (hB.notMem_iff_infDist_pos hBne).1 ((Set.disjoint_left.1 hd) ha))
    exact ⟨e, he0, fun a ha b hb => (he a ha).trans (Metric.infDist_le_dist_of_mem hb)⟩

end Work.PlanarSC
