import Mathlib

namespace Work.Mostow

open Set Metric

/-- A `δ`-separated subset of a compact subset of a pseudometric space is finite. -/
theorem separatedFinite {α : Type*} [PseudoMetricSpace α] {s A : Set α} (hc : IsCompact s)
    (hsub : A ⊆ s) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → δ ≤ dist x y) : A.Finite := by
  -- Cover the compact set `s` by finitely many balls of radius `δ / 2`.
  have hε : 0 < δ / 2 := by linarith
  obtain ⟨t, _ht_sub, ht_fin, ht_cov⟩ := finite_cover_balls_of_compact hc hε
  -- `A` is covered by the intersections of `A` with those balls.
  have hAcov : A ⊆ ⋃ x ∈ t, A ∩ ball x (δ / 2) := by
    intro a ha
    rcases mem_iUnion₂.1 (ht_cov (hsub ha)) with ⟨x, hxt, hax⟩
    exact mem_iUnion₂.2 ⟨x, hxt, ⟨ha, hax⟩⟩
  have hEq : A = ⋃ x ∈ t, A ∩ ball x (δ / 2) := by
    apply Subset.antisymm hAcov
    intro a ha
    rcases mem_iUnion₂.1 ha with ⟨x, hxt, hax⟩
    exact hax.1
  rw [hEq]
  refine ht_fin.biUnion fun x _ => Subsingleton.finite ?_
  -- Each such ball meets `A` in at most one point (separation).
  intro a ha b hb
  rcases ha with ⟨haA, hax⟩
  rcases hb with ⟨hbA, hbx⟩
  by_contra hne
  have hge := hsep a haA b hbA hne
  have h1 : dist a x < δ / 2 := hax
  have h2 : dist x b < δ / 2 := by rw [dist_comm]; exact hbx
  have : dist a b < δ := by
    calc dist a b ≤ dist a x + dist x b := dist_triangle _ _ _
      _ < δ / 2 + δ / 2 := by linarith
      _ = δ := by ring
  linarith

end Work.Mostow
