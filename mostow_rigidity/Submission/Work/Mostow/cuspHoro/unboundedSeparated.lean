import Mathlib

namespace Work.Mostow.cuspHoro

/-- In an unbounded set of a pseudo metric space one can find, for any prescribed finite set
of centres, a point of the set at distance at least `2ε` from all of them. -/
theorem exists_far_of_not_isBounded {α : Type*} [PseudoMetricSpace α] {A : Set α}
    (hA : ¬ Bornology.IsBounded A) (ε : ℝ) (T : Finset α) :
    ∃ y ∈ A, ∀ x ∈ T, 2 * ε ≤ dist y x := by
  by_contra h
  push Not at h
  have hsub : A ⊆ ⋃ x ∈ (T : Set α), Metric.ball x (2 * ε) := by
    intro y hy
    obtain ⟨x, hxT, hxy⟩ := h y hy
    exact Set.mem_iUnion₂.mpr ⟨x, hxT, hxy⟩
  have hb : Bornology.IsBounded (⋃ x ∈ (T : Set α), Metric.ball x (2 * ε)) :=
    (Bornology.isBounded_biUnion (T.finite_toSet)).2 (fun x _ => Metric.isBounded_ball)
  exact hA (hb.subset hsub)

/-- An unbounded subset of a pseudo metric space admits, for every `N`, a subset with `N`
elements that is `2ε`-separated. -/
theorem unboundedSeparated {α : Type*} [PseudoMetricSpace α] {A : Set α}
    (hA : ¬ Bornology.IsBounded A) {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∃ S : Finset α, S.card = N ∧ (∀ y ∈ S, y ∈ A) ∧
      ∀ y ∈ S, ∀ y' ∈ S, y ≠ y' → 2 * ε ≤ dist y y' := by
  classical
  have key : ∀ k, ∃ S : Finset α, S.card = k ∧ (∀ y ∈ S, y ∈ A) ∧
      ∀ y ∈ S, ∀ y' ∈ S, y ≠ y' → 2 * ε ≤ dist y y' := by
    intro k
    induction k with
    | zero => exact ⟨∅, rfl, by simp, by simp⟩
    | succ k ih =>
      obtain ⟨S, hcard, hsub, hsep⟩ := ih
      obtain ⟨y, hyA, hyfar⟩ := exists_far_of_not_isBounded hA ε S
      have hyS : y ∉ S := by
        intro hmem
        have := hyfar y hmem
        rw [dist_self] at this
        linarith
      refine ⟨insert y S, ?_, ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hyS, hcard]
      · intro z hz
        rw [Finset.mem_insert] at hz
        rcases hz with rfl | hz
        · exact hyA
        · exact hsub z hz
      · intro z hz z2 hz2 hne
        rw [Finset.mem_insert] at hz hz2
        rcases hz with rfl | hz
        · rcases hz2 with rfl | hz2
          · exact absurd rfl hne
          · exact hyfar z2 hz2
        · rcases hz2 with rfl | hz2
          · rw [dist_comm]; exact hyfar z hz
          · exact hsep z hz z2 hz2 hne
  exact key N

end Work.Mostow.cuspHoro
