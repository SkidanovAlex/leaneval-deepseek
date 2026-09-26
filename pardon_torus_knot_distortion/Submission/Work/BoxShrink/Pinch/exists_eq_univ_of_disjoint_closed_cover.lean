import Mathlib

namespace Work.BoxShrink.Pinch

/-- A finite disjoint cover of `ℝ` by closed sets has one member equal to the whole space.
`ℝ` is (pre)connected, so each member of a disjoint finite cover by closed sets is clopen;
the dichotomy for clopen sets in a preconnected space forces it to be empty or everything,
and non-emptiness of the cover selects one that is everything. -/
theorem exists_eq_univ_of_disjoint_closed_cover {n : ℕ} {A : Fin n → Set ℝ}
    (hclosed : ∀ i : Fin n, IsClosed (A i))
    (hdisj : Pairwise fun i j : Fin n => Disjoint (A i) (A j))
    (hcover : (Set.univ : Set ℝ) ⊆ ⋃ i, A i) : ∃ i : Fin n, A i = Set.univ := by
  have hUnion : (⋃ i, A i) = (Set.univ : Set ℝ) := Set.eq_univ_of_univ_subset hcover
  -- Each `A j` is clopen: closed by hypothesis, and open since its complement is the
  -- finite union of the (closed) other pieces.
  have hclopen : ∀ j : Fin n, IsClopen (A j) := by
    intro j
    refine ⟨hclosed j, ?_⟩
    rw [← isClosed_compl_iff]
    have hcompl : (A j)ᶜ = ⋃ i : Fin n, (A i \ A j) := by
      rw [Set.compl_eq_univ_sdiff, ← hUnion, Set.iUnion_sdiff]
    rw [hcompl]
    refine isClosed_iUnion_of_finite (fun i => ?_)
    rcases eq_or_ne i j with rfl | hne
    · simp
    · rw [(hdisj hne).sdiff_eq_left]; exact hclosed i
  -- Extract a member of the cover from the (nonempty) point `0`.
  obtain ⟨j, hj⟩ : ∃ j, (0 : ℝ) ∈ A j := by
    have h := hcover (Set.mem_univ (0 : ℝ))
    rwa [Set.mem_iUnion] at h
  refine ⟨j, ?_⟩
  rcases (isClopen_iff.mp (hclopen j)) with h | h
  · rw [h] at hj; exact absurd hj (by simp)
  · exact h

end Work.BoxShrink.Pinch
