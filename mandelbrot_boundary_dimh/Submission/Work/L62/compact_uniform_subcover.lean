import Mathlib

namespace Work.L62

/-- **Uniform radius and uniform compact set from a compact family of local data.**
Let `Λ ⊆ ℂ` be compact and suppose that to every `β ∈ Λ` there is attached a positive radius
`r β` and a compact set `A β ⊆ B`.  Then there are a positive `ρ₀` and a compact `K ⊆ B` such that
every `β' ∈ Λ` lies in one of the balls `ball β (r β / 4)` whose index `β ∈ Λ` satisfies
`ρ₀ ≤ r β / 4` and `A β ⊆ K`. -/
theorem compact_uniform_subcover {Λ : Set ℂ} (hΛ : IsCompact Λ) {r : ℂ → ℝ} {A : ℂ → Set ℂ}
    {B : Set ℂ} (hr : ∀ β ∈ Λ, 0 < r β) (hAc : ∀ β ∈ Λ, IsCompact (A β))
    (hAB : ∀ β ∈ Λ, A β ⊆ B) :
    ∃ (ρ₀ : ℝ) (K : Set ℂ), 0 < ρ₀ ∧ IsCompact K ∧ K ⊆ B ∧
      ∀ β' ∈ Λ, ∃ β ∈ Λ, β' ∈ Metric.ball β (r β / 4) ∧ ρ₀ ≤ r β / 4 ∧ A β ⊆ K := by
  rcases Set.eq_empty_or_nonempty Λ with hΛ0 | hne
  · subst hΛ0
    exact ⟨1, ∅, one_pos, isCompact_empty, Set.empty_subset B, by simp⟩
  · -- the balls `ball β (r β / 4)`, `β ∈ Λ`, form an open cover of `Λ`
    -- (each `β` lies in its own ball as `r β > 0`)
    have hcover : Λ ⊆ ⋃ β : Λ, Metric.ball (β : ℂ) (r β / 4) := by
      intro x hx
      refine Set.mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
      simp only [Metric.mem_ball, dist_self]
      have := hr x hx
      linarith
    obtain ⟨t, ht⟩ := hΛ.elim_finite_subcover (fun β : Λ => Metric.ball (β : ℂ) (r β / 4))
      (fun _ => Metric.isOpen_ball) hcover
    -- the finite subcover is nonempty because `Λ` is nonempty
    have htne : t.Nonempty := by
      obtain ⟨x, hx⟩ := hne
      have hx' : x ∈ ⋃ β ∈ t, Metric.ball (β : ℂ) (r β / 4) := ht hx
      rw [Set.mem_iUnion] at hx'
      obtain ⟨β, hx'⟩ := hx'
      rw [Set.mem_iUnion] at hx'
      exact ⟨β, hx'.1⟩
    -- the uniform radius is the minimum of `r β / 4` over the finite subcover,
    -- the uniform compact set is the union of the corresponding `A β`
    refine ⟨t.inf' htne (fun β : Λ => r β / 4), ⋃ β ∈ t, A (β : ℂ), ?_, ?_, ?_, ?_⟩
    · rw [Finset.lt_inf'_iff htne]
      intro β _
      have := hr β β.2
      linarith
    · exact Finset.isCompact_biUnion t (fun β _ => hAc β β.2)
    · intro y hy
      rw [Set.mem_iUnion] at hy
      obtain ⟨β, hy⟩ := hy
      rw [Set.mem_iUnion] at hy
      exact hAB β β.2 hy.2
    · intro β' hβ'
      have hmem : β' ∈ ⋃ β ∈ t, Metric.ball (β : ℂ) (r β / 4) := ht hβ'
      rw [Set.mem_iUnion] at hmem
      obtain ⟨β, hmem⟩ := hmem
      rw [Set.mem_iUnion] at hmem
      obtain ⟨hβt, hball⟩ := hmem
      refine ⟨β, β.2, hball, ?_, ?_⟩
      · exact Finset.inf'_le (fun β : Λ => r β / 4) hβt
      · intro y hy
        exact Set.mem_iUnion.mpr ⟨β, Set.mem_iUnion.mpr ⟨hβt, hy⟩⟩

end Work.L62
