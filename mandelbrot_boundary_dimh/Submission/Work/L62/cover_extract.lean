import Mathlib
import Submission.Work.L62.compact_uniform_subcover

namespace Work.L62

/-- **Extract a finite uniform cover with uniform lower bounds on two data functions.**
Let `Λ ⊆ ℂ` be compact and suppose to every `β ∈ Λ` there is attached a positive radius `ε β`,
two positive reals `ρ₁ β`, `δg β`, and a compact set `A β ⊆ B`.  Then there is a finite set
`t ⊆ Λ`, positive reals `ρ₀`, `δ₀` and a compact `K ⊆ B` containing all `A β` (`β ∈ t`), such
that every `β' ∈ Λ` lies in the ball `ball β (ε β)` for some `β ∈ t` which simultaneously
satisfies `ρ₀ ≤ ρ₁ β` and `δ₀ ≤ δg β`. -/
theorem cover_extract {Λ : Set ℂ} (hΛ : IsCompact Λ) {ε ρ₁ δg : ℂ → ℝ}
    (hε : ∀ β ∈ Λ, 0 < ε β) (hρ₁ : ∀ β ∈ Λ, 0 < ρ₁ β) (hδ : ∀ β ∈ Λ, 0 < δg β)
    {A : ℂ → Set ℂ} {B : Set ℂ} (hA : ∀ β ∈ Λ, IsCompact (A β)) (hAB : ∀ β ∈ Λ, A β ⊆ B) :
    ∃ (t : Finset ℂ) (ρ₀ δ₀ : ℝ) (K : Set ℂ), (∀ β ∈ t, β ∈ Λ) ∧ 0 < ρ₀ ∧ 0 < δ₀ ∧
      IsCompact K ∧ K ⊆ B ∧ (∀ β ∈ t, A β ⊆ K) ∧
      ∀ β' ∈ Λ, ∃ β ∈ t, ‖β' - β‖ < ε β ∧ ρ₀ ≤ ρ₁ β ∧ δ₀ ≤ δg β := by
  classical
  rcases Set.eq_empty_or_nonempty Λ with hΛ0 | hne
  · subst hΛ0
    exact ⟨∅, 1, 1, ∅, by simp, one_pos, one_pos, isCompact_empty, Set.empty_subset B,
      by simp, by simp⟩
  · -- The balls `ball β (ε β)`, `β ∈ Λ`, form an open cover of `Λ`.
    have hcover : Λ ⊆ ⋃ β : Λ, Metric.ball (β : ℂ) (ε β) := by
      intro x hx
      refine Set.mem_iUnion.mpr ⟨⟨x, hx⟩, ?_⟩
      simp only [Metric.mem_ball, dist_self]
      exact hε x hx
    obtain ⟨t, ht⟩ := hΛ.elim_finite_subcover (fun β : Λ => Metric.ball (β : ℂ) (ε β))
      (fun _ => Metric.isOpen_ball) hcover
    -- The finite subcover is nonempty because `Λ` is nonempty.
    have htne : t.Nonempty := by
      obtain ⟨x, hx⟩ := hne
      have hx' : x ∈ ⋃ β ∈ t, Metric.ball (β : ℂ) (ε β) := ht hx
      rw [Set.mem_iUnion] at hx'
      obtain ⟨β, hx'⟩ := hx'
      rw [Set.mem_iUnion] at hx'
      exact ⟨β, hx'.1⟩
    refine ⟨t.image (fun β : Λ => (β : ℂ)),
      t.inf' htne (fun β : Λ => ρ₁ β), t.inf' htne (fun β : Λ => δg β),
      ⋃ β ∈ t, A (β : ℂ), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- every `β ∈ t` lies in `Λ`
      intro β hβ
      obtain ⟨γ, _, rfl⟩ := Finset.mem_image.mp hβ
      exact γ.2
    · rw [Finset.lt_inf'_iff htne]
      intro β _
      exact hρ₁ β β.2
    · rw [Finset.lt_inf'_iff htne]
      intro β _
      exact hδ β β.2
    · exact Finset.isCompact_biUnion t (fun β _ => hA β β.2)
    · intro y hy
      rw [Set.mem_iUnion] at hy
      obtain ⟨β, hy⟩ := hy
      rw [Set.mem_iUnion] at hy
      exact hAB β β.2 hy.2
    · -- the union contains each `A β` for `β ∈ t`
      intro β hβ y hy
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hβ
      exact Set.mem_iUnion.mpr ⟨γ, Set.mem_iUnion.mpr ⟨hγ, hy⟩⟩
    · -- the covering property with the uniform lower bounds
      intro β' hβ'
      have hmem : β' ∈ ⋃ β ∈ t, Metric.ball (β : ℂ) (ε β) := ht hβ'
      rw [Set.mem_iUnion] at hmem
      obtain ⟨β, hmem⟩ := hmem
      rw [Set.mem_iUnion] at hmem
      obtain ⟨hβt, hball⟩ := hmem
      refine ⟨β, Finset.mem_image.mpr ⟨β, hβt, rfl⟩, ?_, ?_, ?_⟩
      · rw [Metric.mem_ball, dist_eq_norm] at hball
        exact hball
      · exact Finset.inf'_le (fun β : Λ => ρ₁ β) hβt
      · exact Finset.inf'_le (fun β : Λ => δg β) hβt

end Work.L62
