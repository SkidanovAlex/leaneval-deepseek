import Mathlib

namespace Work.RPB.B3

/-- The box `[a,b] × ([c,d] × [-e,e])` is compact. -/
theorem isCompact_rectangularBox (a b c d e : ℝ) :
    IsCompact (Set.Icc a b ×ˢ (Set.Icc c d ×ˢ Set.Icc (-e) e)) :=
  isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)

/-- On a compact set where a continuous function is strictly positive, the function admits a
positive lower bound and a positive upper bound for its absolute value. -/
theorem exists_pos_bounds_of_compact {s : Set (ℝ × (ℝ × ℝ))} {g : ℝ × (ℝ × ℝ) → ℝ}
    (hs : IsCompact s) (hg : Continuous g) (hpos : ∀ p ∈ s, 0 < g p) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ M : ℝ, 0 < M ∧ ∀ p ∈ s, δ ≤ g p ∧ |g p| ≤ M := by
  classical
  by_cases hne : s.Nonempty
  · obtain ⟨x₀, hx₀, hmin⟩ := hs.exists_isMinOn hne hg.continuousOn
    obtain ⟨C, hC⟩ := hs.exists_bound_of_continuousOn hg.continuousOn
    refine ⟨g x₀, hpos x₀ hx₀, max C 1, lt_of_lt_of_le zero_lt_one (le_max_right C 1), ?_⟩
    intro p hp
    exact ⟨hmin hp, le_trans (by simpa [Real.norm_eq_abs] using hC p hp) (le_max_left C 1)⟩
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    exact ⟨1, one_pos, 1, one_pos, fun p hp => absurd (hne ▸ hp) (Set.notMem_empty p)⟩

theorem boundsOnCompactBox {g : ℝ × (ℝ × ℝ) → ℝ} (hg : Continuous g)
    {a b c d e : ℝ}
    (hpos : ∀ p ∈ Set.Icc a b ×ˢ (Set.Icc c d ×ˢ Set.Icc (-e) e), 0 < g p) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ M : ℝ, 0 < M ∧
      ∀ p ∈ Set.Icc a b ×ˢ (Set.Icc c d ×ˢ Set.Icc (-e) e), δ ≤ g p ∧ |g p| ≤ M :=
  exists_pos_bounds_of_compact (isCompact_rectangularBox a b c d e) hg hpos

end Work.RPB.B3
