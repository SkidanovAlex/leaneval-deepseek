import Mathlib

namespace Work.WilG4c

theorem eqEndpointsOfSingleton {S : Set ℝ} {lo hi x0 : ℝ} (hS : S = {x0})
    (h1 : ∀ x ∈ S, lo ≤ x ∧ x ≤ hi)
    (h2 : ∀ u : ℝ, lo < u → ∃ x ∈ S, x < u)
    (h3 : ∀ u : ℝ, u < hi → ∃ x ∈ S, u < x) :
    lo = x0 ∧ hi = x0 := by
  have hx0 : x0 ∈ S := by rw [hS]; exact Set.mem_singleton x0
  obtain ⟨hlo, hhi⟩ := h1 x0 hx0
  have hle : x0 ≤ lo := by
    by_contra h
    push Not at h
    obtain ⟨x, hxS, hxu⟩ := h2 x0 h
    rw [hS, Set.mem_singleton_iff] at hxS
    rw [hxS] at hxu
    exact lt_irrefl x0 hxu
  have hge : hi ≤ x0 := by
    by_contra h
    push Not at h
    obtain ⟨x, hxS, hxu⟩ := h3 x0 h
    rw [hS, Set.mem_singleton_iff] at hxS
    rw [hxS] at hxu
    exact lt_irrefl x0 hxu
  exact ⟨le_antisymm hlo hle, le_antisymm hge hhi⟩

end Work.WilG4c
