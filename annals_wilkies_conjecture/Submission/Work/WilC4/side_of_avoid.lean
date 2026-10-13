import Mathlib

namespace Work.WilC4

theorem side_of_avoid {s M : Set ℝ} {f : ℝ → ℝ} {m : ℝ}
    (hs : IsPreconnected s) (hcont : ContinuousOn f s)
    (havoid : ∀ x ∈ s, f x ∉ M) (hm : m ∈ M) :
    (∀ x ∈ s, f x < m) ∨ (∀ x ∈ s, m < f x) := by
  -- The image of a preconnected set under a continuous map is preconnected, hence
  -- order-connected: it contains every interval between two of its points.
  have hord : Set.OrdConnected (f '' s) := (hs.image f hcont).ordConnected
  by_cases h : ∀ x ∈ s, f x < m
  · exact Or.inl h
  · right
    push Not at h
    obtain ⟨x, hx, hxle⟩ := h
    have hne : f x ≠ m := fun hfxm => havoid x hx (by rw [hfxm]; exact hm)
    have hfg : m < f x := lt_of_le_of_ne hxle (Ne.symm hne)
    intro y hy
    by_contra hcon
    have hymle : f y ≤ m := not_lt.mp hcon
    have hfy : f y ∈ f '' s := ⟨y, hy, rfl⟩
    have hfx : f x ∈ f '' s := ⟨x, hx, rfl⟩
    have hmem : m ∈ f '' s := hord.out hfy hfx ⟨hymle, le_of_lt hfg⟩
    obtain ⟨z, hz, hzf⟩ := hmem
    exact havoid z hz (by rw [hzf]; exact hm)

end Work.WilC4
