import Mathlib

namespace Work.WilG4c

theorem eqEndpointsOfIoo {S : Set ℝ} {lo hi ra rb : ℝ}
    (hS : S = Set.Ioo ra rb) (hne : S.Nonempty)
    (h1 : ∀ x ∈ S, lo ≤ x ∧ x ≤ hi)
    (h2 : ∀ u : ℝ, lo < u → ∃ x ∈ S, x < u)
    (h3 : ∀ u : ℝ, u < hi → ∃ x ∈ S, u < x) :
    lo = ra ∧ hi = rb := by
  obtain ⟨x0, hx0m⟩ := hne
  have hx0 : ra < x0 ∧ x0 < rb := by
    rw [hS] at hx0m
    exact Set.mem_Ioo.mp hx0m
  have hra_lt_rb : ra < rb := hx0.1.trans hx0.2
  -- `lo` is the infimum of `S`: it is a lower bound, and the interval squeezes it below.
  have hlo_le_ra : lo ≤ ra := by
    by_contra h
    push_neg at h
    -- h : ra < lo
    have hram : ra < min rb lo := lt_min hra_lt_rb h
    have hmin_rb : min rb lo ≤ rb := min_le_left _ _
    have hmin_lo : min rb lo ≤ lo := min_le_right _ _
    have hrt : ra < (ra + min rb lo) / 2 := by linarith
    have ht_rb : (ra + min rb lo) / 2 < rb := by linarith
    have ht_lo : (ra + min rb lo) / 2 < lo := by linarith
    have htS : (ra + min rb lo) / 2 ∈ S := by
      rw [hS]
      exact Set.mem_Ioo.mpr ⟨hrt, ht_rb⟩
    have := (h1 _ htS).1
    linarith
  have hra_le_lo : ra ≤ lo := by
    by_contra h
    push_neg at h
    -- h : lo < ra
    obtain ⟨x, hxS, hx⟩ := h2 ra h
    rw [hS, Set.mem_Ioo] at hxS
    linarith [hxS.1]
  -- Symmetrically for `hi`.
  have hhi_le_rb : hi ≤ rb := by
    by_contra h
    push_neg at h
    -- h : rb < hi
    obtain ⟨x, hxS, hx⟩ := h3 rb h
    rw [hS, Set.mem_Ioo] at hxS
    linarith [hxS.2]
  have hrb_le_hi : rb ≤ hi := by
    by_contra h
    push_neg at h
    -- h : hi < rb
    have hM : max ra hi < rb := max_lt hra_lt_rb h
    have hcM : max ra hi < (max ra hi + rb) / 2 := by linarith
    have hcrb : (max ra hi + rb) / 2 < rb := by linarith
    have hcS : (max ra hi + rb) / 2 ∈ S := by
      rw [hS]
      exact Set.mem_Ioo.mpr ⟨lt_of_le_of_lt (le_max_left _ _) hcM, hcrb⟩
    have hcle := (h1 _ hcS).2
    have hhi_lt : hi < (max ra hi + rb) / 2 := lt_of_le_of_lt (le_max_right _ _) hcM
    linarith
  exact ⟨le_antisymm hlo_le_ra hra_le_lo, le_antisymm hhi_le_rb hrb_le_hi⟩

end Work.WilG4c
