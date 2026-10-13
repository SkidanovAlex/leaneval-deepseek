import Mathlib

namespace Work.WilG4a

theorem signConst_ivt {u v : ℝ} (huv : u < v) (g : ℝ → ℝ)
    (hg : ContinuousOn g (Set.Ioo u v)) (hne : ∀ x ∈ Set.Ioo u v, g x ≠ 0) :
    (∀ x ∈ Set.Ioo u v, 0 ≤ g x) ∨ (∀ x ∈ Set.Ioo u v, g x ≤ 0) := by
  by_contra h
  push Not at h
  obtain ⟨x, hx, hxg⟩ := h.1
  obtain ⟨y, hy, hyg⟩ := h.2
  have h0 : (0 : ℝ) ∈ Set.Icc (g x) (g y) := ⟨le_of_lt hxg, le_of_lt hyg⟩
  have him := (isPreconnected_Ioo (a := u) (b := v)).intermediate_value hx hy hg h0
  obtain ⟨z, hz, hzg⟩ := him
  exact hne z hz hzg

end Work.WilG4a
