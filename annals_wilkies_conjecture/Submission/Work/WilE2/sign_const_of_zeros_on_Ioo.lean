import Mathlib

namespace Work.WilE2

/-- If a continuous function vanishes at `a` and has no zeros on the open interval
`(a, b)`, then it has constant sign there. -/
theorem sign_const_of_zeros_on_Ioo {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hcont : Continuous f) (hfa : f a = 0)
    (hne : ∀ x ∈ Set.Ioo a b, f x ≠ 0) :
    (∀ x ∈ Set.Ioo a b, 0 < f x) ∨ (∀ x ∈ Set.Ioo a b, f x < 0) := by
  by_contra h
  push Not at h
  obtain ⟨x, hx, hx0⟩ := h.1
  obtain ⟨y, hy, hy0⟩ := h.2
  have hxneg : f x < 0 := lt_of_le_of_ne hx0 (hne x hx)
  have hypos : 0 < f y := lt_of_le_of_ne hy0 (Ne.symm (hne y hy))
  have hzero : (0 : ℝ) ∈ Set.Icc (f x) (f y) := Set.mem_Icc.mpr ⟨hxneg.le, hypos.le⟩
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · have hmem : (0 : ℝ) ∈ f '' Set.Icc x y :=
      intermediate_value_Icc hxy.le hcont.continuousOn hzero
    obtain ⟨z, hz, hfz⟩ := (Set.mem_image f (Set.Icc x y) 0).mp hmem
    exact hne z ⟨lt_of_lt_of_le hx.1 hz.1, lt_of_le_of_lt hz.2 hy.2⟩ hfz
  · subst hxy
    exact absurd hypos (not_lt.mpr hxneg.le)
  · have hmem : (0 : ℝ) ∈ f '' Set.Icc y x :=
      intermediate_value_Icc' hxy.le hcont.continuousOn hzero
    obtain ⟨z, hz, hfz⟩ := (Set.mem_image f (Set.Icc y x) 0).mp hmem
    exact hne z ⟨lt_of_lt_of_le hy.1 hz.1, lt_of_le_of_lt hz.2 hx.2⟩ hfz

end Work.WilE2
