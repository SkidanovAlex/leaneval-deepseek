import Mathlib

namespace Work.EQ

/-- On an interval whose interior is free of zeros, a continuous real function has a
uniform sign. -/
theorem sign_uniform {f : ℝ → ℝ} (hcont : Continuous f) {a b : ℝ} (hab : a < b)
    (ha : f a = 0) (hb : f b = 0)
    (hfix : ∀ x, a < x → x < b → f x ≠ 0) :
    (∀ x, a < x → x < b → 0 < f x) ∨ (∀ x, a < x → x < b → f x < 0) := by
  by_cases h : ∃ x, a < x ∧ x < b ∧ 0 < f x
  · -- there is a positive value on the open interval: every value there is positive
    left
    rintro y hay hyb
    by_contra hnot
    have hyneg : f y < 0 := lt_of_le_of_ne (not_lt.mp hnot) (hfix y hay hyb)
    obtain ⟨x, hax, hxb, hxpos⟩ := h
    -- a zero strictly between x and y would contradict hfix
    have hzero : ∃ z, a < z ∧ z < b ∧ f z = 0 := by
      rcases le_total x y with hxy | hyx
      · -- x ≤ y, f x > 0 > f y : IVT on [x, y]
        obtain ⟨z, hz, hfz⟩ := (intermediate_value_Icc' hxy hcont.continuousOn)
          (show (0 : ℝ) ∈ Set.Icc (f y) (f x) from ⟨le_of_lt hyneg, le_of_lt hxpos⟩)
        exact ⟨z, lt_of_lt_of_le hax hz.1, lt_of_le_of_lt hz.2 hyb, hfz⟩
      · -- y < x, f y < 0 < f x : IVT on [y, x]
        obtain ⟨z, hz, hfz⟩ := (intermediate_value_Icc hyx hcont.continuousOn)
          (show (0 : ℝ) ∈ Set.Icc (f y) (f x) from ⟨le_of_lt hyneg, le_of_lt hxpos⟩)
        exact ⟨z, lt_of_lt_of_le hay hz.1, lt_of_le_of_lt hz.2 hxb, hfz⟩
    obtain ⟨z, haz, hzb, hfz⟩ := hzero
    exact (hfix z haz hzb) hfz
  · -- no positive value: every value on the open interval is negative
    right
    intro x hx hxb'
    have hxne : f x ≠ 0 := hfix x hx hxb'
    have hxle : f x ≤ 0 := not_lt.mp (fun hpos => h ⟨x, hx, hxb', hpos⟩)
    exact lt_of_le_of_ne hxle hxne

end Work.EQ
