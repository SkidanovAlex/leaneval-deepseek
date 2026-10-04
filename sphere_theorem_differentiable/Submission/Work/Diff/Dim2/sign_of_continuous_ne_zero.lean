import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Dim2

/-- **A continuous nowhere-zero function on `ℝ` has constant sign.** -/
theorem sign_of_continuous_ne_zero {f : ℝ → ℝ} (hf : Continuous f) (hne : ∀ θ, f θ ≠ 0) :
    (∀ θ, 0 < f θ) ∨ (∀ θ, f θ < 0) := by
  -- `f 0 ≠ 0`, so `f` is either positive or negative at `0`; show that this sign is constant,
  -- using the intermediate value theorem: a value of the opposite sign would force a zero.
  rcases lt_or_gt_of_ne (hne 0) with h0 | h0
  · -- `f 0 < 0`: every value of `f` is negative.
    right
    intro θ
    by_contra h
    -- `h : ¬ f θ < 0`, i.e. `0 ≤ f θ`, and `f θ ≠ 0`, hence `0 < f θ`.
    have hpos : 0 < f θ := lt_of_le_of_ne (not_lt.mp h) (Ne.symm (hne θ))
    have hmem : (0 : ℝ) ∈ Set.Icc (f 0) (f θ) := Set.mem_Icc.mpr ⟨h0.le, hpos.le⟩
    have hx := intermediate_value_univ (0 : ℝ) θ hf hmem
    rw [Set.mem_range] at hx
    obtain ⟨x, hx⟩ := hx
    exact hne x hx
  · -- `0 < f 0`: every value of `f` is positive.
    left
    intro θ
    by_contra h
    -- `h : ¬ 0 < f θ`, i.e. `f θ ≤ 0`, and `f θ ≠ 0`, hence `f θ < 0`.
    have hneg : f θ < 0 := lt_of_le_of_ne (not_lt.mp h) (hne θ)
    have hmem : (0 : ℝ) ∈ Set.Icc (f θ) (f 0) := Set.mem_Icc.mpr ⟨hneg.le, h0.le⟩
    have hx := intermediate_value_univ θ 0 hf hmem
    rw [Set.mem_range] at hx
    obtain ⟨x, hx⟩ := hx
    exact hne x hx

end Work.Diff.Dim2
