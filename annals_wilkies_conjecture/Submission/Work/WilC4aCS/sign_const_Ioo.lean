import Mathlib

namespace Work.WilC4aCS

/-- A continuous nowhere-zero real function on an interval `(a,b)` has constant sign on that
interval: if two points of `(a,b)` carried values of opposite sign, the intermediate value
theorem applied on the subinterval between them would produce a zero inside `(a,b)`. -/
theorem sign_const_Ioo {g : ℝ → ℝ} {a b : ℝ} (hcont : ContinuousOn g (Set.Icc a b))
    (hnz : ∀ x ∈ Set.Ioo a b, g x ≠ 0) :
    (∀ x ∈ Set.Ioo a b, 0 < g x) ∨ (∀ x ∈ Set.Ioo a b, g x < 0) := by
  by_cases hpos : ∃ x ∈ Set.Ioo a b, 0 < g x
  · left
    obtain ⟨x₀, hx₀, hx₀pos⟩ := hpos
    intro x hx
    by_contra h
    rw [not_lt] at h
    have hneg : g x < 0 := lt_of_le_of_ne h (hnz x hx)
    rcases le_total x₀ x with hle | hle
    · -- `x₀ ≤ x`: apply IVT on `[x₀, x]`, noting `g x < 0 < g x₀`.
      have hcont' : ContinuousOn g (Set.Icc x₀ x) :=
        hcont.mono fun z hz => ⟨le_trans hx₀.1.le hz.1, le_trans hz.2 hx.2.le⟩
      have hmem : (0 : ℝ) ∈ Set.Ioo (g x) (g x₀) := ⟨hneg, hx₀pos⟩
      obtain ⟨c, hc, hgc⟩ := intermediate_value_Ioo' hle hcont' hmem
      exact hnz c ⟨lt_trans hx₀.1 hc.1, lt_trans hc.2 hx.2⟩ hgc
    · -- `x ≤ x₀`: apply IVT on `[x, x₀]`, noting `g x < 0 < g x₀`.
      have hcont' : ContinuousOn g (Set.Icc x x₀) :=
        hcont.mono fun z hz => ⟨le_trans hx.1.le hz.1, le_trans hz.2 hx₀.2.le⟩
      have hmem : (0 : ℝ) ∈ Set.Ioo (g x) (g x₀) := ⟨hneg, hx₀pos⟩
      obtain ⟨c, hc, hgc⟩ := intermediate_value_Ioo hle hcont' hmem
      exact hnz c ⟨lt_trans hx.1 hc.1, lt_trans hc.2 hx₀.2⟩ hgc
  · right
    intro x hx
    have hle : g x ≤ 0 := le_of_not_gt fun hlt => hpos ⟨x, hx, hlt⟩
    exact lt_of_le_of_ne hle (hnz x hx)

end Work.WilC4aCS
