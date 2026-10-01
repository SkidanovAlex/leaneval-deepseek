import Mathlib

namespace Work.LinnikAreas.Density4

/-- On the interval `(0, 1]` the Gamma function is at least `1`: it strictly decreases
there from `+∞` (as `σ → 0⁺`) down to `Gamma 1 = 1` (Mathlib's `Real.Gamma_strictAntiOn_Ioc`). -/
theorem Gamma_ge_one (σ : ℝ) (hσ : 0 < σ) (hσ1 : σ ≤ 1) : 1 ≤ Real.Gamma σ := by
  rcases lt_or_eq_of_le hσ1 with h | h
  · have h2 := Real.Gamma_strictAntiOn_Ioc.antitoneOn ⟨hσ, hσ1⟩ ⟨one_pos, le_rfl⟩ hσ1
    rwa [Real.Gamma_one] at h2
  · rw [h, Real.Gamma_one]

end Work.LinnikAreas.Density4
