import Mathlib.Analysis.Complex.Exponential

namespace Commons.NumberTheory.Linnik

theorem exp_neg_bounds (t : ℝ) (ht : 0 ≤ t) :
    (0 ≤ 1 - Real.exp (-t)) ∧ (1 - Real.exp (-t) ≤ t) ∧
    (t - t ^ 2 / 2 ≤ 1 - Real.exp (-t)) := by
  -- (1): exp (-t) ≤ 1 since -t ≤ 0
  have hmt : -t ≤ 0 := (neg_nonpos).mpr ht
  have hexple : Real.exp (-t) ≤ 1 := (Real.exp_le_one_iff).2 hmt
  have h1 : 0 ≤ 1 - Real.exp (-t) := by linarith
  -- (2): lower bound exp (-t) ≥ 1 - t
  have hlb : 1 - t ≤ Real.exp (-t) := Real.one_sub_le_exp_neg t
  have h2 : 1 - Real.exp (-t) ≤ t := by linarith
  -- (3): upper bound exp (-t) ≤ 1 - t + t²/2 via reciprocals
  have hquad : 1 + t + t ^ 2 / 2 ≤ Real.exp t := Real.quadratic_le_exp_of_nonneg ht
  have hqpos : 0 < 1 + t + t ^ 2 / 2 := by positivity
  have hrec : (Real.exp t)⁻¹ ≤ (1 + t + t ^ 2 / 2)⁻¹ :=
    (inv_le_inv₀ (Real.exp_pos t) hqpos).2 hquad
  have hprod : 1 ≤ (1 - t + t ^ 2 / 2) * (1 + t + t ^ 2 / 2) := by
    have hpoly : (1 - t + t ^ 2 / 2) * (1 + t + t ^ 2 / 2) = 1 + t ^ 4 / 4 := by
      ring
    rw [hpoly]
    have hnn : 0 ≤ t ^ 4 / 4 := by positivity
    linarith
  have htwo : (1 + t + t ^ 2 / 2)⁻¹ ≤ 1 - t + t ^ 2 / 2 := by
    have hden : (1 : ℝ) / (1 + t + t ^ 2 / 2) ≤ 1 - t + t ^ 2 / 2 := by
      rw [div_le_iff₀ hqpos]
      exact hprod
    simpa [one_div] using hden
  have hub : Real.exp (-t) ≤ 1 - t + t ^ 2 / 2 := by
    calc
      Real.exp (-t) = (Real.exp t)⁻¹ := Real.exp_neg t
      _ ≤ (1 + t + t ^ 2 / 2)⁻¹ := hrec
      _ ≤ 1 - t + t ^ 2 / 2 := htwo
  have h3 : t - t ^ 2 / 2 ≤ 1 - Real.exp (-t) := by linarith
  exact ⟨h1, h2, h3⟩

end Commons.NumberTheory.Linnik