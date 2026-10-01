import Mathlib

namespace Work.LinnikAreas.Density4

/-- For `X ≥ 1` one has `1 / (1 - exp(-1/X)) ≤ X + 1`, i.e. `1 - exp(-t) ≥ t/(1+t)`
with `t = 1/X`. -/
lemma inv_one_sub_exp_neg_one_div_le (X : ℝ) (hX : 1 ≤ X) :
    1 / (1 - Real.exp (-(1 / X))) ≤ X + 1 := by
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  set t : ℝ := 1 / X with ht_def
  have ht_pos : 0 < t := by rw [ht_def]; positivity
  have hexp : 1 + t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
  have h_inv : (Real.exp t)⁻¹ ≤ (1 + t)⁻¹ := by
    rw [inv_le_inv₀ (Real.exp_pos t) (by linarith)]
    exact hexp
  have hden_pos : 0 < t / (1 + t) := div_pos ht_pos (by linarith)
  have h1mexp : t / (1 + t) ≤ 1 - Real.exp (-t) := by
    rw [Real.exp_neg]
    have h1 : t / (1 + t) = 1 - (1 + t)⁻¹ := by
      field_simp
      ring
    rw [h1]
    linarith [h_inv]
  have hgoal : 1 / (1 - Real.exp (-t)) ≤ 1 / (t / (1 + t)) :=
    one_div_le_one_div_of_le hden_pos h1mexp
  have hright : 1 / (t / (1 + t)) = X + 1 := by
    rw [one_div_div, ht_def]
    field_simp
  calc 1 / (1 - Real.exp (-(1 / X)))
      = 1 / (1 - Real.exp (-t)) := by rw [← ht_def]
    _ ≤ 1 / (t / (1 + t)) := hgoal
    _ = X + 1 := hright

end Work.LinnikAreas.Density4
