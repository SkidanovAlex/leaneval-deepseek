import Mathlib

namespace Work.KMTAreas.A5

theorem ofReal_toReal_const_eq3_nn {m : ℝ} (hm : 0 ≤ m) {U V W : ENNReal} (hU : U < ⊤) (hV : V < ⊤) (hW : W < ⊤) {α β γ : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) : ENNReal.ofReal (m * U.toReal ^ α * V.toReal ^ β * W.toReal ^ γ) = ENNReal.ofReal m * U ^ α * V ^ β * W ^ γ := by
  -- each finite `ENNReal` is the `ofReal` of its `toReal`, and `ofReal` commutes with `rpow`
  have hUpow : U ^ α = ENNReal.ofReal (U.toReal ^ α) := by
    conv_lhs => rw [← ENNReal.ofReal_toReal (ne_top_of_lt hU)]
    rw [ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hα]
  have hVpow : V ^ β = ENNReal.ofReal (V.toReal ^ β) := by
    conv_lhs => rw [← ENNReal.ofReal_toReal (ne_top_of_lt hV)]
    rw [ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hβ]
  have hWpow : W ^ γ = ENNReal.ofReal (W.toReal ^ γ) := by
    conv_lhs => rw [← ENNReal.ofReal_toReal (ne_top_of_lt hW)]
    rw [ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hγ]
  rw [hUpow, hVpow, hWpow]
  -- now `ofReal` of the four-factor nonnegative product, split off one factor at a time
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul (by positivity)]

end Work.KMTAreas.A5
