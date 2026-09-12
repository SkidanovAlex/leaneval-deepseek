import Mathlib.Data.ENNReal.Basic

open scoped NNReal ENNReal

set_option linter.unusedVariables false

namespace Commons.Order.ENNReal

lemma exists_positive_nnreal_lt {x : ℝ≥0} (hx : 0 < x) (b : ℝ≥0∞) (hb : b < (x : ℝ≥0∞)) :
    ∃ ω : ℝ≥0, 0 < ω ∧ b < (ω : ℝ≥0∞) ∧ ω < x := by
  rcases ENNReal.lt_iff_exists_nnreal_btwn.1 hb with ⟨ω, hbω, hωx⟩
  refine ⟨ω, ?_, hbω, ?_⟩
  · exact ENNReal.coe_lt_coe.1 (lt_of_le_of_lt (zero_le (a := b)) hbω)
  · exact ENNReal.coe_lt_coe.1 hωx

end Commons.Order.ENNReal