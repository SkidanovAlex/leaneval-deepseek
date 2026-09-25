import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Commons.NumberTheory.Robin

lemma caF1_le_inv_mul_log {p : ℕ} (hp : 2 ≤ p) :
    Real.log ((((p : ℝ) ^ (2 : ℕ)) - 1) / (((p : ℝ) ^ (2 : ℕ)) - (p : ℝ))) / Real.log (p : ℝ)
      ≤ 1 / ((p : ℝ) * Real.log (p : ℝ)) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp1 : (1 : ℝ) < (p : ℝ) := by linarith
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hlog_pos : 0 < Real.log (p : ℝ) := Real.log_pos hp1
  have hpm1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hratio : (((p : ℝ) ^ (2 : ℕ) - 1) / ((p : ℝ) ^ (2 : ℕ) - (p : ℝ)))
      = ((p : ℝ) + 1) / (p : ℝ) := by
    have h1 : (p : ℝ) ^ (2 : ℕ) - 1 = ((p : ℝ) - 1) * ((p : ℝ) + 1) := by ring
    have h2 : (p : ℝ) ^ (2 : ℕ) - (p : ℝ) = (p : ℝ) * ((p : ℝ) - 1) := by ring
    rw [h1, h2]
    field_simp
  rw [hratio]
  have hlog_le : Real.log (((p : ℝ) + 1) / (p : ℝ)) ≤ 1 / (p : ℝ) := by
    have hpos : 0 < ((p : ℝ) + 1) / (p : ℝ) := by positivity
    have h := Real.log_le_sub_one_of_pos hpos
    have hsub : ((p : ℝ) + 1) / (p : ℝ) - 1 = 1 / (p : ℝ) := by
      field_simp
      ring
    linarith [hsub]
  calc Real.log (((p : ℝ) + 1) / (p : ℝ)) / Real.log (p : ℝ)
      ≤ (1 / (p : ℝ)) / Real.log (p : ℝ) :=
        div_le_div_of_nonneg_right hlog_le (le_of_lt hlog_pos)
    _ = 1 / ((p : ℝ) * Real.log (p : ℝ)) := by
        field_simp

end Commons.NumberTheory.Robin