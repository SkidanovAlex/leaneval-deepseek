import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Commons.NumberTheory.Robin

lemma caMu_pos {p : ℕ} {ε : ℝ} (hp : 2 ≤ p) (hε : 0 < ε) : 0 < Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / (((p : ℝ) ^ (1 + ε)) - (p : ℝ))) / Real.log (p : ℝ) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp1 : (1 : ℝ) < (p : ℝ) := by linarith
  have hε1 : (1 : ℝ) < 1 + ε := by linarith
  have hpow : (p : ℝ) < (p : ℝ) ^ (1 + ε) := by
    have := Real.rpow_lt_rpow_of_exponent_lt hp1 hε1
    simpa using this
  have hden : 0 < (p : ℝ) ^ (1 + ε) - (p : ℝ) := by linarith
  have hnum1 : 1 < ((p : ℝ) ^ (1 + ε) - 1) / ((p : ℝ) ^ (1 + ε) - (p : ℝ)) := by
    rw [one_lt_div hden]
    linarith
  exact div_pos (Real.log_pos hnum1) (Real.log_pos hp1)

end Commons.NumberTheory.Robin