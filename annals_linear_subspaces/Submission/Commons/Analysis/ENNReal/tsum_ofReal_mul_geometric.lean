import Mathlib.Analysis.SpecificLimits.Basic

namespace Commons.Analysis.ENNReal

theorem tsum_ofReal_mul_geometric {c r : ℝ} (hc : 0 ≤ c) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' n : ℕ, ENNReal.ofReal (c * r ^ n)) = ENNReal.ofReal (c / (1 - r)) := by
  have h2 : (1 : ENNReal) - ENNReal.ofReal r = ENNReal.ofReal (1 - r) := by
    rw [ENNReal.ofReal_sub 1 hr0, ENNReal.ofReal_one]
  have hpos : 0 < 1 - r := by linarith
  have key : ENNReal.ofReal c * (1 - ENNReal.ofReal r)⁻¹ = ENNReal.ofReal (c / (1 - r)) := by
    rw [h2, ← ENNReal.ofReal_inv_of_pos hpos, ← ENNReal.ofReal_mul hc, div_eq_mul_inv]
  rw [show (∑' n : ℕ, ENNReal.ofReal (c * r ^ n))
        = ∑' n : ℕ, ENNReal.ofReal c * (ENNReal.ofReal r) ^ n from
      tsum_congr fun n => by rw [ENNReal.ofReal_mul hc, ENNReal.ofReal_pow hr0]]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
  exact key

end Commons.Analysis.ENNReal