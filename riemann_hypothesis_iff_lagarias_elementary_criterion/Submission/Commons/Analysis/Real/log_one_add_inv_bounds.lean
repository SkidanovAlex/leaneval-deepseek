import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Commons.Analysis.Real

theorem log_one_add_inv_bounds {t : ℝ} (ht : 0 < t) :
    1 / (t + 1) < Real.log (1 + 1 / t) ∧ Real.log (1 + 1 / t) ≤ 1 / t := by
  constructor
  · -- Lower bound: 1 / (t + 1) < log (1 + 1 / t)
    have ht1 : 0 < t + 1 := by linarith
    have ht1n : t + 1 ≠ 0 := ne_of_gt ht1
    have htn : t ≠ 0 := ne_of_gt ht
    have hy : 0 < t / (t + 1) := div_pos ht ht1
    have hyne : t / (t + 1) ≠ 1 := by
      intro h
      have hEq : t = t + 1 := by
        calc
          t = (t / (t + 1)) * (t + 1) := by field_simp [ht1n]
          _ = 1 * (t + 1) := by rw [h]
          _ = t + 1 := by ring
      linarith
    have hloglt := Real.log_lt_sub_one_of_pos hy hyne
    have hstep : t / (t + 1) - 1 = -(1 / (t + 1)) := by
      field_simp [ht1n]
      ring
    have hlt : Real.log (t / (t + 1)) < -(1 / (t + 1)) := by
      rw [← hstep]
      exact hloglt
    have hgt : 1 / (t + 1) < -Real.log (t / (t + 1)) := by
      simpa using (neg_lt_neg hlt)
    have hmain : -Real.log (t / (t + 1)) = Real.log (1 + 1 / t) := by
      have hinv : (t / (t + 1))⁻¹ = 1 + 1 / t := by
        field_simp [ht1n, htn]
      calc
        -Real.log (t / (t + 1)) = Real.log ((t / (t + 1))⁻¹) := by
          rw [← Real.log_inv (t / (t + 1))]
        _ = Real.log (1 + 1 / t) := by rw [hinv]
    rw [← hmain]
    exact hgt
  · -- Upper bound: log (1 + 1 / t) ≤ 1 / t
    have hpos : 0 < 1 + 1 / t := by positivity
    have hub := Real.log_le_sub_one_of_pos hpos
    have hstep : (1 + 1 / t) - 1 = 1 / t := by ring
    simpa [hstep] using hub

end Commons.Analysis.Real