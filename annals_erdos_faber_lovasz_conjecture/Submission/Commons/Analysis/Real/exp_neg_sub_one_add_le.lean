import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

namespace Commons.Analysis.Real

/-- For `a ≥ 0`, `exp(-a) - 1 + a ≤ exp a - 1 - a`, equivalently
`exp a - exp(-a) ≥ 2a = 2 sinh a`, which is the standard inequality
`a ≤ sinh a` for `a ≥ 0`. -/
theorem exp_neg_sub_one_add_le {a : ℝ} (ha : 0 ≤ a) :
    Real.exp (-a) - 1 + a ≤ Real.exp a - 1 - a := by
  have h : a ≤ Real.sinh a := (Real.self_le_sinh_iff).mpr ha
  rw [Real.sinh_eq] at h
  linarith

end Commons.Analysis.Real