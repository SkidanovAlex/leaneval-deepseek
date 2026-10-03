import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Commons.Analysis.InnerProductSpace

theorem norm_smul_rpow_smul_self {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] (v : H) {p c : ℝ} (hp : 1 < p) (hc : 0 ≤ c) :
    ‖c • ((‖v‖ ^ (p - 2)) • v)‖ = c * ‖v‖ ^ (p - 1) := by
  rw [norm_smul, Real.norm_of_nonneg hc]
  congr 1
  rw [norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg v) _)]
  have h : ‖v‖ ^ (p - 2) * ‖v‖ ^ (1:ℝ) = ‖v‖ ^ ((p - 2) + 1) :=
    (Real.rpow_add' (norm_nonneg v) (by linarith : p - 2 + 1 ≠ 0)).symm
  rw [Real.rpow_one, show p - 2 + 1 = p - 1 by ring] at h
  exact h

end Commons.Analysis.InnerProductSpace