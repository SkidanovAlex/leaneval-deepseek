import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

namespace Commons.Analysis.Real

theorem exists_cos_sin_of_sq_add_sq_eq_one {p q : ℝ} (h : p ^ 2 + q ^ 2 = 1) :
    ∃ θ : ℝ, Real.cos θ = p ∧ Real.sin θ = q := by
  have hp2 : p ^ 2 ≤ 1 := by nlinarith [sq_nonneg q]
  have habs : |p| ≤ 1 := (sq_le_one_iff_abs_le_one p).mp hp2
  have hp1 : -1 ≤ p := (abs_le.mp habs).1
  have hp2' : p ≤ 1 := (abs_le.mp habs).2
  have hq2 : q ^ 2 = 1 - p ^ 2 := by nlinarith
  by_cases hq : 0 ≤ q
  · refine ⟨Real.arccos p, Real.cos_arccos hp1 hp2', ?_⟩
    rw [Real.sin_arccos, ← hq2, Real.sqrt_sq_eq_abs, abs_of_nonneg hq]
  · have hq' : q < 0 := not_le.mp hq
    refine ⟨-Real.arccos p, ?_, ?_⟩
    · rw [Real.cos_neg, Real.cos_arccos hp1 hp2']
    · rw [Real.sin_neg, Real.sin_arccos, ← hq2, Real.sqrt_sq_eq_abs, abs_of_neg hq', neg_neg]

end Commons.Analysis.Real