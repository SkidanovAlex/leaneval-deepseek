import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedVariables false

namespace Work.BW

open MeasureTheory Matrix
open scoped Pointwise

/-- Scaling the box where `|A x| ≤ 1` by the factor `2` yields the box where `|A x| ≤ 1/2`.
Since scaling a set in `ℝ^k` multiplies its Lebesgue measure by `2^k`, and the integral of the
indicator of a set is the (real) measure of that set, the two displayed quantities agree. -/
theorem volDilate {k n : ℕ} (A : Matrix (Fin n) (Fin k) ℝ) (hA : (A.transpose * A).det ≠ 0) :
    (MeasureTheory.volume {x : Fin k → ℝ | ∀ i, |(A.mulVec x) i| ≤ 1}).toReal
      = 2^k * ∫ x : Fin k → ℝ, (if ∀ i, |(A.mulVec x) i| ≤ 1/2 then (1:ℝ) else 0) := by
  -- The half-box is measurable.
  have hS2 : MeasurableSet {x : Fin k → ℝ | ∀ i, |(A.mulVec x) i| ≤ 1/2} := by measurability
  -- The integral of the indicator of the half-box is its (real) measure.
  have hint : (∫ x : Fin k → ℝ, (if ∀ i, |(A.mulVec x) i| ≤ 1/2 then (1:ℝ) else 0))
      = (MeasureTheory.volume {x : Fin k → ℝ | ∀ i, |(A.mulVec x) i| ≤ 1/2}).toReal := by
    rw [← MeasureTheory.measureReal_def]
    rw [← MeasureTheory.integral_indicator_one (μ := MeasureTheory.volume) hS2]
    congr 1 with x
    simp [Set.indicator_apply]
  -- The two boxes are related by the homothety `x ↦ 2 • x`.
  have hset : (2:ℝ) • {x : Fin k → ℝ | ∀ i, |(A.mulVec x) i| ≤ 1/2}
      = {x : Fin k → ℝ | ∀ i, |(A.mulVec x) i| ≤ 1} := by
    ext x
    rw [Set.mem_smul_set]
    constructor
    · rintro ⟨y, hy, hxy⟩
      rw [← hxy]
      intro i
      have h2 : (A.mulVec ((2:ℝ) • y)) i = 2 * (A.mulVec y) i := by
        rw [Matrix.mulVec_smul]; simp
      rw [h2, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
      have := hy i
      linarith
    · intro hx
      refine ⟨(1/2:ℝ) • x, ?_, ?_⟩
      · intro i
        have h1 : (A.mulVec ((1/2:ℝ) • x)) i = (1/2) * (A.mulVec x) i := by
          rw [Matrix.mulVec_smul]; simp
        rw [h1, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ (1/2:ℝ))]
        have := hx i
        linarith
      · rw [smul_smul]; norm_num
  -- Scaling a set in `ℝ^k` multiplies its Lebesgue measure by `2^k`.
  have hvol : MeasureTheory.volume {x : Fin k → ℝ | ∀ i, |(A.mulVec x) i| ≤ 1}
      = ENNReal.ofReal (2^k) * MeasureTheory.volume {x : Fin k → ℝ | ∀ i, |(A.mulVec x) i| ≤ 1/2} := by
    rw [← hset, MeasureTheory.Measure.addHaar_smul_of_nonneg (μ := MeasureTheory.volume) (r := 2)
      (by norm_num)]
    simp [Module.finrank_fintype_fun_eq_card]
  rw [hint, hvol, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]

end Work.BW
