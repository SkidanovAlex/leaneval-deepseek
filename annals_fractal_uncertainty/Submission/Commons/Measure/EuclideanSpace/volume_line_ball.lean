import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace Commons.Measure.EuclideanSpace

open MeasureTheory Metric Set
open scoped ENNReal InnerProductSpace

/-- **The intersection of a line with a ball.**  For a unit direction `y`, the set of parameters
`t` with `‖x + t • y‖ ≤ ρ` has Lebesgue measure at most `2ρ`.  (The function
`t ↦ ‖x + t • y‖ ^ 2` is the quadratic polynomial `t ^ 2 + 2 * inner ℝ x y * t + ‖x‖ ^ 2`, whose
leading coefficient is `1`.) -/
theorem volume_line_ball {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y : E) (hy : ‖y‖ = 1) (ρ : ℝ) :
    volume {t : ℝ | ‖x + t • y‖ ≤ ρ} ≤ ENNReal.ofReal (2 * ρ) := by
  have hinner : ∀ t : ℝ, ⟪x + t • y, y⟫_ℝ = ⟪x, y⟫_ℝ + t := by
    intro t
    rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hy]
    ring
  have hsub : {t : ℝ | ‖x + t • y‖ ≤ ρ} ⊆ Icc (-⟪x, y⟫_ℝ - ρ) (-⟪x, y⟫_ℝ + ρ) := by
    intro t ht
    change ‖x + t • y‖ ≤ ρ at ht
    have h1 : |⟪x + t • y, y⟫_ℝ| ≤ ρ := by
      have h2 := abs_real_inner_le_norm (x + t • y) y
      rw [hy, mul_one] at h2
      linarith
    rw [hinner t] at h1
    simp only [mem_Icc]
    have := abs_le.mp h1
    constructor <;> linarith
  calc volume {t : ℝ | ‖x + t • y‖ ≤ ρ}
      ≤ volume (Icc (-⟪x, y⟫_ℝ - ρ) (-⟪x, y⟫_ℝ + ρ)) := measure_mono hsub
    _ = ENNReal.ofReal ((-⟪x, y⟫_ℝ + ρ) - (-⟪x, y⟫_ℝ - ρ)) := Real.volume_Icc
    _ = ENNReal.ofReal (2 * ρ) := by congr 1; ring

end Commons.Measure.EuclideanSpace