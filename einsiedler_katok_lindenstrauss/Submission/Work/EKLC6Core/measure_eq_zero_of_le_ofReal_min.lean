import Mathlib

namespace Work.EKLC6Core

/-- If a measure `μ s` is bounded by `ofReal (m * min 1 (η / δ))` for every `η > 0`,
with `δ > 0` and `m ≥ 0`, then `μ s = 0`: letting `η → 0` drives the bound to `0`. -/
theorem measure_eq_zero_of_le_ofReal_min {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {s : Set α} {δ m : ℝ} (hδ : 0 < δ) (hm : 0 ≤ m)
    (h : ∀ η : ℝ, 0 < η → μ s ≤ ENNReal.ofReal (m * min 1 (η / δ))) :
    μ s = 0 := by
  -- For an arbitrary real `ε > 0`, choose `η = δ * (ε / (m + 1)) > 0`.
  -- Then `m * min 1 (η / δ) ≤ m * (ε / (m + 1)) ≤ ε`.
  have key : ∀ ε : ℝ, 0 < ε → μ s ≤ ENNReal.ofReal ε := by
    intro ε hε
    have hm1 : 0 < m + 1 := by linarith
    set η : ℝ := δ * (ε / (m + 1)) with hη
    have hηpos : 0 < η := by
      rw [hη]; positivity
    have hh := h η hηpos
    have hdiv : η / δ = ε / (m + 1) := by
      rw [hη]; field_simp
    have hmin : min 1 (η / δ) ≤ ε / (m + 1) := by
      rw [hdiv]
      exact min_le_right _ _
    have hmul : m * min 1 (η / δ) ≤ m * (ε / (m + 1)) :=
      mul_le_mul_of_nonneg_left hmin hm
    have hle : m * (ε / (m + 1)) ≤ ε := by
      rw [← mul_div_assoc]
      rw [div_le_iff₀ hm1]
      nlinarith [hm, hε.le]
    exact hh.trans (ENNReal.ofReal_le_ofReal (hmul.trans hle))
  refine le_antisymm ?_ zero_le
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  have hε' : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  have hk := key (ε : ℝ) hε'
  simpa only [zero_add, ENNReal.coe_nnreal_eq] using hk

end Work.EKLC6Core
