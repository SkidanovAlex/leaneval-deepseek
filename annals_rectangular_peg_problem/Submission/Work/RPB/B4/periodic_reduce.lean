import Mathlib

namespace Work.RPB.B4

theorem periodic_reduce {X : Type*} (f : ℝ → X)
    (hper : ∀ t, f (t + 2 * Real.pi) = f t) (t : ℝ) :
    ∃ (k : ℤ) (t' : ℝ), t' ∈ Set.Ico (0:ℝ) (2 * Real.pi) ∧
      t = t' + k • (2 * Real.pi) ∧ f t = f t' := by
  have hp : Function.Periodic f (2 * Real.pi) := hper
  have hcpos : (0:ℝ) < 2 * Real.pi := by positivity
  have hcne : (2 * Real.pi : ℝ) ≠ 0 := ne_of_gt hcpos
  have h2 : t = Int.fract (t / (2 * Real.pi)) * (2 * Real.pi)
        + ⌊t / (2 * Real.pi)⌋ • (2 * Real.pi) := by
    rw [zsmul_eq_mul (2 * Real.pi), ← add_mul, Int.fract_add_floor]
    exact (div_mul_cancel₀ t hcne).symm
  refine ⟨⌊t / (2 * Real.pi)⌋, Int.fract (t / (2 * Real.pi)) * (2 * Real.pi), ?_, h2, ?_⟩
  · rw [Set.mem_Ico]
    exact ⟨mul_nonneg (Int.fract_nonneg _) hcpos.le,
      mul_lt_of_lt_one_left hcpos (Int.fract_lt_one _)⟩
  · conv_lhs => rw [h2]
    exact (hp.zsmul ⌊t / (2 * Real.pi)⌋) (Int.fract (t / (2 * Real.pi)) * (2 * Real.pi))

end Work.RPB.B4
