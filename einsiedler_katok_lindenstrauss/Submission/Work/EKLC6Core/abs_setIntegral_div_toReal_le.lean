import Mathlib

namespace Work.EKLC6Core

/-- The normalised average `(∫_S f ∂ρ) / (ρ S).toReal` of a function bounded by `|f| ≤ C` is again
bounded by `C` in absolute value. -/
theorem abs_setIntegral_div_toReal_le {α : Type*} [MeasurableSpace α]
    (ρ : MeasureTheory.Measure α) (S : Set α) (f : α → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ y, |f y| ≤ C) :
    |(∫ y in S, f y ∂ρ) / (ρ S).toReal| ≤ C := by
  by_cases hS : ρ S = ⊤
  · rw [hS, ENNReal.toReal_top, div_zero, abs_zero]
    exact hC
  · have hSlt : ρ S < ⊤ := lt_top_iff_ne_top.mpr hS
    by_cases hS0 : ρ S = 0
    · have hzero : (∫ y in S, f y ∂ρ) = 0 := by
        rw [MeasureTheory.Measure.restrict_eq_zero.mpr hS0]
        simp
      rw [hzero, hS0, ENNReal.toReal_zero, div_zero, abs_zero]
      exact hC
    · have hpos : 0 < (ρ S).toReal := ENNReal.toReal_pos hS0 hS
      have hbound : |∫ y in S, f y ∂ρ| ≤ C * (ρ S).toReal := by
        have h := MeasureTheory.norm_setIntegral_le_of_norm_le_const (μ := ρ) (f := f) (s := S)
          (C := C) hSlt (fun y _ => by simpa [Real.norm_eq_abs] using hf y)
        simpa [Real.norm_eq_abs, MeasureTheory.measureReal_def] using h
      rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
      exact hbound

end Work.EKLC6Core
