import Mathlib

namespace Work.FIArea7

theorem norm_integral_le_of_support {f : ℝ → ℂ} {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hb : ∀ x, ‖f x‖ ≤ B) (hv0 : ∀ x, x < 0 → f x = 0) (hvA : ∀ x, A < x → f x = 0) :
    ∫ x, ‖f x‖ ≤ A * B := by
  have _hB' : (0 : ℝ) ≤ B := hB
  -- Pointwise domination by the indicator of `[0, A]` times the bound `B`.
  have hbound : ∀ x, ‖f x‖ ≤ (Set.Icc 0 A).indicator (fun _ => B) x := by
    intro x
    by_cases hx : x ∈ Set.Icc 0 A
    · rw [Set.indicator_of_mem hx]; exact hb x
    · rw [Set.indicator_of_notMem hx]
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
      rcases hx with h | h
      · rw [hv0 x h]; simp
      · rw [hvA x h]; simp
  -- The dominating function is integrable (finite measure of `[0, A]`).
  have hint : MeasureTheory.Integrable
      (fun x => (Set.Icc 0 A).indicator (fun _ => B) x) MeasureTheory.volume := by
    rw [MeasureTheory.integrable_indicator_iff measurableSet_Icc]
    refine MeasureTheory.integrableOn_const (hs := ?_)
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hmain := MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun x => norm_nonneg (f x))) hint
    (Filter.Eventually.of_forall hbound)
  calc ∫ x, ‖f x‖ ≤ ∫ x, (Set.Icc 0 A).indicator (fun _ => B) x := hmain
    _ = A * B := by
        rw [MeasureTheory.integral_indicator_const B measurableSet_Icc, Real.volume_real_Icc,
          sub_zero, max_eq_left hA, smul_eq_mul]

end Work.FIArea7
