import Mathlib

namespace Work.LinnikAreas.DhRepel

theorem integral_even_compact {L : ℝ} (hL : 0 ≤ L) {φ : ℝ → ℝ}
    (heven : ∀ v, φ (-v) = φ v) (hsupp : ∀ v, L < |v| → φ v = 0) (hint : MeasureTheory.Integrable φ) :
    ∫ v : ℝ, φ v = 2 * ∫ v in (0:ℝ)..L, φ v := by
  have hLle : -L ≤ L := by linarith
  -- `φ` vanishes off the closed interval `[-L, L]`.
  have hsupport : ∀ v ∉ Set.Icc (-L) L, φ v = 0 := by
    intro v hv
    rw [Set.mem_Icc] at hv
    rw [not_and_or, not_le, not_le] at hv
    rcases hv with hv | hv
    · have hv0 : v < 0 := by linarith
      have h : L < |v| := by rw [abs_of_neg hv0]; linarith
      exact hsupp v h
    · have hv0 : 0 < v := by linarith
      have h : L < |v| := by rw [abs_of_pos hv0]; linarith
      exact hsupp v h
  -- The global integral equals the integral over `[-L, L]`.
  have h1 : ∫ v : ℝ, φ v = ∫ v in Set.Icc (-L) L, φ v :=
    (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hsupport).symm
  -- Replace the set integral by an interval integral.
  have h2 : ∫ v in Set.Icc (-L) L, φ v = ∫ v in (-L)..L, φ v := by
    rw [intervalIntegral.integral_of_le hLle]
    exact MeasureTheory.setIntegral_congr_set
      (MeasureTheory.Ioc_ae_eq_Icc (a := -L) (b := L)).symm
  -- Split the interval at `0`.
  have h3 : ∫ v in (-L)..L, φ v = (∫ v in (-L)..0, φ v) + (∫ v in (0:ℝ)..L, φ v) := by
    have hi0 : IntervalIntegrable φ MeasureTheory.volume (-L) 0 := hint.intervalIntegrable
    have hi1 : IntervalIntegrable φ MeasureTheory.volume (0:ℝ) L := hint.intervalIntegrable
    exact (intervalIntegral.integral_add_adjacent_intervals hi0 hi1).symm
  -- Evenness identifies the two halves.
  have h4 : ∫ v in (-L)..0, φ v = ∫ v in (0:ℝ)..L, φ v := by
    have hc := intervalIntegral.integral_comp_neg (a := (0:ℝ)) (b := L) φ
    simp only [neg_zero] at hc
    rw [← hc]
    simp only [heven]
  calc ∫ v : ℝ, φ v
      = ∫ v in Set.Icc (-L) L, φ v := h1
    _ = ∫ v in (-L)..L, φ v := h2
    _ = (∫ v in (-L)..0, φ v) + (∫ v in (0:ℝ)..L, φ v) := h3
    _ = (∫ v in (0:ℝ)..L, φ v) + (∫ v in (0:ℝ)..L, φ v) := by rw [h4]
    _ = 2 * ∫ v in (0:ℝ)..L, φ v := by ring

end Work.LinnikAreas.DhRepel
