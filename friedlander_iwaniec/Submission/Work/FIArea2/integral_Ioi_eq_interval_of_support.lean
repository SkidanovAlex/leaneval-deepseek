import Mathlib

set_option linter.unusedVariables false

namespace Work.FIArea2

/-- If `g` vanishes below `a` and above `b`, where `0 < a ≤ b`, then integrating over `(0,∞)`
agrees with integrating over any interval `[L,U]` that contains `[a,b]` (with `L ≥ 0`):
both integrals are the integral of `g` over the whole line, since `g` is supported in `[a,b]`.

The hypothesis `0 ≤ L` is not needed for the identity itself but is part of the requested
interface. -/
theorem integral_Ioi_eq_interval_of_support {g : ℝ → ℝ} {a b L U : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hL0 : 0 ≤ L) (hLa : L ≤ a) (hbU : b ≤ U)
    (hlo : ∀ x : ℝ, x < a → g x = 0) (hhi : ∀ x : ℝ, b < x → g x = 0) :
    ∫ x in Set.Ioi (0 : ℝ), g x = ∫ x in L..U, g x := by
  have hLU : L ≤ U := le_trans (le_trans hLa hab) hbU
  rw [intervalIntegral.integral_of_le hLU]
  -- Both set integrals equal the integral of `g` over the whole line.
  have h1 : ∫ x in Set.Ioi (0 : ℝ), g x = ∫ x, g x := by
    apply MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    exact hlo x (lt_of_le_of_lt (not_lt.mp hx) ha)
  have h2 : ∫ x in Set.Ioc L U, g x = ∫ x, g x := by
    rw [MeasureTheory.setIntegral_congr_set
      (MeasureTheory.Ioc_ae_eq_Icc (μ := MeasureTheory.volume))]
    apply MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [Set.mem_Icc] at hx
    rcases not_and_or.mp hx with hxL | hxU
    · exact hlo x (lt_of_lt_of_le (not_le.mp hxL) hLa)
    · exact hhi x (lt_of_le_of_lt hbU (not_le.mp hxU))
  exact h1.trans h2.symm

end Work.FIArea2
