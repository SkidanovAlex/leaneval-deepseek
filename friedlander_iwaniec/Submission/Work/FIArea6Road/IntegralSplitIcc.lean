import Mathlib

namespace Work.FIArea6Road

open MeasureTheory

theorem IntegralSplitIcc (f : ℝ → ℂ) (T : ℝ) (hf : MeasureTheory.Integrable f) :
    (∫ t, f t) = (∫ t in (-T)..T, f t) + (∫ t in Set.Ioi T, f t) + (∫ t in Set.Iio (-T), f t) := by
  -- Split the tail `Ioi (-T)` into the interval `(-T)..T` followed by `Ioi T`.
  have h1 : (∫ t in (-T)..T, f t) + (∫ t in Set.Ioi T, f t) = ∫ t in Set.Ioi (-T), f t :=
    intervalIntegral.integral_interval_add_Ioi hf.integrableOn hf.integrableOn
  -- `Ici (-T)` and `Ioi (-T)` differ only at the point `-T`, of zero Lebesgue measure.
  have hIci : (∫ t in Set.Ici (-T), f t) = ∫ t in Set.Ioi (-T), f t :=
    integral_Ici_eq_integral_Ioi
  -- The two half-lines `Iio (-T)` and `Ioi (-T)` cover `ℝ`.
  have h2 : (∫ t in Set.Iio (-T), f t) + (∫ t in Set.Ioi (-T), f t) = ∫ t, f t := by
    have := intervalIntegral.integral_Iio_add_Ici (f := f) (b := -T) hf.integrableOn hf.integrableOn
    rwa [hIci] at this
  rw [h1]
  simpa [add_comm] using h2.symm

end Work.FIArea6Road
