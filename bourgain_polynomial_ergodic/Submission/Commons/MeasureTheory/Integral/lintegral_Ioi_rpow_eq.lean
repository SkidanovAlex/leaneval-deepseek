import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open MeasureTheory
open scoped ENNReal Real
set_option autoImplicit false

namespace Commons.MeasureTheory.Integral

/-- The improper Lebesgue integral of `x ↦ x ^ a` over `(c, ∞)`, for `a < -1`
and `0 < c`, expressed as an `ℝ≥0∞`-valued integral of `ENNReal.ofReal`.

`∫₀ x in (c, ∞), x^a = c^(a+1) / (-(a+1))` since the antiderivative
`x^(a+1)/(a+1)` vanishes at `+∞` (`a+1 < 0`). -/
theorem lintegral_Ioi_rpow_eq (a : ℝ) (c : ℝ) (ha : a < -1) (hc : 0 < c) :
    (∫⁻ x : ℝ in Set.Ioi c, ENNReal.ofReal (x ^ a)) = ENNReal.ofReal (-c ^ (a + 1) / (a + 1)) := by
  let f : ℝ → ℝ := fun x => x ^ a
  have hfi : IntegrableOn f (Set.Ioi c) := by
    simpa [f] using integrableOn_Ioi_rpow_of_lt ha hc
  have hfnn : ∀ x ∈ Set.Ioi c, 0 ≤ f x := by
    intro x hx
    exact Real.rpow_nonneg (le_of_lt (lt_trans hc hx)) a
  have hfnn_ae : 0 ≤ᵐ[(volume : Measure ℝ).restrict (Set.Ioi c)] f := by
    refine (ae_restrict_mem measurableSet_Ioi).mono ?_
    intro x hx
    exact hfnn x hx
  have hlin : ENNReal.ofReal (∫ x : ℝ, f x ∂(volume : Measure ℝ).restrict (Set.Ioi c)) =
      ∫⁻ x : ℝ, ENNReal.ofReal (f x) ∂(volume : Measure ℝ).restrict (Set.Ioi c) := by
    exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      (μ := (volume : Measure ℝ).restrict (Set.Ioi c)) (f := f) hfi hfnn_ae
  rw [← hlin]
  congr 1
  simpa [f] using integral_Ioi_rpow_of_lt ha hc

end Commons.MeasureTheory.Integral