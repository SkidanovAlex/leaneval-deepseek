import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace Commons.Analysis.Lp

theorem ofReal_integral_norm_rpow_eq_lintegral_enorm_rpow {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α} {H : Type*} [NormedAddCommGroup H] (h : α → H) {p : ℝ} (hp : 0 < p) (hint : MeasureTheory.Integrable (fun x => ‖h x‖ ^ p) μ) : ENNReal.ofReal (∫ x, ‖h x‖ ^ p ∂μ) = ∫⁻ x, ‖h x‖ₑ ^ p ∂μ := by
  have hfun : (fun x => ‖h x‖ₑ ^ p) = fun x => ENNReal.ofReal (‖h x‖ ^ p) := by
    funext x
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp.le]
  rw [hfun]
  exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (norm_nonneg _) p)

end Commons.Analysis.Lp