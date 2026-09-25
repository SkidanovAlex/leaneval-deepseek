import Mathlib.MeasureTheory.Function.LpSeminorm.Defs

namespace Commons.Analysis.MeasureTheory

theorem eLpNorm_rpow_toReal {α ε : Type*} [MeasurableSpace α] [TopologicalSpace ε] [ENorm ε]
    {μ : MeasureTheory.Measure α} {p : ENNReal} (hp0 : p ≠ 0) (hptop : p ≠ ⊤) (f : α → ε)
    (hf : MeasureTheory.AEStronglyMeasurable f μ) :
    (MeasureTheory.eLpNorm f p μ) ^ p.toReal = ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ := by
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop hf, ← ENNReal.rpow_mul,
    one_div, inv_mul_cancel₀, ENNReal.rpow_one]
  exact (ENNReal.toReal_pos hp0 hptop).ne'

end Commons.Analysis.MeasureTheory