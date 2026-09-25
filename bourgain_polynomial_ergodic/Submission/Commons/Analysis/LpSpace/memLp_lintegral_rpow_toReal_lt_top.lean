import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

namespace Commons.Analysis.LpSpace

open MeasureTheory Filter Finset
open scoped BigOperators ENNReal Topology

/-- On a finite measure space, an `L^p` function (`p ≠ ∞`, extended exponent) has finite
`L^{p.toReal}` lintegral of the `enorm`.  This is what lets one pass from a `MemLp f p μ`
hypothesis to the real-exponent hypotheses of the transference lemmas. -/
theorem memLp_lintegral_rpow_toReal_lt_top {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsFiniteMeasure μ] {f : X → ℝ} {p : ℝ≥0∞} (hp : p ≠ ∞) (hf : MemLp f p μ) :
    ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ < ⊤ := by
  rcases eq_or_ne p 0 with rfl | hp0
  · simp only [ENNReal.toReal_zero, ENNReal.rpow_zero, lintegral_one]
    exact IsFiniteMeasure.measure_univ_lt_top
  · exact lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0 hp hf.eLpNorm_lt_top

end Commons.Analysis.LpSpace