import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

set_option autoImplicit false

open Filter MeasureTheory
open scoped Topology

namespace Commons.Analysis.Integral

theorem tendsto_interval_integral_atTop (f : ℝ → ℂ) (hf : MeasureTheory.Integrable f) :
    Tendsto (fun T : ℝ => ∫ y in -T..T, f y) atTop (𝓝 (∫ y : ℝ, f y)) := by
  -- The half-open intervals `Set.Ioc (-T) T` form an `AECover` of `ℝ` as `T → atTop`.
  let φ : ℝ → Set ℝ := fun T => Set.Ioc (-T) T
  have hφ : AECover (volume : Measure ℝ) atTop φ := by
    dsimp [φ]
    exact aecover_Ioc tendsto_neg_atTop_atBot tendsto_id
  -- Set integrals over an AECover of an integrable function converge to the full integral.
  have hlim : Tendsto (fun T => ∫ y in φ T, f y) atTop (𝓝 (∫ y : ℝ, f y)) :=
    hφ.integral_tendsto_of_countably_generated hf
  -- For `T ≥ 0`, the interval integral `∫ y in -T..T` agrees with the set integral
  -- over `Set.Ioc (-T) T`; the two families are eventually equal.
  exact hlim.congr' (by
    filter_upwards [eventually_ge_atTop 0] with T hT
    dsimp [φ]
    rw [intervalIntegral.integral_of_le]
    linarith)

end Commons.Analysis.Integral