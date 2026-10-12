import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBox.LatticeModel.Defs
import Submission.Work.BoseBox.LatticeModel.radial_integral_corollaries
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBox.LatticeModel

open MeasureTheory Set
open scoped Real

/-- **Tail integral of `|lhyProfile c|`.**  From the decay
`|lhyProfile c r| ≤ c³/(2r⁴)` for `r > 0`, the integral of `|lhyProfile c (‖x‖)|`
over the exterior `{‖x‖ ≥ R}` of the ball of radius `R > 0` in `Fin 3 → ℝ` is at
most `4π · c³/(2R)` — the sharp value of `∫_{‖x‖≥R} c³/(2‖x‖⁴)`.

The bound is obtained by comparing with the radial model function `c³/(2‖x‖⁴)`
whose tail integral is `4π/R` (`radial_integral_corollaries`). -/
theorem integral_tail_abs_lhyProfile_le {c : ℝ} (hc : 0 < c) {R : ℝ} (hR : 0 < R)
    (h2 : ∀ r : ℝ, 0 < r → |lhyProfile c r| ≤ c ^ 3 / (2 * r ^ 4)) :
    (∫ x in {x : Fin 3 → ℝ | R ≤ Submission.BoseGases.eucNorm3 x},
        |lhyProfile c (Submission.BoseGases.eucNorm3 x)|)
      ≤ 4 * Real.pi * (c ^ 3 / (2 * R)) := by
  set s : Set (Fin 3 → ℝ) := {x : Fin 3 → ℝ | R ≤ Submission.BoseGases.eucNorm3 x} with hs
  have hms : MeasurableSet s := by
    rw [hs]
    exact measurableSet_le measurable_const eucNorm3_measurable
  -- The `‖x‖⁻⁴` tail integral over the exterior of the ball is `4π/R`.
  have hmodel : (∫ x in s, (1 : ℝ) / (Submission.BoseGases.eucNorm3 x) ^ 4)
      = 4 * Real.pi / R := by
    rw [hs]
    exact radial_integral_corollaries.2.2.2 R hR
  -- Integrability of the radial model function on the tail, deduced from the fact
  -- that its (set) integral is the nonzero number `4π/R`.
  have hint : Integrable (s.indicator
      (fun x => (1 : ℝ) / (Submission.BoseGases.eucNorm3 x) ^ 4)) := by
    by_contra h
    have h0 : (∫ x, s.indicator
        (fun x => (1 : ℝ) / (Submission.BoseGases.eucNorm3 x) ^ 4) x) = 0 :=
      integral_undef h
    rw [integral_indicator hms, hmodel] at h0
    have hpos : (0 : ℝ) < 4 * Real.pi / R := by positivity
    exact (ne_of_gt hpos) h0
  -- Pointwise domination on the tail.
  have hle : ∀ x : Fin 3 → ℝ,
      s.indicator (fun x => |lhyProfile c (Submission.BoseGases.eucNorm3 x)|) x
        ≤ (c ^ 3 / 2) * (s.indicator
            (fun x => (1 : ℝ) / (Submission.BoseGases.eucNorm3 x) ^ 4) x) := by
    intro x
    by_cases hx : x ∈ s
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      have hxR : R ≤ Submission.BoseGases.eucNorm3 x := by
        simpa [hs] using hx
      have hpos : 0 < Submission.BoseGases.eucNorm3 x := lt_of_lt_of_le hR hxR
      calc |lhyProfile c (Submission.BoseGases.eucNorm3 x)|
          ≤ c ^ 3 / (2 * (Submission.BoseGases.eucNorm3 x) ^ 4) := h2 _ hpos
        _ = (c ^ 3 / 2) * (1 / (Submission.BoseGases.eucNorm3 x) ^ 4) := by ring
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, mul_zero]
  have hnonneg : 0 ≤ᵐ[volume] (s.indicator
      (fun x => |lhyProfile c (Submission.BoseGases.eucNorm3 x)|)) := by
    filter_upwards with x
    by_cases hx : x ∈ s
    · rw [Set.indicator_of_mem hx]; exact abs_nonneg _
    · rw [Set.indicator_of_notMem hx]; exact le_refl 0
  have hkey := integral_mono_of_nonneg hnonneg (hint.const_mul (c ^ 3 / 2))
    (Filter.Eventually.of_forall hle)
  rw [integral_indicator hms, integral_const_mul, integral_indicator hms, hmodel] at hkey
  calc (∫ x in s, |lhyProfile c (Submission.BoseGases.eucNorm3 x)|)
      ≤ (c ^ 3 / 2) * (4 * Real.pi / R) := hkey
    _ = 4 * Real.pi * (c ^ 3 / (2 * R)) := by ring

end Work.BoseBox.LatticeModel
