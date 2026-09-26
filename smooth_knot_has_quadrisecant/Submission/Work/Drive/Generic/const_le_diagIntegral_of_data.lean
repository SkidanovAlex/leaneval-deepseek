import Mathlib
import Submission.Work.Drive.needleAngVelAssembly

namespace Work.Drive.Generic

open scoped Real Topology intervalIntegral
open MeasureTheory

/-- **The diagonal lower bound survives the double weighted average.**  If every individual
numerator `f u v * g u v - h u v * k u v` is at least `κ` on the square `[-1,1]²`, and `b` is a
nonnegative weight of total mass `1`, then the double weighted average of the numerators — the
diagonal term of the angular-velocity assembly — is still at least `κ`.

The proof is the two nested weighted-average inequalities: for fixed `u` the slice average of the
numerators is at least `κ` (the weight `b v ≥ 0` with total mass `1`), and then the outer weighted
average over `u` preserves the bound.  Only the integrability data of
`Work.Drive.DoubleAverageData` is needed. -/
theorem const_le_diagIntegral_of_data {b : ℝ → ℝ} {f g h k : ℝ → ℝ → ℝ} {κ : ℝ}
    (hb : Continuous b) (hb0 : ∀ u : ℝ, 0 ≤ b u)
    (hb1 : (∫ u in (-1 : ℝ)..1, b u) = 1)
    (hd1 : Work.Drive.DoubleAverageData b f g) (hd2 : Work.Drive.DoubleAverageData b h k)
    (hF : ∀ u ∈ Set.Icc (-1 : ℝ) 1, ∀ v ∈ Set.Icc (-1 : ℝ) 1,
      κ ≤ f u v * g u v - h u v * k u v) :
    κ ≤ ∫ u in (-1 : ℝ)..1, ∫ v in (-1 : ℝ)..1,
      b u * b v * (f u v * g u v - h u v * k u v) := by
  have hbInt : IntervalIntegrable b volume (-1 : ℝ) 1 := hb.intervalIntegrable _ _
  -- the crucial pointwise identity `b v * (fg - hk) = b v * fg - b v * hk`
  have hsplit : ∀ u : ℝ, (fun v : ℝ => b v * (f u v * g u v) - b v * (h u v * k u v))
      = fun v : ℝ => b v * (f u v * g u v - h u v * k u v) := by
    intro u; funext v; ring
  -- integrability of the slice integrand `v ↦ b v * (f u v * g u v - h u v * k u v)`
  have hslice : ∀ u : ℝ, IntervalIntegrable
      (fun v : ℝ => b v * (f u v * g u v - h u v * k u v)) volume (-1 : ℝ) 1 := by
    intro u
    have hint := (hd1.slice_fg u).sub (hd2.slice_fg u)
    rw [hsplit u] at hint
    exact hint
  -- the slice (inner) weighted average is at least `κ`
  have hinner : ∀ u ∈ Set.Icc (-1 : ℝ) 1,
      κ ≤ ∫ v in (-1 : ℝ)..1, b v * (f u v * g u v - h u v * k u v) := by
    intro u hu
    have hmono : (∫ v in (-1 : ℝ)..1, b v * κ)
        ≤ ∫ v in (-1 : ℝ)..1, b v * (f u v * g u v - h u v * k u v) :=
      intervalIntegral.integral_mono_on (by norm_num) (hbInt.mul_const κ) (hslice u)
        (fun v hv => mul_le_mul_of_nonneg_left (hF u hu v hv) (hb0 v))
    rwa [intervalIntegral.integral_mul_const, hb1, one_mul] at hmono
  -- integrability of the outer integrand
  have hJint : IntervalIntegrable (fun u : ℝ => b u * (∫ v in (-1 : ℝ)..1,
      b v * (f u v * g u v - h u v * k u v))) volume (-1 : ℝ) 1 := by
    have hfun : (fun u : ℝ => b u * (∫ v in (-1 : ℝ)..1,
          b v * (f u v * g u v - h u v * k u v)))
        = fun u : ℝ => b u * (∫ v in (-1 : ℝ)..1, b v * (f u v * g u v))
            - b u * (∫ v in (-1 : ℝ)..1, b v * (h u v * k u v)) := by
      funext u
      have hsub : (∫ v in (-1 : ℝ)..1, b v * (f u v * g u v - h u v * k u v))
          = (∫ v in (-1 : ℝ)..1, b v * (f u v * g u v))
            - (∫ v in (-1 : ℝ)..1, b v * (h u v * k u v)) := by
        have hint := intervalIntegral.integral_sub (hd1.slice_fg u) (hd2.slice_fg u)
        rw [hsplit u] at hint
        exact hint
      rw [hsub]; ring
    rw [hfun]
    exact hd1.outer_slice_fg.sub hd2.outer_slice_fg
  -- the target double integral is the iterated one with the constant pulled out
  have hgoal_eq : (∫ u in (-1 : ℝ)..1, ∫ v in (-1 : ℝ)..1,
        b u * b v * (f u v * g u v - h u v * k u v))
      = ∫ u in (-1 : ℝ)..1, b u * (∫ v in (-1 : ℝ)..1,
          b v * (f u v * g u v - h u v * k u v)) := by
    refine intervalIntegral.integral_congr (fun u _ => ?_)
    have hassoc : (fun v : ℝ => b u * b v * (f u v * g u v - h u v * k u v))
        = fun v : ℝ => b u * (b v * (f u v * g u v - h u v * k u v)) := by
      funext v; ring
    rw [hassoc, intervalIntegral.integral_const_mul]
  rw [hgoal_eq]
  -- the outer weighted average preserves the bound
  have houter : (∫ u in (-1 : ℝ)..1, b u * κ)
      ≤ ∫ u in (-1 : ℝ)..1, b u * (∫ v in (-1 : ℝ)..1,
          b v * (f u v * g u v - h u v * k u v)) :=
    intervalIntegral.integral_mono_on (by norm_num) (hbInt.mul_const κ) hJint
      (fun u hu => mul_le_mul_of_nonneg_left (hinner u hu) (hb0 u))
  have hleft : (∫ u in (-1 : ℝ)..1, b u * κ) = κ := by
    rw [intervalIntegral.integral_mul_const, hb1, one_mul]
  rw [hleft] at houter
  exact houter

end Work.Drive.Generic
