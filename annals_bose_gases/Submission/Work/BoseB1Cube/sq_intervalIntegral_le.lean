import Mathlib.Analysis.Convex.Integral
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB1Cube

open MeasureTheory

/-- **Jensen / Cauchy–Schwarz for the square, on an interval.**
`(∫ s in a..b, f s)² ≤ (b - a) · ∫ s in a..b, (f s)²` for `a ≤ b`, assuming only that the square
`f²` is interval integrable.

If `a = b` both sides vanish.  If `a < b` and `f` is interval integrable, this is Jensen's
inequality for the convex function `x ↦ x²` applied to the average of `f` over the interval
(`ConvexOn.map_set_average_le` with the interval `Set.Ioc a b`, whose `volume`-measure is
`b - a`), followed by the elementary rescaling of the average.  If `f` itself is *not* interval
integrable, `∫ s in a..b, f s = 0` (`MeasureTheory.integral_undef`) while the right-hand side is
nonnegative (product of `b - a ≥ 0` with the integral of the pointwise nonnegative `f²`). -/
theorem sq_intervalIntegral_le (f : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable (fun s => f s ^ 2) MeasureTheory.volume a b) :
    (∫ s in a..b, f s) ^ 2 ≤ (b - a) * ∫ s in a..b, f s ^ 2 := by
  rcases eq_or_lt_of_le hab with h | hlt
  · subst h
    rw [intervalIntegral.integral_same, sub_self, zero_mul]
    norm_num
  · have hba : 0 < b - a := sub_pos.mpr hlt
    have hne : b - a ≠ 0 := ne_of_gt hba
    have hA : ∫ s in a..b, f s = ∫ s in Set.Ioc a b, f s := intervalIntegral.integral_of_le hab
    have hB : ∫ s in a..b, f s ^ 2 = ∫ s in Set.Ioc a b, f s ^ 2 :=
      intervalIntegral.integral_of_le hab
    rw [hA, hB]
    have hgi : IntegrableOn (fun x => f x ^ 2) (Set.Ioc a b) MeasureTheory.volume := hf.1
    have hreal : (MeasureTheory.volume : Measure ℝ).real (Set.Ioc a b) = b - a := by
      rw [MeasureTheory.measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
    by_cases hfi : IntegrableOn f (Set.Ioc a b) MeasureTheory.volume
    · have hconv : ConvexOn ℝ Set.univ (fun x : ℝ => x ^ 2) :=
        (show Even 2 by decide).convexOn_pow (𝕜 := ℝ)
      have h0 : MeasureTheory.volume (Set.Ioc a b) ≠ 0 := by
        rw [Real.volume_Ioc]
        exact ENNReal.ofReal_ne_zero_iff.mpr hba
      have ht : MeasureTheory.volume (Set.Ioc a b) ≠ ⊤ := by
        rw [Real.volume_Ioc]
        exact ENNReal.ofReal_ne_top
      have hJ := ConvexOn.map_set_average_le (μ := (MeasureTheory.volume : Measure ℝ))
        (s := Set.univ) (t := Set.Ioc a b) (f := f) (g := fun x : ℝ => x ^ 2)
        hconv (continuousOn_pow 2) isClosed_univ h0 ht
        (Filter.Eventually.of_forall (fun _ => Set.mem_univ _)) hfi hgi
      rw [MeasureTheory.setAverage_eq, MeasureTheory.setAverage_eq, smul_eq_mul, smul_eq_mul,
        hreal] at hJ
      have h1 := mul_le_mul_of_nonneg_left hJ (sq_nonneg (b - a))
      have e1 : (b - a) ^ 2 * ((b - a)⁻¹ * (∫ (x : ℝ) in Set.Ioc a b, f x)) ^ 2
          = (∫ (x : ℝ) in Set.Ioc a b, f x) ^ 2 := by field_simp
      have e2 : (b - a) ^ 2 * ((b - a)⁻¹ * (∫ (x : ℝ) in Set.Ioc a b, f x ^ 2))
          = (b - a) * (∫ (x : ℝ) in Set.Ioc a b, f x ^ 2) := by field_simp
      rw [e1, e2] at h1
      linarith
    · have hni : ¬ MeasureTheory.Integrable f
          (MeasureTheory.volume.restrict (Set.Ioc a b)) := hfi
      have hAz : ∫ s in Set.Ioc a b, f s = 0 := MeasureTheory.integral_undef hni
      have hBnn : 0 ≤ ∫ s in Set.Ioc a b, f s ^ 2 :=
        MeasureTheory.integral_nonneg (fun x => sq_nonneg (f x))
      rw [hAz]
      nlinarith [hBnn, hba]

end Work.BoseB1Cube
