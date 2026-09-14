import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Commons.Analysis.Calculus.contDiff_intervalIntegral_of_contDiff_moving

namespace Commons.Analysis.Calculus

open MeasureTheory Set
open scoped Topology ContDiff

/-- The primitive `x ↦ ∫ t in a..x, f t` of a smooth function `f : ℝ → ℝ` is again smooth, and its
derivative is `f`. -/
theorem contDiff_primitive_intervalIntegral {f : ℝ → ℝ} {a : ℝ}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => ∫ t in a..x, f t) ∧
      deriv (fun x => ∫ t in a..x, f t) = f := by
  constructor
  · have hF : ContDiff ℝ ∞ (fun p : ℝ × ℝ => f p.2) := by
      exact hf.comp contDiff_snd
    have h := contDiff_intervalIntegral_of_contDiff_moving (F := fun _ t : ℝ => f t)
      (a := fun _ : ℝ => a) (b := fun s : ℝ => s) hF contDiff_const contDiff_id
    simpa using h
  · funext x
    exact intervalIntegral.deriv_integral_right (a := a) (b := x) (f := f)
      (hf.continuous.intervalIntegrable a x)
      hf.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
      hf.continuous.continuousAt

end Commons.Analysis.Calculus