import Mathlib

open MeasureTheory
open scoped Interval Topology

namespace Work.Analysis.Abel

/-- **Integrability of a power with a singular endpoint times a continuous function.**
For `q > -1`, `x ≤ b` and `f` continuous on `[x,b]`, the function
`σ ↦ (σ - x)^q * f σ` is interval-integrable on `[x,b]`.  (For `q < 0` the factor
`(σ-x)^q` blows up at the left endpoint, but the singularity is integrable; the proof
bounds `|f|` by a constant on the compact interval and compares with the integrable
function `C * (σ-x)^q`, using `intervalIntegral.intervalIntegrable_rpow'` together with
`IntervalIntegrable.comp_add_right` and `IntervalIntegrable.mono_fun'`.) -/
theorem intervalIntegrable_rpow_sub_mul {q : ℝ} (hq : -1 < q) {x b : ℝ} (hxb : x ≤ b)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc x b)) :
    IntervalIntegrable (fun σ : ℝ => (σ - x) ^ q * f σ) volume x b := by
  -- The pure power `τ ↦ τ ^ q` is integrable on `[0, b - x]` because `q > -1`.
  have hr : IntervalIntegrable (fun τ : ℝ => τ ^ q) volume 0 (b - x) :=
    intervalIntegral.intervalIntegrable_rpow' hq
  -- Translate it to the interval `[x, b]`, turning `τ` into `σ - x`.
  have hr' : IntervalIntegrable (fun σ : ℝ => (σ - x) ^ q) volume x b := by
    have h := hr.comp_add_right (-x)
    rw [show (0 : ℝ) - -x = x by ring, show b - x - -x = b by ring] at h
    simpa [sub_eq_add_neg] using h
  -- `f` is continuous on the compact interval `[x, b]`, so multiplying is legitimate.
  have hf' : ContinuousOn f (Set.uIcc x b) := by
    rw [Set.uIcc_of_le hxb]; exact hf
  exact hr'.mul_continuousOn hf'

end Work.Analysis.Abel
