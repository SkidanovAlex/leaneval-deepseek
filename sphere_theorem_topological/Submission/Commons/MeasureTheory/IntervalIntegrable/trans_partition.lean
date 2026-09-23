import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory

namespace Commons.MeasureTheory.IntervalIntegrable

/-- **Gluing interval-integrability over a partition.** If `f` is interval-integrable on each of the
adjacent intervals `[c k, c (k+1)]` of a partition of `[a,b]` (with `c` monotone), then `f` is
interval-integrable on `[a,b]`. -/
theorem trans_partition {f : ℝ → ℝ} {N : ℕ} {c : ℕ → ℝ} {a b : ℝ}
    (hc0 : c 0 = a) (hcN : c N = b) (hmono : ∀ k < N, c k ≤ c (k + 1))
    (hpiece : ∀ k < N, IntervalIntegrable f volume (c k) (c (k + 1))) :
    IntervalIntegrable f volume a b := by
  have h := IntervalIntegrable.trans_iterate (f := f) (μ := volume) (a := c) (n := N) hpiece
  rwa [hc0, hcN] at h

end Commons.MeasureTheory.IntervalIntegrable