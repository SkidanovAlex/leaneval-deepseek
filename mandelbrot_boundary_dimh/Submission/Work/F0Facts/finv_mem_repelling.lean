import Mathlib
import Submission.Work.F0Facts.FinvRegion
import Submission.Work.F0Facts.Basic

namespace Work.F0Facts

open Filter Topology Set Metric
open scoped Topology

/-- The repelling region is invariant under the backward branch `finv` of `f₀`.

If `w` lies in `repelling = {w | 2 ≤ ‖1 + 4w‖ + (1 + 4w).re}`, then so does `finv w`.
Indeed `1 + 4 * finv w = -1 + 2 * sqroot w` and `(sqroot w).re ≥ 1`, so both the modulus and
the real part of `1 + 4 * finv w` are at least `1`. -/
theorem finv_mem_repelling {w : ℂ} (hw : w ∈ repelling) : finv w ∈ repelling := by
  have hs : (1 : ℝ) ≤ (sqroot w).re := one_le_re_sqroot_of_mem hw
  have hkey : 1 + 4 * finv w = -1 + 2 * sqroot w := by
    simp only [finv, sqroot]; ring
  have hre : (-1 + 2 * sqroot w).re = 2 * (sqroot w).re - 1 := by
    simp; ring
  have hnorm : 2 * (sqroot w).re - 1 ≤ ‖-1 + 2 * sqroot w‖ := by
    have h := Complex.re_le_norm (-1 + 2 * sqroot w)
    rwa [hre] at h
  show 2 ≤ ‖1 + 4 * finv w‖ + (1 + 4 * finv w).re
  rw [hkey, hre]
  linarith

end Work.F0Facts
