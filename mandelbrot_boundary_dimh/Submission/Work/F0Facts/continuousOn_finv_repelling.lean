import Mathlib
import Submission.Work.F0Facts.FinvRegion
import Submission.Work.F0Facts.Basic

/-!
# Continuity of the inverse branch `finv` on the repelling region

The branch `finv w = (-1 + √(1 + 4w))/2` of the inverse of `f₀(z) = z + z²` is a composition
of the (continuous) affine map `w ↦ 1 + 4w` with the principal square root.  The only
discontinuity of `Complex.sqrt` is along the non-positive real axis, and no `1 + 4w` with
`w ∈ repelling = {w | 2 ≤ ‖1 + 4w‖ + re (1 + 4w)}` is a non-positive real number: for such a
number the sum `‖z‖ + re z` vanishes.  Hence `finv` is continuous on `repelling`.
-/

namespace Work.F0Facts

open Filter Topology Set Metric
open scoped Topology

noncomputable section

/-- Two elementary facts about a complex number `z` that lies in the "repelling" range:
`0 ≤ z.re ∨ z.im ≠ 0` (so that `Complex.sqrt` is continuous at `z`). -/
lemma sqrt_continuousAt_of_two_le (z : ℂ) (hz : 2 ≤ ‖z‖ + z.re) :
    0 ≤ z.re ∨ z.im ≠ 0 := by
  by_contra h
  rw [not_or] at h
  obtain ⟨h1, h2⟩ := h
  have him : z.im = 0 := not_not.mp h2
  have hlt : z.re < 0 := not_le.mp h1
  have hz' : z = (z.re : ℂ) := by
    apply Complex.ext <;> simp [him]
  have hnorm : ‖z‖ = -z.re := by
    rw [hz', Complex.norm_real, Real.norm_eq_abs, abs_of_neg hlt]
    rw [Complex.ofReal_re]
  have hsum : ‖z‖ + z.re = 0 := by rw [hnorm]; ring
  have : (2 : ℝ) ≤ 0 := by linarith
  norm_num at this

theorem continuousOn_finv_repelling : ContinuousOn finv repelling := by
  intro w hw
  have hw' : 2 ≤ ‖1 + 4 * w‖ + (1 + 4 * w).re := hw
  have hre : 0 ≤ (1 + 4 * w).re ∨ (1 + 4 * w).im ≠ 0 :=
    sqrt_continuousAt_of_two_le (1 + 4 * w) hw'
  have hcont : ContinuousAt (fun y : ℂ => 1 + 4 * y) w := by fun_prop
  have hs : ContinuousAt sqroot w := by
    show ContinuousAt (fun y : ℂ => Complex.sqrt (1 + 4 * y)) w
    exact (Complex.continuousAt_sqrt hre).comp
      (f := fun y : ℂ => 1 + 4 * y) (g := Complex.sqrt) hcont
  have hfun : finv = fun y : ℂ => (-1 + sqroot y) / 2 := by funext y; rfl
  rw [hfun]
  exact ((continuousAt_const.add hs).div_const 2).continuousWithinAt

end

end Work.F0Facts
