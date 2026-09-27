import Mathlib
import Submission.Work.Drive.rotSideCount
import Submission.Work.Drive.planeChartDefs

/-!
# The core loop of a plane chart is closed

The `hloop` hypothesis of the loop-vs-chain engine `Work.Drive.odd_ncard_loopFamMeet_iff` (and of the
`famMeet` forms `Work.Drive.odd_ncard_famMeet_iff` / `Work.Drive.odd_coreSideCount_iff_of_famRegular`)
asks that each member of the loop family be a *closed* loop.  For the design's loop
`Work.Drive.coreLoop Q t = Q (exp (i π t))` this is exactly the seam clause
`z ∈ S¹ ⟹ Q (-z) = Q z` of the plane chart (`Work.Drive.IsPlaneChart`), since `exp 0 = 1` and
`exp (i π) = -1`.

This file records the two forms (bare seam clause, and `IsPlaneChart`) and the rotated version used by
the rotation form of the count (`Submission/Work/Drive/HN4_SARD_ROUTE.md` §2).
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology

noncomputable section

/-- `exp (i π t)` at `t = 0` is `1`, at `t = 1` is `-1`; this is what turns the seam clause into the
closure of the core loop. -/
lemma exp_pi_mul_I_zero : Complex.exp (Real.pi * ((0 : ℝ) : ℂ) * Complex.I) = 1 := by
  rw [show Real.pi * ((0 : ℝ) : ℂ) * Complex.I = 0 by push_cast; ring]
  exact Complex.exp_zero

lemma exp_pi_mul_I_one : Complex.exp (Real.pi * ((1 : ℝ) : ℂ) * Complex.I) = -1 := by
  rw [show Real.pi * ((1 : ℝ) : ℂ) * Complex.I = (Real.pi : ℂ) * Complex.I by push_cast; ring]
  exact Complex.exp_pi_mul_I

/-- **The core loop is closed, from the seam clause of the chart.** -/
theorem coreLoop_zero_eq_one {Q : ℂ → CappingSpace}
    (hQseam : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z) : coreLoop Q 0 = coreLoop Q 1 := by
  simp only [coreLoop, exp_pi_mul_I_zero, exp_pi_mul_I_one]
  exact (hQseam 1 (by simp)).symm

/-- **The core loop of a plane chart is closed.** -/
theorem coreLoop_zero_eq_one_of_isPlaneChart {γ : Circle → ℝ × ℝ} {hγne : ∀ x : Circle, γ x ≠ 0}
    {Q : ℂ → CappingSpace} (hQ : IsPlaneChart γ hγne Q) : coreLoop Q 0 = coreLoop Q 1 :=
  coreLoop_zero_eq_one hQ.2.2.1

/-- **The members of the rotated loop family are closed too.**  This is the `hloop` input for the
rotation form of the design's count (`regarding` the angle as the first box coordinate of the
`(2,3)` system). -/
theorem coreLoop_rotCapping_zero_eq_one {Q : ℂ → CappingSpace}
    (hQseam : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z) (u : UnitAddCircle) :
    coreLoop (fun z => rotCapping u (Q z)) 0 = coreLoop (fun z => rotCapping u (Q z)) 1 := by
  rw [coreLoop_rotCapping, coreLoop_rotCapping, coreLoop_zero_eq_one hQseam]

end

end Work.Drive
