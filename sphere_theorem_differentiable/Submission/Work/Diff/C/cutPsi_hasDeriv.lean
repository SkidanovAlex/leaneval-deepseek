import Mathlib
import Submission.Work.Diff.C.cutoff_psi_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The derivative of the cutoff profile `cutPsi`

`cutPsi c` is the primitive of `cutRho c` normalised so that it is constant `-1 + c` on
`(-∞, -1 + c]`.  Since `cutRho c` is continuous (it is a rescaled `Real.smoothTransition`),
the fundamental theorem of calculus gives `(cutPsi c)' = cutRho c` everywhere.
-/

namespace Work.Diff.C

open MeasureTheory

/-- `cutRho c` is continuous: it is `cutW` composed with the affine map `x ↦ (x + 1 - c)/c`,
and `cutW` is continuous. -/
lemma cutRho_continuous (c : ℝ) : Continuous (cutRho c) := by
  unfold cutRho cutW
  fun_prop

/-- The candidate cutoff `cutPsi c` has derivative `cutRho c` at every point. -/
theorem cutPsi_hasDeriv {c : ℝ} (hc : 0 < c) (s : ℝ) :
    HasDerivAt (cutPsi c) (cutRho c s) s := by
  have _ := hc
  have hcont : Continuous (cutRho c) := cutRho_continuous c
  -- `cutPsi c u = (-1 + c) + ∫ x in (-1 + c)..u, cutRho c x`
  change HasDerivAt (fun u => (-1 + c) + ∫ x in (-1 + c)..u, cutRho c x) (cutRho c s) s
  exact ((hcont.integral_hasStrictDerivAt (-1 + c) s).const_add (-1 + c)).hasDerivAt

end Work.Diff.C
