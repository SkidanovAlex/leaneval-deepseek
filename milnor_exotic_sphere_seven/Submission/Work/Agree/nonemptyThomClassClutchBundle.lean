import Mathlib
import Submission.Work.Agree.thomClass_clutchBundle_one_zero
import Submission.Work.Agree.clutchAux
import Submission.Work.Agree.det_qTwist_one_zero_pos
import Submission.Work.Thom.isOrientedOver_of_det_pos

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The Thom class of `L^a = clutchBundle a 0`, for every `a : ℤ`

`Work.Thom.nonempty_thomClass_of_charts` produces a Thom class of a rank-`n` real bundle from an
oriented two-chart cover.  The bundle `clutchBundle a 0` over `S⁴ = OnePoint ℝ⁴` is trivial over the
two hemispheres `hemi0 = {p ≠ ∞}`, `hemi1 = {p ≠ ↑0}`, with transition function over the overlap
`qTwist a 0 (uDir p)`, i.e. left multiplication in `ℍ ≅ ℝ⁴` by the `a`-th power of the unit
quaternion `uDir p`.

Left multiplication by a *unit* quaternion is a rotation, so this transition has positive
determinant, and `Work.Thom.isOrientedOver_of_det_pos` turns that into the orientation input
`Work.Thom.IsOrientedOver (clutchBundle a 0) 4 hemi0 hemi1`.  The general `a` is thus the same
argument as the case `a = 1` of `Submission/Work/Agree/thomClass_clutchBundle_one_zero.lean`, with
`det_qTwist_one_zero_pos` replaced by its immediate generalisation `det_qTwist_zero_pos`.

This is the `L^a` (i.e. `L^a R^0`; Milnor's `ξ = L²R⁻¹` is `a = 2`, `b = -1`) instance of "every
`clutchBundle a b` carries a Thom class in degree `4`".
-/

namespace Work.Agree

open Work.TangentClasses

/-! ## Positivity of the determinant of the twist `qTwist a 0` -/

/-- **The determinant of the twisting map of `clutchBundle a 0` is positive for a unit quaternion.**
`qTwist a 0 q` is the real-linear map `v ↦ q^a · v` of `ℝ⁴ ≅ ℍ`, i.e. `qTwist 1 0 (q^a)`; for
`‖q‖ = 1` we have `‖q^a‖ = 1`, so the case `a = 1`
(`Work.Agree.det_qTwist_one_zero_pos`, itself `Work.Agree.detMulLeftPos`) applies. -/
theorem det_qTwist_zero_pos (a : ℤ) (q : Quaternion ℝ) (hq : ‖q‖ = 1) :
    0 < LinearMap.det ((Work.Agree.qTwist a 0 q).toLinearMap) := by
  rw [show Work.Agree.qTwist a 0 q = Work.Agree.qTwist 1 0 (q ^ a) from by
    unfold Work.Agree.qTwist
    simp only [zpow_zero, zpow_one]]
  exact det_qTwist_one_zero_pos (q ^ a) (by rw [norm_zpow, hq, one_zpow])

/-! ## The orientation of `clutchBundle a 0` over the two hemispheres -/

/-- **`clutchBundle a 0` is oriented over the cover by the two hemispheres**: the transition is
`qTwist a 0 (uDir p)`, which has positive determinant by `det_qTwist_zero_pos` since `uDir p` is a
unit quaternion (`Work.Agree.norm_uDir'`). -/
theorem isOrientedOver_clutchBundle_zero (a : ℤ) :
    Work.Thom.IsOrientedOver (clutchBundle a 0) 4 hemi0 hemi1 := by
  refine Work.Thom.isOrientedOver_of_det_pos (U := hemi0) (V := hemi1) (i := false) (j := true)
    4 (by norm_num) (by rw [finrank_euclideanSpace_fin]) (clutchBundle a 0) ?_ ?_ ?_
  · intro x hx
    exact hx
  · intro x hx
    exact hx
  · intro x
    show 0 < LinearMap.det ((qTwist a 0 (uDir (x : S4))).toLinearMap)
    exact det_qTwist_zero_pos a (uDir (x : S4)) (norm_uDir' (x : S4))

/-! ## The Thom class -/

/-- **Every `clutchBundle a 0` carries a Thom class in degree `4`**: the two hemispheres cover `S⁴`
(`hemi_cover'`), each lies in a chart of `clutchBundle a 0` (definitionally), and the orientation
over the overlap is `isOrientedOver_clutchBundle_zero`. -/
theorem nonemptyThomClassClutchBundle (a : ℤ) :
    Nonempty (Work.Thom.ThomClass (Work.Agree.clutchBundle a 0) 4) :=
  Work.Thom.nonempty_thomClass_of_charts (n := 4) (by norm_num) Bool (clutchBundle a 0)
    (U := hemi0) (V := hemi1) (i := false) (j := true) (k := false)
    isOpen_hemi0 isOpen_hemi1 hemi_cover'
    (fun x hx => hx) (fun x hx => hx) (fun x hx => hx.1)
    (isOrientedOver_clutchBundle_zero a)

end Work.Agree
