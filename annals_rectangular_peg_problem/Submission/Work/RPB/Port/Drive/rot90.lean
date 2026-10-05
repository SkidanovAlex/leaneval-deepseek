import Mathlib
import Submission.Work.RPB.Port.Geometry

/-!
# The right-angle rotation of the plane

`rot90 v = (-v.2, v.1)` is the rotation of `v ∈ ℝ × ℝ` by `π/2`; it is the basic geometric operation
used to turn a chord of a plane curve into the "perpendicular chord through the same midpoint", i.e.
to build the square having a given chord as a diagonal.

This module is a shared helper for `Work.RPB.Port.Drive.inscribed_square` and for the auxiliary lemma
`Work.RPB.Port.Drive.exists_inscribed_square` (the classical inscribed square theorem).
-/

set_option autoImplicit false
noncomputable section

namespace Work.RPB.Port.Drive

/-- Rotation by a right angle in the plane, `(x,y) ↦ (-y,x)`. -/
def rot90 (v : ℝ × ℝ) : ℝ × ℝ := (-v.2, v.1)

@[simp] lemma rot90_fst (v : ℝ × ℝ) : (rot90 v).1 = -v.2 := rfl
@[simp] lemma rot90_snd (v : ℝ × ℝ) : (rot90 v).2 = v.1 := rfl

@[simp] lemma rot90_zero : rot90 (0 : ℝ × ℝ) = 0 := by ext <;> simp [rot90]

@[simp] lemma rot90_neg (v : ℝ × ℝ) : rot90 (-v) = -rot90 v := rfl

@[simp] lemma rot90_add (v w : ℝ × ℝ) : rot90 (v + w) = rot90 v + rot90 w := by
  ext <;> simp [rot90] <;> ring

@[simp] lemma rot90_smul (c : ℝ) (v : ℝ × ℝ) : rot90 (c • v) = c • rot90 v := by
  ext <;> simp [rot90]

lemma rot90_ne_zero {v : ℝ × ℝ} (hv : v ≠ 0) : rot90 v ≠ 0 := by
  intro h
  apply hv
  have h1 : v.2 = 0 := by
    have := congrArg Prod.fst h
    simpa [rot90] using this
  have h2 : v.1 = 0 := by
    have := congrArg Prod.snd h
    simpa [rot90] using this
  exact Prod.ext h2 h1

lemma eucNorm_rot90 (v : ℝ × ℝ) :
    Work.RPB.Port.Geometry.eucNorm (rot90 v) = Work.RPB.Port.Geometry.eucNorm v := by
  unfold Work.RPB.Port.Geometry.eucNorm
  congr 1
  simp [Work.RPB.Port.Geometry.eucDot, rot90]
  ring

end Work.RPB.Port.Drive
