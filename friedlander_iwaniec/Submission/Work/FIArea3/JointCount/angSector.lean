/-
# `Work.FIArea3.JointCount.angSector`

A general "angular annular sector" `{a < ‖z‖ ∧ ‖z‖ ≤ b ∧ arg z ∈ A}`, generalising
`annSector` (which uses a single interval `(φ, φ+Δ]`).  This is the shape whose convex hull is
estimated by `convexHull_annSector_gap_le`.
-/
import Mathlib

namespace Work.FIArea3.JointCount

noncomputable section

/-- The angular annulus sector `{z : ℂ | a < ‖z‖ ∧ ‖z‖ ≤ b ∧ arg z ∈ A}`. -/
def angSector (a b : ℝ) (A : Set ℝ) : Set ℂ :=
  {z : ℂ | a < ‖z‖ ∧ ‖z‖ ≤ b ∧ Complex.arg z ∈ A}

end

end Work.FIArea3.JointCount
