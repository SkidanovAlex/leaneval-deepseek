/-
# `Work.FIArea3.JointCount.sharp_defs` — the annular-sector region used by the sharp polar-box
lattice count.
-/
import Mathlib
import Submission.Work.FIArea3.JointCount.polarBox_lattice_count

namespace Work.FIArea3.JointCount

noncomputable section

/-- The annular sector `{a < |z| ≤ b, φ < arg z ≤ φ + Δ}` (the "polar box" region). -/
def annSector (a b φ Δ : ℝ) : Set ℂ :=
  {z : ℂ | a < ‖z‖ ∧ ‖z‖ ≤ b ∧ φ < Complex.arg z ∧ Complex.arg z ≤ φ + Δ}

end

end Work.FIArea3.JointCount
