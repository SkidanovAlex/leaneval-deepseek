import Mathlib
import Submission.Work.Drive.framedPolarDefs

namespace Work.Drive

/-- The slice of the framed star-shaped interpolation depends analytically on
both parameters (with the parameter pair written as `(t, s)` so that
`p.2 = s` and `p.1 = t`). -/
theorem contDiff_framedSliceFamily {lam psi : ℝ → ℝ} (c : LeanEval.KnotTheory.Quadrisecant.Space)
    {g : ℝ → LeanEval.KnotTheory.Quadrisecant.Space × LeanEval.KnotTheory.Quadrisecant.Space}
    (hlam : ContDiff ℝ ⊤ lam) (hpsi : ContDiff ℝ ⊤ psi) (hg : ContDiff ℝ ⊤ g) :
    ContDiff ℝ ⊤ (fun p : ℝ × ℝ => Work.Drive.framedSlice lam psi c g p.2 p.1) := by
  simp only [framedSlice, starRad, starAngle]
  rw [contDiff_piLp (p := 2)]
  intro i
  fin_cases i <;> simp <;> fun_prop

end Work.Drive
