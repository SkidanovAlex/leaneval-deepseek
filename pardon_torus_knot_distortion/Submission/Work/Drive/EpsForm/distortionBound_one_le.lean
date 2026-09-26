import Mathlib
import Submission.Work.Sweep.Defs
import Submission.Work.Distortion.one_le_distortion

namespace Work.Drive.EpsForm

open LeanEval.KnotTheory.PardonDistortion

/-- **Every distortion bound is at least `1`.**  A knot is a non-constant closed
curve, so the two points with parameters `0` and `π` are distinct and the chord
between them has positive length.  The intrinsic distance dominates that chord
(`Work.Distortion.OneLe.dist_le_intrinsicDistance`), while the distortion
hypothesis bounds the intrinsic distance by `d` times the chord; dividing by the
positive chord gives `1 ≤ d`. -/
theorem distortionBound_one_le (K : LeanEval.KnotTheory.PardonDistortion.Knot) (d : ℝ)
    (h : Work.Sweep.IsDistortionBound K d) : 1 ≤ d := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h0 : (0 : ℝ) ∈ Set.Ico (0 : ℝ) (2 * Real.pi) := ⟨le_refl _, by linarith⟩
  have hπ : Real.pi ∈ Set.Ico (0 : ℝ) (2 * Real.pi) := ⟨hpi.le, by linarith⟩
  have hne : (0 : ℝ) ≠ Real.pi := ne_of_lt hpi
  -- the chord between the points of parameters `0` and `π` is nonzero
  have hb : 0 < dist (K.curve 0) (K.curve Real.pi) := by
    rw [dist_pos]
    intro hh
    exact hne (K.injOn h0 hπ hh)
  -- chord ≤ intrinsic distance ≤ d * chord
  have h1 : dist (K.curve 0) (K.curve Real.pi) ≤ intrinsicDistance K 0 Real.pi :=
    Work.Distortion.OneLe.dist_le_intrinsicDistance K h0 hπ
  have h2 : intrinsicDistance K 0 Real.pi ≤ d * dist (K.curve 0) (K.curve Real.pi) :=
    h 0 h0 Real.pi hπ
  have hthis : dist (K.curve 0) (K.curve Real.pi)
      ≤ d * dist (K.curve 0) (K.curve Real.pi) :=
    le_trans h1 h2
  nlinarith [hthis, hb]

end Work.Drive.EpsForm
