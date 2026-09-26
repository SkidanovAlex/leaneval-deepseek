import Mathlib
import Submission.Work.Sweep.Defs
import Submission.Work.Distortion.one_le_distortion

/-!
# A distortion bound bounds the distortion

`distortion K` is, by definition, the supremum of the extended nonnegative reals
`ENNReal.ofReal (distortionRatio K s t)`, over pairs `s ≠ t` of parameters in the
half-open fundamental interval `[0, 2π)`.  Here `distortionRatio K s t` is the
quotient of the intrinsic (arclength) distance by the Euclidean chord.

A distortion bound `IsDistortionBound K d` says that for *every* pair of
parameters in `[0, 2π)` the intrinsic distance is at most `d` times the chord,
i.e. the ratio of intrinsic distance to chord is at most `d` whenever the chord
is non-zero.  Since the chord is non-zero exactly when the two parameters
differ (the parametrisation is injective on the fundamental interval), every
element of the set whose supremum defines `distortion` is at most
`ENNReal.ofReal d`, whence `distortion K ≤ ENNReal.ofReal d`.

This is the converse direction of the definition of `IsDistortionBound`, which
is used throughout the integral-geometric estimates of the sweep.
-/

noncomputable section

open LeanEval.KnotTheory.PardonDistortion
open scoped ENNReal

namespace Work.PinchCounted

theorem distortion_le_of_isDistortionBound {K : LeanEval.KnotTheory.PardonDistortion.Knot} {d : ℝ} (hd : 0 ≤ d) (h : Work.Sweep.IsDistortionBound K d) : LeanEval.KnotTheory.PardonDistortion.distortion K ≤ ENNReal.ofReal d := by
  change sSup {e : ℝ≥0∞ | ∃ s ∈ Set.Ico (0 : ℝ) (2 * Real.pi),
      ∃ t ∈ Set.Ico (0 : ℝ) (2 * Real.pi),
        s ≠ t ∧ e = ENNReal.ofReal (distortionRatio K s t)} ≤ ENNReal.ofReal d
  rw [sSup_le_iff]
  rintro e ⟨s, hs, t, ht, hst, rfl⟩
  -- the chord between two distinct points of the fundamental interval is non-zero
  have hD : 0 < dist (K.curve s) (K.curve t) := by
    rw [dist_pos]
    intro hh
    exact hst (K.injOn hs ht hh)
  rw [ENNReal.ofReal_le_ofReal_iff hd, distortionRatio, div_le_iff₀ hD]
  exact h s hs t ht

end Work.PinchCounted
