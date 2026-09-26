import ChallengeDeps
import Submission.Basic

/-!
# Passing between "distortion ratio" bounds and "intrinsic distance" bounds

The geometric arguments (sweep, topological core, systole) are naturally stated in
terms of the *bound* `intrinsicDistance K s t ≤ d * dist (curve s) (curve t)` for a
real constant `d`, while the core statement of the challenge is naturally stated in
terms of the ratios `distortionRatio K s t = intrinsicDistance K s t / dist (...)`
being `< d`.  This file records the (elementary) equivalence, using that distinct
parameters give distinct points of the curve (`Knot.injOn`), hence a nonzero chord.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Submission

/-- For distinct parameters of the fundamental interval the chord is nonzero, so
`distortionRatio` is a genuine quotient. -/
theorem dist_pos_of_ne (K : Knot) {s t : ℝ}
    (hs : s ∈ Set.Ico (0 : ℝ) (2 * Real.pi)) (ht : t ∈ Set.Ico (0 : ℝ) (2 * Real.pi))
    (hst : s ≠ t) : 0 < dist (K.curve s) (K.curve t) :=
  dist_pos.mpr fun hcon => hst (K.injOn hs ht hcon)

/-- The distortion ratio is below `d` exactly when the intrinsic distance is below
`d` times the chord. -/
theorem ratio_lt_iff {K : Knot} {s t : ℝ} (hpos : 0 < dist (K.curve s) (K.curve t))
    {d : ℝ} : distortionRatio K s t < d ↔ intrinsicDistance K s t < d * dist (K.curve s) (K.curve t) := by
  rw [distortionRatio, div_lt_iff₀ hpos]

/-- The distortion ratio is at most `d` exactly when the intrinsic distance is at
most `d` times the chord. -/
theorem ratio_le_iff {K : Knot} {s t : ℝ} (hpos : 0 < dist (K.curve s) (K.curve t))
    {d : ℝ} : distortionRatio K s t ≤ d ↔ intrinsicDistance K s t ≤ d * dist (K.curve s) (K.curve t) := by
  rw [distortionRatio, div_le_iff₀ hpos]

/-- A strict bound on all distortion ratios gives the corresponding strict bound on
intrinsic distances. -/
theorem bound_of_ratio_lt (K : Knot) {d : ℝ}
    (h : ∀ s ∈ Set.Ico (0 : ℝ) (2 * Real.pi), ∀ t ∈ Set.Ico (0 : ℝ) (2 * Real.pi),
      s ≠ t → distortionRatio K s t < d) :
    ∀ s ∈ Set.Ico (0 : ℝ) (2 * Real.pi), ∀ t ∈ Set.Ico (0 : ℝ) (2 * Real.pi), s ≠ t →
      intrinsicDistance K s t < d * dist (K.curve s) (K.curve t) :=
  fun s hs t ht hst => (ratio_lt_iff (dist_pos_of_ne K hs ht hst)).mp (h s hs t ht hst)

/-- A bound on intrinsic distances gives the corresponding bound on all distortion
ratios. -/
theorem ratio_le_of_bound (K : Knot) {d : ℝ}
    (h : ∀ s ∈ Set.Ico (0 : ℝ) (2 * Real.pi), ∀ t ∈ Set.Ico (0 : ℝ) (2 * Real.pi), s ≠ t →
      intrinsicDistance K s t ≤ d * dist (K.curve s) (K.curve t)) :
    ∀ s ∈ Set.Ico (0 : ℝ) (2 * Real.pi), ∀ t ∈ Set.Ico (0 : ℝ) (2 * Real.pi), s ≠ t →
      distortionRatio K s t ≤ d :=
  fun s hs t ht hst => (ratio_le_iff (dist_pos_of_ne K hs ht hst)).mpr (h s hs t ht hst)

end Submission
