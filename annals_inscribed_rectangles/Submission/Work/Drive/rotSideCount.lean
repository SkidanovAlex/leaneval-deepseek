import Mathlib
import Submission.Work.Drive.designCount
import Submission.Work.Drive.rotSweepEquivariance
import Submission.Work.Drive.planeSq_rot

/-!
# The rotation invariance of the design's count, and the fixed-plane form of `designCount`

The design's count `Work.Drive.designCount` compares the core loop of the chart with the clamped sweep
of the rotated plane.  This file proves the two rotation identities that turn it into a count of a
*loop family* against a *fixed plane presentation* — the layout in which the loop-family engine
`Work.Drive.odd_ncard_loopFamMeet_iff` (and hence the Sard/`good family` route to the locality `hn4`)
applies:

* `Work.Drive.coreSideCount_rotCapping` — **rotation invariance**: rotating the whole configuration
  (chart *and* plane) does not change the number of meets;
* `Work.Drive.coreSideCount_rotPresentation` — hence the count of the chart at angle `u` against the
  rotated plane equals the count of the *rotated chart* `rotCapping (-u) ∘ Q` against the **fixed**
  plane `rotPresentation Q 0`.  This is the identity that removes the angle from the chain side,
  leaving a family of loops (the `2`-chain `a ↦ coreLoop (rotCapping (-a) ∘ Q)`) against one fixed
  `3`-chain — exactly the `(2,3)` `chartDiff` layout.

**Correction recorded while proving this (it fixes a docstring).**  `rotCapping` does *not* commute
with `linCapping A`: by `Work.Drive.rotCapping_linCapping`,
`rotCapping t ∘ linCapping A = linCapping (diagRotL t * A * (diagRotL t)⁻¹) ∘ rotCapping t`, i.e. a
class perturbation is *conjugated* by the rotation.  In particular the assertion in
`Drive/designCount.lean`'s docstring that `linCapping A' ∘ rotPresentation Q w =
rotPresentation (linCapping A' ∘ Q) w` "is the rotation family of one perturbed chart" is **false**:
the family `w ↦ linCapping A' ∘ rotPresentation Q w` is the rotation family of one chart only after
conjugating the perturbation by `diagRotL w`.  The *definitions* and `hn1` (which is definitional) are
unaffected, but any argument that treats that family as "one chart rotated" must carry the
conjugation; in particular the perturbed form of `coreSideCount_rotPresentation` has
`linCapping (diagRotL (-t) * A * (diagRotL (-t))⁻¹)` on the fixed side.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology

noncomputable section

/-- **The core loop of a rotated chart is the rotation of the core loop.** -/
lemma coreLoop_rotCapping (Q : ℂ → CappingSpace) (u : UnitAddCircle) (t : ℝ) :
    coreLoop (fun z => rotCapping u (Q z)) t = rotCapping u (coreLoop Q t) := rfl

/-- **The rotated plane presentation is the rotation of the plane at angle zero.**  (Either side is
`y ↦ rotCapping u (Q (sqDisk (foldBox y)))`.) -/
lemma rotPresentation_apply_eq_rotCapping (Q : ℂ → CappingSpace) (u : UnitAddCircle)
    (y : EuclideanSpace ℝ (Fin 2)) :
    rotPresentation Q u y = rotCapping u (rotPresentation Q (0 : UnitAddCircle) y) := by
  simp only [rotPresentation, diskPlane_apply, rotCapping_zero, id_eq]

/-- **The negative rotation of the plane at angle `u` is the plane at angle zero.** -/
lemma rotCapping_neg_rotPresentation (Q : ℂ → CappingSpace) (u : UnitAddCircle) :
    (fun y => rotCapping (-u) (rotPresentation Q u y)) = rotPresentation Q (0 : UnitAddCircle) := by
  funext y
  rw [rotPresentation_apply_eq_rotCapping, ← rotCapping_add_apply, add_neg_cancel, rotCapping_zero]
  rfl

/-- **The rotation invariance of the design's count.**  Rotating the whole configuration — the chart
*and* the plane presentation — by `u` does not change the number of meets of the core loop with the
clamped sweep. -/
theorem coreSideCount_rotCapping (Q : ℂ → CappingSpace) (c : ℝ)
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace) (u : UnitAddCircle) :
    coreSideCount Q c P
      = coreSideCount (fun z => rotCapping u (Q z)) c (fun y => rotCapping u (P y)) := by
  rw [coreSideCount, coreSideCount]
  have h : coreMeet Q c P
      = coreMeet (fun z => rotCapping u (Q z)) c (fun y => rotCapping u (P y)) := by
    ext q
    rw [coreMeet, coreMeet]
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, by rw [coreLoop_rotCapping, clampedSweep_rotCapping, h3]⟩
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, h2, ?_⟩
      rw [coreLoop_rotCapping, clampedSweep_rotCapping] at h3
      exact rotCapping_injective u h3
  rw [h]

/-- **The design's count at the angle `u`, with the plane side frozen.**  Rotating the chart by `-u`
and keeping the plane at angle zero gives the same count: the rotated chart's core loop against the
*fixed* plane presentation `rotPresentation Q 0`.  This is the form in which the angle is a
*box coordinate* of a loop-vs-chain system (the `(2,3)` layout of
`Work.Drive.odd_ncard_loopFamMeet_iff`). -/
theorem coreSideCount_rotPresentation (Q : ℂ → CappingSpace) (c : ℝ) (u : UnitAddCircle) :
    coreSideCount Q c (rotPresentation Q u)
      = coreSideCount (fun z => rotCapping (-u) (Q z)) c (rotPresentation Q (0 : UnitAddCircle)) := by
  rw [coreSideCount_rotCapping Q c (rotPresentation Q u) (-u),
    rotCapping_neg_rotPresentation]

end

end Work.Drive
