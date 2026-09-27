import Mathlib
import Submission.Work.Surf.grbDefs
import Submission.Work.Surf.grbCurve
import Submission.Work.Surf.Neutral.GrbLevel
import Submission.Work.Surf.goodRayDefs
import Submission.Work.Surf.defs
import Submission.Work.Drive.Neutral.HalfDir
import Submission.Work.Surf.Neutral.WindingEqTwoMulDegreeHalfDir
import Submission.Work.Surf.ncard_crossSet_mod_two

/-!
# (Neutral copy) `GrbTransport`

Verbatim copy of the module `Work.Surf.grbTransport` in the namespace `Work.Surf.ChordN`, with:

* every import of a module whose closure contains the declaration `Work.Drive.toC` of
  `Submission/Work/Drive/winding_eq_crossing_sum.lean` redirected to the neutral copy of that module
  (the only such channel is the import of `Submission/Work/Drive/line_crossings_even.lean`, replaced
  by `Submission/Work/Drive/Neutral/HalfDir.lean`);
* every qualified reference to the declarations of the neutral half-direction file
  (`halfDir`, `continuous_halfDir`, `halfDir_apply`, `halfDir_add_self`, `rescaleAngle`,
  `twoPiNeZero`, `toC`) redirected to `Work.Drive.NH`.

Reason: `Work.Drive.toC` is declared both in `Submission/Work/Drive/winding_eq_crossing_sum.lean` (in
the chord-parity world) and in `Submission/Work/Drive/UmlaufSetup.lean` (in the capping world), so the
two worlds cannot be imported together.  With these copies,
`Work.Surf.ChordN.chord_crossing_parity` — the strict base case of the mod-2 intersection form of
`ℝP²` — is importable next to `Work.Drive.CappingSpace`; see
`Submission/Work/Drive/cutTransportStrict.lean`.
-/
/-!
# The transport between the level set of the honest direction and the ray-meeting set

The boundary curve of the difference map of two chords, in the product model `ℝ × ℝ`, and its
identification with the ray-meeting set of the difference map.
-/

namespace Work.Surf.ChordN

open Work.Drive.NH

open Set Work.Surf.GRB Work.Drive

noncomputable section

open scoped Topology

variable {a b : ℝ → EuclideanSpace ℝ (Fin 2)}

/-! ## The transport between the level set and the ray-meeting set -/


variable {a b : ℝ → EuclideanSpace ℝ (Fin 2)}

/-- The ray-meeting set in the pair model. -/
def rayMeetP (F : ℝ × ℝ → ℝ × ℝ) (v : ℝ × ℝ) : Set (ℝ × ℝ) :=
  {p | ∃ r : ℝ, 0 < r ∧ F p = r • v}

/-- The honest direction of the boundary curve at a real parameter is the honest direction of the
curve value. -/
lemma toC_eq_gToC (z : ℝ × ℝ) : Work.Drive.NH.toC z = gToC z := by
  apply Complex.ext <;> simp [Work.Drive.NH.toC, gToC]

lemma grbDir_apply_eq (a b : ℝ → EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    grbDir a b (t : UnitAddCircle) = gDir (grbCurveR a b t) := by
  rw [grbDir, halfDir_apply]
  have h1 : grbCurve a b (t : UnitAddCircle) - 0 = grbCurveR a b t := by
    rw [sub_zero]; rfl
  rw [h1, gDir, toC_eq_gToC]

/-- **The ray-meeting condition on the boundary curve is the level condition.** -/
theorem grbCurve_mem_rayMeet_iff {v : ℝ × ℝ} (hv : v ≠ 0) (a b : ℝ → EuclideanSpace ℝ (Fin 2))
    (hint : ∀ s t : ℝ, s ∈ Set.Icc (0:ℝ) 1 → t ∈ Set.Icc (0:ℝ) 1 → a s = b t →
      s ∈ Set.Ioo (0:ℝ) 1 ∧ t ∈ Set.Ioo (0:ℝ) 1 ∧ ‖a s‖ < 1) (t : ℝ) :
    (∃ r : ℝ, 0 < r ∧ grbCurve a b (t : UnitAddCircle) = r • v) ↔
      grbDir a b (t : UnitAddCircle) = gDir v := by
  rw [grbDir_apply_eq a b t]
  have hne : grbCurveR a b t ≠ 0 := grbCurveR_ne_zero (a := a) (b := b) hint t
  exact (gDir_eq_iff hne hv).symm

/-- **The boundary ray-meeting set is the parametrised level set.** -/
theorem rayMeetP_inter_eq_image (a b : ℝ → EuclideanSpace ℝ (Fin 2))
    (hint : ∀ s t : ℝ, s ∈ Set.Icc (0:ℝ) 1 → t ∈ Set.Icc (0:ℝ) 1 → a s = b t →
      s ∈ Set.Ioo (0:ℝ) 1 ∧ t ∈ Set.Ioo (0:ℝ) 1 ∧ ‖a s‖ < 1)
    {v : ℝ × ℝ} (hv : v ≠ 0) :
    rayMeetP (grbDiff a b) v ∩ Work.Drive.sqBoxBdry
      = sqPar '' {t : ℝ | t ∈ Set.Ico (0:ℝ) 1 ∧ grbDir a b (t : UnitAddCircle) = gDir v} := by
  ext p
  constructor
  · rintro ⟨hp, hbdy⟩
    obtain ⟨t, ht, rfl⟩ := sqPar_surjOn hbdy
    refine ⟨t, ⟨ht, ?_⟩, rfl⟩
    refine (grbCurve_mem_rayMeet_iff hv a b hint t).mp ?_
    rw [grbCurve_coe]
    exact hp
  · rintro ⟨t, ⟨ht, ht'⟩, rfl⟩
    refine ⟨?_, sqPar_mem_sqBoxBdry t⟩
    have h := (grbCurve_mem_rayMeet_iff hv a b hint t).mpr ht'
    rwa [grbCurve_coe] at h

/-- The cardinality of the boundary ray-meeting set is the cardinality of the level set. -/
theorem ncard_rayMeetP_eq (a b : ℝ → EuclideanSpace ℝ (Fin 2))
    (hint : ∀ s t : ℝ, s ∈ Set.Icc (0:ℝ) 1 → t ∈ Set.Icc (0:ℝ) 1 → a s = b t →
      s ∈ Set.Ioo (0:ℝ) 1 ∧ t ∈ Set.Ioo (0:ℝ) 1 ∧ ‖a s‖ < 1)
    {v : ℝ × ℝ} (hv : v ≠ 0) :
    ((rayMeetP (grbDiff a b) v ∩ Work.Drive.sqBoxBdry : Set (ℝ × ℝ)).ncard)
      = Set.ncard {t : ℝ | t ∈ Set.Ico (0:ℝ) 1 ∧ grbDir a b (t : UnitAddCircle) = gDir v} := by
  rw [rayMeetP_inter_eq_image a b hint hv]
  exact Set.InjOn.ncard_image (s := {t : ℝ | t ∈ Set.Ico (0:ℝ) 1 ∧
    grbDir a b (t : UnitAddCircle) = gDir v}) (sqPar_injOn.mono (by
      rintro t ⟨ht, -⟩; exact ht))



end

end Work.Surf.ChordN
