import Mathlib
import Submission.Work.Drive.linCommonPoint
import Submission.Work.Drive.planeChain

/-!
# The triple-parameter set of three linear plane charts

Three linear plane charts `Q k = linPlaneChart (φ k) c hc` of one level, whose planes
`projLine (linSub (φ k))` have a one-dimensional triple intersection, have exactly one common value
`Work.Drive.linCommonPt` (`Work.Drive.linPlanes_meet_unique`).  Consequently the set

> `{x : (Eucl 2)³ | x ∈ (unitBox 1)³ ∧ B 0 (x 0) = B 1 (x 1) ∧ B 0 (x 0) = B 2 (x 2)}`

of parameter triples at which the three *folded* presentations `B k = diskPlane (Q k)` agree is exactly
the set of triples all of whose three values are `linCommonPt`:

> `{x | x ∈ (unitBox 1)³ ∧ ∀ k, B k (x k) = linCommonPt φ c hc h}`.

This is the description of the end contribution's bottom face that the count
`Work.Drive.ncard_linPlaneTriples_eq_one` consumes: once the common value is pinned, the count is the
product of the three fibres `B k ⁻¹ {linCommonPt}`, and each of these is a singleton off the chart's
line at infinity (`Work.Drive.existsUnique_fibre_linPlaneChart`).
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

noncomputable section

set_option maxHeartbeats 2000000

/-- **The triple-parameter set of three linear plane charts, in terms of the common point.** -/
theorem tripleMeet_linPlaneCharts (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (c : ℝ) (hc : 0 < c)
    (h : Module.finrank ℝ ↥(⨅ k : Fin 3, linSub (φ k)) = 1) :
    {x : Fin 3 → EuclideanSpace ℝ (Fin 2) |
        (∀ k, x k ∈ Submission.Drive.unitBox 1) ∧
        diskPlane (linPlaneChart (φ 0) c hc) (x 0)
          = diskPlane (linPlaneChart (φ 1) c hc) (x 1) ∧
        diskPlane (linPlaneChart (φ 0) c hc) (x 0)
          = diskPlane (linPlaneChart (φ 2) c hc) (x 2)}
      = {x : Fin 3 → EuclideanSpace ℝ (Fin 2) |
        (∀ k, x k ∈ Submission.Drive.unitBox 1) ∧
        ∀ k, diskPlane (linPlaneChart (φ k) c hc) (x k) = linCommonPt φ c hc h} := by
  ext x
  constructor
  · rintro ⟨hbox, h01, h02⟩
    have hlevel : ((cappingSpaceHomeoProj (diskPlane (linPlaneChart (φ 0) c hc) (x 0))).1 : ℝ) = c := by
      rw [diskPlane_apply]
      exact level_linPlaneChart (φ 0) c hc (sqDisk (foldBox (x 0)))
    have hclass : ∀ k : Fin 3,
        (cappingSpaceHomeoProj (diskPlane (linPlaneChart (φ 0) c hc) (x 0))).2
          ∈ projLine (linSub (φ k)) := by
      intro k
      fin_cases k
      · rw [diskPlane_apply]
        exact linPlaneChart_mem_projLine (φ 0) c hc (sqDisk (foldBox (x 0)))
      · rw [h01, diskPlane_apply]
        exact linPlaneChart_mem_projLine (φ 1) c hc (sqDisk (foldBox (x 1)))
      · rw [h02, diskPlane_apply]
        exact linPlaneChart_mem_projLine (φ 2) c hc (sqDisk (foldBox (x 2)))
    have hval0 : diskPlane (linPlaneChart (φ 0) c hc) (x 0) = linCommonPt φ c hc h :=
      eq_linCommonPt φ c hc h hlevel hclass
    refine ⟨hbox, fun k => ?_⟩
    fin_cases k
    · exact hval0
    · exact h01.symm.trans hval0
    · exact h02.symm.trans hval0
  · rintro ⟨hbox, hall⟩
    exact ⟨hbox, by rw [hall 0, hall 1], by rw [hall 0, hall 2]⟩

end

end Work.Drive
