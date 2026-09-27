import Mathlib
import Submission.Work.Drive.linPlanes_meet_unique

/-!
# The common point of three linear projective planes in general position

`Work.Drive.linPlanes_meet_unique` proves that three projective planes `projLine (linSub (φ k))` of one
level `c` whose `3`-dimensional subspaces `linSub (φ k) ⊆ ℝ⁴` have a one-dimensional triple
intersection meet in exactly one point of the capping space `CappingSpace ≅ (0,∞) × ℝP³`.  This file
names that point and records the two properties that make it usable as the *common value* of the
three plane charts:

* every point `q` of the level `c` whose projective class lies on all three planes *is* that point
  (`Work.Drive.eq_linCommonPt`) — this is what identifies the value of a triple of parameters at which
  the three folded plane charts agree;
* consequently the triple-parameter set of the three charts may be described as the set of triples
  whose three values are all equal to `linCommonPt` (`Work.Drive.tripleMeet_linPlaneCharts`).

The point itself is the unique point produced by `Work.Drive.linPlanes_meet_unique`: the projective
class of the line `⨅ k, linSub (φ k)`, placed on the level `c`.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

noncomputable section

/-- **The common point of three linear projective planes of one level in general position.**  It is
the single point of `CappingSpace` of level `c` lying on all three projective planes
`projLine (linSub (φ k))`; it exists and is unique by `Work.Drive.linPlanes_meet_unique`, and it is the
value that three plane charts must share at a triple parameter. -/
def linCommonPt (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (c : ℝ) (hc : 0 < c)
    (h : Module.finrank ℝ ↥(⨅ k : Fin 3, linSub (φ k)) = 1) : CappingSpace :=
  (linPlanes_meet_unique φ c hc h).choose

/-- The defining level of `Work.Drive.linCommonPt`. -/
theorem level_linCommonPt (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (c : ℝ) (hc : 0 < c)
    (h : Module.finrank ℝ ↥(⨅ k : Fin 3, linSub (φ k)) = 1) :
    ((cappingSpaceHomeoProj (linCommonPt φ c hc h)).1 : ℝ) = c :=
  (linPlanes_meet_unique φ c hc h).choose_spec.1.1

/-- The projective class of `Work.Drive.linCommonPt` lies on each of the three planes. -/
theorem mem_projLine_linCommonPt (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (c : ℝ) (hc : 0 < c)
    (h : Module.finrank ℝ ↥(⨅ k : Fin 3, linSub (φ k)) = 1) (k : Fin 3) :
    (cappingSpaceHomeoProj (linCommonPt φ c hc h)).2 ∈ projLine (linSub (φ k)) := by
  fin_cases k
  · exact (linPlanes_meet_unique φ c hc h).choose_spec.1.2.1
  · exact (linPlanes_meet_unique φ c hc h).choose_spec.1.2.2.1
  · exact (linPlanes_meet_unique φ c hc h).choose_spec.1.2.2.2

/-- Every point of the projective space of the level `c` whose class lies on all three planes is
`Work.Drive.linCommonPt`: the common point is the *unique* point with those two properties. -/
theorem eq_linCommonPt (φ : Fin 3 → Eucl 3 ≃L[ℝ] Eucl 3) (c : ℝ) (hc : 0 < c)
    (h : Module.finrank ℝ ↥(⨅ k : Fin 3, linSub (φ k)) = 1) {q : CappingSpace}
    (hq : ((cappingSpaceHomeoProj q).1 : ℝ) = c)
    (hqk : ∀ k : Fin 3, (cappingSpaceHomeoProj q).2 ∈ projLine (linSub (φ k))) :
    q = linCommonPt φ c hc h :=
  ((linPlanes_meet_unique φ c hc h).unique ⟨hq, hqk 0, hqk 1, hqk 2⟩
    ⟨level_linCommonPt φ c hc h, mem_projLine_linCommonPt φ c hc h 0,
      mem_projLine_linCommonPt φ c hc h 1, mem_projLine_linCommonPt φ c hc h 2⟩)

end

end Work.Drive
