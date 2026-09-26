import Mathlib
import Submission.Work.CoreTopology.Disk
import Submission.Work.Drive.Mono.interiorInter_discParam
import Submission.Work.Drive.Mono.emptyInterior_discParam

/-!
# Gluing two convex discs along a common boundary segment

`Work.Drive.Mono.exists_discParam_of_two_convex_glued`: if `A` and `B` are compact convex subsets of
`ℝ²` with non-empty interiors whose intersection contains two distinct points, then `A ∪ B` is the
image of the closed unit disc under an injective continuous map which carries the unit circle onto
`frontier (A ∪ B)`.

The proof is the case split on whether the interiors of `A` and `B` meet.

* If they do (in particular if one of the two sets contains the other), `A ∪ B` is star-shaped about
  a common interior point and the radial map built from the gauges of `A - x` and of `B - x` is a
  parametrisation: `Work.Drive.Mono.interiorInter_discParam`.

* If they do not, the two sets are tangent along a line and `A ∩ B` is a nondegenerate segment lying
  in `frontier A ∩ frontier B`; the union is the gluing of two "half discs", obtained by
  `Work.Drive.Mono.emptyInterior_discParam` (which glues two half-disc parametrisations of `A` and of
  `B` along their common diameter, the diameter being mapped affinely onto the shared segment).
-/

namespace Work.Drive.Mono

open Set

/-- **The union of two compact convex planar sets meeting in at least two points is an image of the
closed disc.** -/
theorem exists_discParam_of_two_convex_glued (A B : Set (EuclideanSpace ℝ (Fin 2)))
    (hAc : Convex ℝ A) (hAcl : IsCompact A) (hAne : (interior A).Nonempty)
    (hBc : Convex ℝ B) (hBcl : IsCompact B) (hBne : (interior B).Nonempty)
    (h2 : ∃ x : EuclideanSpace ℝ (Fin 2), x ∈ A ∩ B ∧
      ∃ y : EuclideanSpace ℝ (Fin 2), y ∈ A ∩ B ∧ x ≠ y) :
    ∃ e : C(Metric.closedBall (0 : ℂ) 1, EuclideanSpace ℝ (Fin 2)),
      Function.Injective e ∧ Set.range e = A ∪ B ∧
      Set.range (fun θ : ℝ => e (Work.CoreTopology.circlePoint θ)) = frontier (A ∪ B) := by
  by_cases h : (interior (A ∩ B)).Nonempty
  · exact interiorInter_discParam A B hAc hAcl hAne hBc hBcl hBne h
  · exact emptyInterior_discParam A B hAc hAcl hAne hBc hBcl hBne h2 h

end Work.Drive.Mono
