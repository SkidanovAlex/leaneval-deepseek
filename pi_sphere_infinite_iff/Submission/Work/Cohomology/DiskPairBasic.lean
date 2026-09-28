import Mathlib
import Submission.Work.Cohomology.HomologyPairSequence

set_option synthInstance.maxHeartbeats 400000

/-!
# The pair `(Dⁿ, Sⁿ⁻¹)`

Convenient names for the closed unit ball `Dⁿ ⊆ ℝⁿ` (as a topological space) and for the unit
sphere `Sⁿ⁻¹` viewed as a subset of `Dⁿ`.  The relative singular homology of this pair is the
"local homology" of an `n`-manifold and computes the (co)homology of spheres by the long exact
sequence of the pair; it is also the degree-`n` part of the Thom isomorphism for a trivial rank-`n`
bundle.
-/

open Metric

namespace Work.Cohomology

noncomputable section

/-- The closed unit ball `Dⁿ ⊆ ℝⁿ`, as a topological space. -/
abbrev diskUnit (n : ℕ) : TopCat :=
  TopCat.of (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)

/-- The unit sphere `Sⁿ⁻¹`, as a subset of `Dⁿ`. -/
abbrev sphereInUnit (n : ℕ) : Set (diskUnit n) :=
  {x | (x : EuclideanSpace ℝ (Fin n)) ∈ Metric.sphere 0 1}

end

end Work.Cohomology
