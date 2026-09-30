import Mathlib
import Submission.Work.Cohomology.HomologyPairSequence

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


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
