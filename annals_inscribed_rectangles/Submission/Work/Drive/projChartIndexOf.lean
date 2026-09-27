import Mathlib
import Submission.Work.Drive.projCharted

/-!
# The canonical chart index of a point of `ℝPⁿ` for the transparent structure

`Work.Drive.projCharted n` picks, at every point `p`, the classical affine chart
`Work.Drive.projChart (Classical.choose (Work.Drive.exists_mem_projChartSource p))`.  This file names
the index and records that this *is* the chart, so that a caller who wants to verify a smoothness or
transversality statement in coordinates can instantiate the projective chart at a point without
carrying the `Classical.choose` term around.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff LinearAlgebra.Projectivization

noncomputable section

/-- **The index of the canonical projective chart at a point of `ℝPⁿ`.** -/
def projChartIndexOf {n : ℕ} (p : Projectivization ℝ (Eucl n)) : Fin (n + 1) :=
  Classical.choose (exists_mem_projChartSource p)

/-- The canonical index really is a chart index at the point. -/
lemma projChartIndexOf_spec {n : ℕ} (p : Projectivization ℝ (Eucl n)) :
    p ∈ projChartSource (projChartIndexOf p) :=
  Classical.choose_spec (exists_mem_projChartSource p)

/-- **The chart of `projCharted n` at `p` is `projChart (projChartIndexOf p)`** — by definition. -/
lemma projCharted_chartAt_eq_projChart {n : ℕ} (p : Projectivization ℝ (Eucl n)) :
    (@chartAt (EuclideanSpace ℝ (Fin n)) _ (Projectivization ℝ (Eucl n)) _
        (Work.Drive.projCharted n) p) = Work.Drive.projChart (projChartIndexOf p) := rfl

end

end Work.Drive
