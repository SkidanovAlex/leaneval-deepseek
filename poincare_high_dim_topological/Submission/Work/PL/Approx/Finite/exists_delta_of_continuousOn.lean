import Mathlib
import Submission.Work.PL.Approx.Defs

/-!
# Uniform continuity of a continuous function on a finite simplicial complex

`Work.PL.Approx.Finite.exists_delta_of_continuousOn` : a function which is continuous on the
underlying space `K.space` of a finite simplicial complex `K` (i.e. `K.faces` is finite) is
uniformly continuous there.

This is the Heine–Cantor theorem for `K.space`: a finite union of simplices is compact, and a
function continuous on a compact set is uniformly continuous on it.
-/

open Set Metric

namespace Work.PL.Approx.Finite

/-- The underlying space of a simplicial complex with finitely many faces is compact: it is the
finite union of the (compact) convex hulls of those faces. -/
theorem isCompact_space_of_finite_faces {N : ℕ} (K : PL.Cx N) (hK : K.faces.Finite) :
    IsCompact K.space := by
  rw [Geometry.SimplicialComplex.space]
  exact hK.isCompact_biUnion fun s _ => (s.finite_toSet).isCompact_convexHull ℝ

lemma exists_delta_of_continuousOn {N : ℕ} (K : PL.Cx N) (hK : K.faces.Finite) {X : Type*} [PseudoMetricSpace X]
    (f : PL.E N → X) (hf : ContinuousOn f K.space) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x ∈ K.space, ∀ y ∈ K.space, dist x y < δ → dist (f x) (f y) < ε := by
  have hu := (isCompact_space_of_finite_faces K hK).uniformContinuousOn_of_continuous hf
  rw [Metric.uniformContinuousOn_iff] at hu
  exact hu ε hε

end Work.PL.Approx.Finite
