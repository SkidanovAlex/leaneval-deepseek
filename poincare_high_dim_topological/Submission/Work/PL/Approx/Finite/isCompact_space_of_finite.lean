import Mathlib
import Submission.Work.PL.Approx.Defs

/-!
# A finite PL complex has compact underlying space

`PL.Cx N` is a `Geometry.SimplicialComplex ℝ (E N)`.  Its underlying space is the union of
the convex hulls of its faces, and each face is a `Finset (E N)`, hence a finite set whose
convex hull is compact (`Set.Finite.isCompact_convexHull`).  So if the face set is finite the
underlying space is a finite union of compact sets.
-/

namespace Work.PL.Approx.Finite

lemma isCompact_space_of_finite {N : ℕ} (K : PL.Cx N) (hK : K.faces.Finite) : IsCompact K.space := by
  rw [Geometry.SimplicialComplex.space]
  exact hK.isCompact_biUnion (fun s _ => s.finite_toSet.isCompact_convexHull ℝ)

end Work.PL.Approx.Finite
