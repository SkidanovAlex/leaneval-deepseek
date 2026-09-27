import Mathlib
import Submission.Work.Drive.encodedEndData

namespace Work.Drive

open scoped Manifold Topology

-- the same elaboration setting as in `encodedEndData.lean`: the tangent spaces of `Projectivization ℝ (Eucl 3)`
-- at distinct points are *definitionally* equal only at full transparency, and the class-level regularity
-- statements (unions/intersections of ranges of `mfderiv`s based at different points) need that.
set_option backward.isDefEq.respectTransparency false

/-- The class-level end-triple regularity is invariant under the cyclic permutation of the three
maps.  `EndTripleReg F A B` asks, at every common value `v` of `F`, `A` and `B`, for injectivity of
the three class differentials at the (unique, by the matching values) preimages of `v` and for
triviality of the intersection of their ranges.  The conditions are therefore symmetric in the three
maps, and reindexing the triple `(y₀,y₁,y₂) ↦ (y₂,y₀,y₁)` turns the statement about `(F,A,B)` into
the statement about `(A,B,F)`. -/
theorem endTripleReg_cyclic {F A B : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3)}
    (h : Work.Drive.EndTripleReg F A B) :
    Work.Drive.EndTripleReg A B F := by
  intro y₀ y₁ y₂ hAB hAF
  obtain ⟨hF, hA, hB, hI⟩ := h y₂ y₀ y₁ hAF.symm (hAF.symm.trans hAB)
  refine ⟨hA, hB, hF, ?_⟩
  rw [← hI]
  ac_rfl

end Work.Drive
