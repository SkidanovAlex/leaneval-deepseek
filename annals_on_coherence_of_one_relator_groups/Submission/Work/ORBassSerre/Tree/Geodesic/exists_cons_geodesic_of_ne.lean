import Mathlib
import Submission.Work.ORBassSerre.Tree.IsTreeAPI
import Submission.Work.ORBassSerre.Tree.Convex

namespace Work.ORBassSerre.Tree.Geodesic

universe u

/-- If `x ≠ y`, the geodesic from `x` to `y` is non-trivial, so it splits as a path
`q : x ⟶ c` followed by a final edge `e : c ⟶ y`; the penultimate vertex `c` lies on the
reduced span from `x` to `y`. -/
theorem exists_cons_geodesic_of_ne {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (hT : Work.ORBassSerre.IsTree V) {x y : V} (hxy : x ≠ y) :
    ∃ (c : V) (q : Quiver.Path x c) (e : c ⟶ y),
      hT.geodesic x y = q.cons e ∧ c ∈ Work.ORBassSerre.reducedSpan x y := by
  -- A path of length zero has equal endpoints, so `x ≠ y` forces positive length.
  have hlen : (hT.geodesic x y).length ≠ 0 := fun h0 =>
    hxy (Quiver.Path.eq_of_length_zero (hT.geodesic x y) h0)
  -- A path of positive length is an initial path followed by a final edge.
  obtain ⟨c, q, e, hq⟩ :=
    (Quiver.Path.length_ne_zero_iff_eq_cons (hT.geodesic x y)).mp hlen
  refine ⟨c, q, e, hq, ?_⟩
  -- The penultimate vertex lies on the geodesic, hence in the reduced span.
  rw [hT.reducedSpan_eq, hq]
  exact (Quiver.Path.mem_vertices_cons q e).mpr
    (Or.inl (Quiver.Path.end_mem_vertices q))

end Work.ORBassSerre.Tree.Geodesic
