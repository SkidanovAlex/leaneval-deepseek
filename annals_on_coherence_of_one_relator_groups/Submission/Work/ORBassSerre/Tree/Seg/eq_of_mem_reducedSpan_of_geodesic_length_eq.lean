import Mathlib
import Submission.Work.ORBassSerre.Tree.Geodesic.mem_geodesic_length_eq
import Submission.Work.ORBassSerre.Tree.IsTreeAPI

namespace Work.ORBassSerre.Tree.Seg

/-- In a tree, a vertex `c` of the geodesic segment from `a` to `b` whose distance from `a`
equals the distance from `a` to `b` must be the endpoint `b`: along the geodesic the distance
from `a` strictly increases, and `b` is the unique vertex at the maximal distance. -/
theorem eq_of_mem_reducedSpan_of_geodesic_length_eq {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (hT : Work.ORBassSerre.IsTree V) {a b c : V}
    (hc : c ∈ Work.ORBassSerre.reducedSpan a b)
    (h : (hT.geodesic a c).length = (hT.geodesic a b).length) : c = b := by
  have hc' : c ∈ (hT.geodesic a b).vertices := (hT.reducedSpan_eq a b).le hc
  exact Work.ORBassSerre.Tree.Geodesic.mem_geodesic_length_eq hT hc'
    (hT.end_mem_geodesic a b) h

end Work.ORBassSerre.Tree.Seg
