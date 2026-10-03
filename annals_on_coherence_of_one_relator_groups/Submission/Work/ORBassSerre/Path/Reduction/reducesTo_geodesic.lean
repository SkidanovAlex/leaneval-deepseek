import Mathlib
import Submission.Work.ORBassSerre.Tree.IsTreeAPI
import Submission.Work.ORBassSerre.Tree.Reduction.qpath_exists_reducesTo_isReduced

namespace Work.ORBassSerre.Path.Reduction

/-- In a tree, every path reduces, by deleting backtracks, to the unique reduced path (geodesic) between its endpoints. -/
theorem reducesTo_geodesic {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (h : Work.ORBassSerre.IsTree V) {a b : V} (p : Quiver.Path a b) :
    p.ReducesTo (h.geodesic a b) := by
  classical
  -- Reduce `p` to some reduced path `q`.
  obtain ⟨q, hpq, hqred⟩ :=
    Work.ORBassSerre.Tree.Reduction.qpath_exists_reducesTo_isReduced p
  -- In a tree, the reduced path `q` is the geodesic.
  rw [h.eq_geodesic hqred] at hpq
  exact hpq

end Work.ORBassSerre.Path.Reduction
