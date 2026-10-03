import Mathlib
import Submission.Work.ORBassSerre.Tree.Seg.reducedSpan_eq_union_of_mem
import Submission.Work.ORBassSerre.Tree.IsTreeAPI

namespace Work.ORBassSerre.Tree.Seg

theorem geodesic_length_le_of_mem_reducedSpan {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (hT : Work.ORBassSerre.IsTree V) {a b c : V}
    (hc : c ∈ Work.ORBassSerre.reducedSpan a b) :
    (hT.geodesic a c).length ≤ (hT.geodesic a b).length := by
  -- `c` lies on the geodesic from `a` to `b`, so that geodesic splits at `c` as
  -- `geodesic a c` followed by `geodesic c b`.
  obtain ⟨p₁, p₂, hp_eq, hp₁geod, _⟩ :=
    geodesic_eq_comp_geodesic_of_mem (hT := hT) hc
  rw [hp₁geod] at hp_eq
  rw [hp_eq, Quiver.Path.length_comp]
  omega

end Work.ORBassSerre.Tree.Seg
