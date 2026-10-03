import Mathlib
import Submission.Work.ORBassSerre.Tree.IsTreeAPI

namespace Work.ORBassSerre.Tree.Seg

open Quiver

/-- **Edge dichotomy for geodesics in a tree.**  Let `f : a ⟶ b` be an arrow of a tree `T` and
let `z` be any vertex.  Then one of the two following holds: either the geodesic from `z` to `b`
is the geodesic from `z` to `a` followed by the edge `f`, or `a` is the last vertex of the walk
obtained by going from `z` to `b` and then back along some edge `g : b ⟶ a`.

Equivalently: the geodesic from `z` to one of the endpoints of `f` passes through the other
endpoint, and then uses the edge `f` (or its reverse) as its last step. -/
theorem geodesic_edge_dichotomy {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    {hT : Work.ORBassSerre.IsTree V} {a b z : V} (f : a ⟶ b) :
    hT.geodesic z b = (hT.geodesic z a).comp f.toPath ∨
      ∃ g : b ⟶ a, hT.geodesic z a = (hT.geodesic z b).comp g.toPath := by
  classical
  by_cases hred : ((hT.geodesic z a).comp f.toPath).IsReduced
  · -- The walk `z → a → b` is already reduced, hence is the geodesic `z → b`.
    left
    exact (hT.eq_geodesic hred).symm
  · -- Otherwise some backtrack can be deleted from `z → a → b`; since both factors are reduced,
    -- the backtrack straddles the junction `a`, so `geodesic z a` ends with an edge `b ⟶ a`.
    right
    obtain ⟨q, hq⟩ : ∃ q : Quiver.Path z b,
        Quiver.Path.DeleteBacktrack ((hT.geodesic z a).comp f.toPath) q := by
      simpa only [Quiver.Path.IsReduced, not_forall, not_not] using hred
    obtain ⟨x, f', u', v', hP, hf, -⟩ :=
      Work.ORBassSerre.Tree.Geodesic.deleteBacktrack_comp_junction (u := hT.geodesic z a)
        (v := f.toPath) (hT.geodesic_isReduced z a)
        (Quiver.Path.IsReduced.of_length_lt_two (by simp)) hq
    -- `v'` is a path of length `0`, so its source `x` is `b`.
    have hv0 : v'.length = 0 := by
      have h := congrArg Quiver.Path.length hf
      rw [Quiver.Path.length_toPath, Quiver.Path.length_comp, Quiver.Path.length_toPath] at h
      omega
    have hxb : x = b := Quiver.Path.eq_of_length_zero v' hv0
    subst hxb
    -- `u'` is a reduced initial segment of `geodesic z a`, hence is `geodesic z x`.
    have hu' : u' = hT.geodesic z x := by
      apply hT.eq_geodesic
      apply Quiver.Path.IsReduced.of_comp (q := f'.toPath)
      rw [Quiver.Path.comp_toPath_eq_cons, ← hP]
      exact hT.geodesic_isReduced z a
    exact ⟨f', by rw [← hu', Quiver.Path.comp_toPath_eq_cons]; exact hP⟩

end Work.ORBassSerre.Tree.Seg
