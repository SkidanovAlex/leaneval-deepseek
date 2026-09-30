/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The adjunction space is compact Hausdorff

Consequences of `glueData_isClosed_relGraph` for the gluing `~₃` of the
Ratcliffe--Tschantz construction: the adjunction space along a homeomorphism of two closed
subsets of compact Hausdorff spaces is compact Hausdorff.
-/
import Mathlib
import Submission.Work.QuotientT2.Basic
import Submission.Work.QuotientT2.Adjunction
import Submission.Work.QuotientT2.glueData_isClosed_relGraph

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Set Topology Function

namespace Work.QuotientT2

namespace GlueData

variable {X : Type*} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The graph of the adjunction relation is closed (restatement of
`Work.QuotientT2.glueData_isClosed_relGraph`). -/
theorem isClosed_relGraph [T2Space X] [T2Space Y] (G : GlueData X Y) :
    IsClosed (relGraph G.setoid) :=
  glueData_isClosed_relGraph G

/-- **The adjunction space along a homeomorphism of closed subsets of compact Hausdorff spaces
is Hausdorff.** -/
theorem t2Space_quotient [CompactSpace X] [CompactSpace Y] [T2Space X] [T2Space Y]
    (G : GlueData X Y) : T2Space (Quotient G.setoid) :=
  t2_quotient_of_closed (r := G.setoid) G.isClosed_relGraph

/-- The adjunction space along a homeomorphism of closed subsets of compact spaces is
compact. -/
theorem compactSpace_quotient [CompactSpace X] [CompactSpace Y] (G : GlueData X Y) :
    CompactSpace (Quotient G.setoid) :=
  Quotient.compactSpace

/-- The t1 instance (points are closed) follows from `t2Space_quotient`. -/
theorem t1Space_quotient [CompactSpace X] [CompactSpace Y] [T2Space X] [T2Space Y]
    (G : GlueData X Y) : T1Space (Quotient G.setoid) := by
  have := G.t2Space_quotient
  infer_instance

/-- The identified points have the same class in the adjunction space. -/
theorem mk_inl_eq_mk_inr (G : GlueData X Y) (x : G.s) :
    Quotient.mk G.setoid (Sum.inl (x : X)) =
      Quotient.mk G.setoid (Sum.inr ((G.h x : G.t) : Y)) :=
  Quotient.sound (G.rel_inl_inr x)

/-- Points of the two pieces that are not identified have different classes. -/
theorem mk_inl_ne_mk_inr (G : GlueData X Y) {x : X} {y : Y}
    (h : ¬ ∃ hx : x ∈ G.s, ((G.h ⟨x, hx⟩ : G.t) : Y) = y) :
    Quotient.mk G.setoid (Sum.inl x) ≠ Quotient.mk G.setoid (Sum.inr y) := by
  intro hxy
  refine h ?_
  rcases (Quotient.eq.mp hxy : G.Rel (Sum.inl x) (Sum.inr y)) with ⟨z, h1, h2⟩ | ⟨z, h1, h2⟩ | h'
  · have hz : x = (z : X) := Sum.inl.inj h1
    subst hz
    exact ⟨z.2, (Sum.inr.inj h2).symm⟩
  · exact absurd h1 (by simp)
  · exact absurd h' (by simp)

end GlueData

end Work.QuotientT2
