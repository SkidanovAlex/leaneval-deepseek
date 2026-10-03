import Mathlib
import Submission.Work.ORBassSerre.Action.QuotientGroupOrbitV

namespace Work.ORBassSerre.QuotientTree

universe u

open Quiver

/-- The induced action of `G ⧸ N` on the quotient graph `V ⧸ N` preserves adjacency. -/
theorem nonempty_hom_smul {G V : Type u} [Group G] [Quiver V] [Quiver.HasInvolutiveReverse V]
    [MulAction G V] [GraphAction G V] (N : Subgroup G) [N.Normal]
    {A B : Work.ORBassSerre.orbitV N V} (h : Nonempty (A ⟶ B)) (q : G ⧸ N) :
    Nonempty (q • A ⟶ q • B) := by
  obtain ⟨f⟩ := h
  obtain ⟨e, _he, hl, hr⟩ := f.2
  induction q using QuotientGroup.induction_on with
  | H g =>
    refine ⟨⟨Quotient.mk'' (g • e), g • e, rfl, ?_, ?_⟩⟩
    · rw [show (g • e).left = g • e.left from GraphAction.smul_left g e, ← hl]
      exact (quotient_smul_mk N g e.left).symm
    · rw [show (g • e).right = g • e.right from GraphAction.smul_right g e, ← hr]
      exact (quotient_smul_mk N g e.right).symm

end Work.ORBassSerre.QuotientTree
