import Mathlib
import Submission.Work.OROneRel.hnnConjSplit
import Submission.Work.ORBassSerre.Action.Structure.isFinitelyPresented_of_hnn_case
import Submission.Work.OROneRel.stabilizer_edge_eq_hnnEdgeA
import Submission.Work.OROneRel.hnnConjEquiv_eq_hnnPhi
import Submission.Work.OROneRel.exists_hnnExtension_iso_of_data

/-!
# Injectivity of the canonical HNN comparison map from an action on a tree

For a group `G` acting on a tree `V` (with an involutive reversal, no inversions), a vertex `v`, an
edge `e : v ⟶ z` and an element `t` with `t • z = v`, the canonical comparison map
`hnnConjMap (Stab v) t : HNN(↥Stab v, Stab v ⊓ t⁻¹(Stab v)t, t(…)t⁻¹, conj_t) →* G` is injective.

This is the classical Bass--Serre statement that a vertex stabiliser together with a "stable
letter" closing up an edge orbit is an HNN extension; it is exactly the injectivity input isolated
by `Work.OROneRel.hnnConjSplit` (see also the discussion in
`Submission/Work/OROneRel/magnus_residual_winSplitting.lean`, item 3 of the reduction chain).

## The proof

The workspace already contains the injectivity of the *Bass--Serre* comparison map
`Work.ORBassSerre.Action.Structure.hnnMap v t e'` for the fundamental edge `e' : v ⟶ t • v`
(`Work.ORBassSerre.Action.Structure.hnnMap_injective`, whose proof is the tree normal form of
`hnn_reduced_word_ne_one`) — note that it requires *no* orbit hypotheses.  It remains to observe
that `hnnConjMap (Stab v) t` is the composite of `hnnMap v t e'` with the isomorphism between the
two HNN extensions, which have the same data after all:

* for the fundamental edge `e' := t • e.reverse` one has `hnnEdge v t e' = t • e.reverse` and
  `hnnBack v t e' = e`, so the Bass--Serre associated subgroups `hnnA = Stab(e') = t Stab(e) t⁻¹`
  and `hnnB = Stab(e)` of `isFinitelyPresented_of_hnn_case` are the edge stabiliser of `e` and its
  `t`-conjugate;
* by `stabilizer_edge_eq_hnnEdgeA` (for a tree) the edge stabiliser of `e` is
  `hnnEdgeA (Stab v) t = Stab v ⊓ t⁻¹(Stab v)t`, and its `t`-conjugate is `hnnEdgeB (Stab v) t`;
* the two conjugation isomorphisms agree (`hnnConjEquiv_eq_hnnPhi`), and the residual difference of
  the subgroup *terms* is handled by `exists_hnnExtension_iso_of_data`.
-/

namespace Work.OROneRel

open Quiver

universe u

theorem hnnConjMap_injective_of_tree {G : Type u} [Group G] {V : Type u} [Quiver V]
    [Quiver.HasInvolutiveReverse V] [MulAction G V] [Work.ORBassSerre.GraphAction G V]
    (hT : Work.ORBassSerre.IsTree V)
    (hninv : Work.ORBassSerre.ActsWithoutInversions G V)
    (v : V) (t : G) {z : V} (e : v ⟶ z) (ht : t • z = v) :
    Function.Injective (Work.OROneRel.hnnConjMap (MulAction.stabilizer G v) t) := by
  classical
  -- ## The fundamental edge `e' : v ⟶ t • v` of the Bass--Serre description, namely `t • e.reverse`
  have hFleft : (t • (Quiver.Total.mk v z e).reverse).left = v := by
    rw [Quiver.Total.reverse_mk, Work.ORBassSerre.GraphAction.smul_left_mk, ht]
  have hFright : (t • (Quiver.Total.mk v z e).reverse).right = t • v := by
    rw [Quiver.Total.reverse_mk, Work.ORBassSerre.GraphAction.smul_right_mk]
  let e' : v ⟶ t • v :=
    Quiver.homOfEq (t • (Quiver.Total.mk v z e).reverse).hom hFleft hFright
  have hmk : Quiver.Total.mk v (t • v) e' = t • (Quiver.Total.mk v z e).reverse := by
    refine Quiver.Total.ext hFleft.symm hFright.symm ?_
    exact (Quiver.heq_of_homOfEq_ext hFleft hFright (f := _) (f' := e') rfl).symm
  have hnnEdge_eq : Work.ORBassSerre.Action.Structure.hnnEdge v t e'
      = t • (Quiver.Total.mk v z e).reverse := hmk
  -- the reversed fundamental edge is the original edge, whence the edge stabilisers match
  have hnnBack_eq : Work.ORBassSerre.Action.Structure.hnnBack v t e'
      = Quiver.Total.mk v z e := by
    unfold Work.ORBassSerre.Action.Structure.hnnBack
    rw [hnnEdge_eq, inv_smul_smul, Quiver.Total.reverse_reverse]
  have hStabBack : MulAction.stabilizer G (Work.ORBassSerre.Action.Structure.hnnBack v t e')
      = MulAction.stabilizer G (Quiver.Total.mk v z e) := by rw [hnnBack_eq]
  have hStabEdge : MulAction.stabilizer G (Work.ORBassSerre.Action.Structure.hnnEdge v t e')
      = (MulAction.stabilizer G (Quiver.Total.mk v z e)).map (MulAut.conj t) := by
    rw [hnnEdge_eq, MulAction.stabilizer_smul_eq_stabilizer_map_conj,
      Work.ORBassSerre.Action.Structure.stabilizer_reverse]
    rfl
  -- ## The two HNN descriptions have the same data
  -- the edge stabiliser of `e` is the group-theoretic `hnnEdgeA`
  have hEdgeA : Work.OROneRel.hnnEdgeA (MulAction.stabilizer G v) t
      = MulAction.stabilizer G (Quiver.Total.mk v z e) :=
    Work.OROneRel.stabilizer_edge_eq_hnnEdgeA hT v t e ht
  have hA : (Work.OROneRel.hnnEdgeA (MulAction.stabilizer G v) t).subgroupOf
        (MulAction.stabilizer G v)
      = Work.ORBassSerre.Action.Structure.hnnA v t e' := by
    rw [hEdgeA]
    unfold Work.ORBassSerre.Action.Structure.hnnA
    rw [hStabBack]
    rfl
  -- and the `t`-conjugate is `hnnEdgeB`
  have hEdgeB : Work.OROneRel.hnnEdgeB (MulAction.stabilizer G v) t
      = (MulAction.stabilizer G (Quiver.Total.mk v z e)).map (MulAut.conj t) := by
    rw [Work.OROneRel.hnnEdgeB, hEdgeA]
  have hB : (Work.OROneRel.hnnEdgeB (MulAction.stabilizer G v) t).subgroupOf
        (MulAction.stabilizer G v)
      = Work.ORBassSerre.Action.Structure.hnnB v t e' := by
    rw [hEdgeB]
    unfold Work.ORBassSerre.Action.Structure.hnnB
    rw [hStabEdge]
    rfl
  -- the two conjugation isomorphisms agree on the common elements
  have hφ : ∀ (x : ↥(MulAction.stabilizer G v))
      (hx : x ∈ (Work.OROneRel.hnnEdgeA (MulAction.stabilizer G v) t).subgroupOf
        (MulAction.stabilizer G v))
      (hx' : x ∈ Work.ORBassSerre.Action.Structure.hnnA v t e'),
      ((Work.OROneRel.hnnConjEquiv (MulAction.stabilizer G v) t ⟨x, hx⟩ :
          (Work.OROneRel.hnnEdgeB (MulAction.stabilizer G v) t).subgroupOf
            (MulAction.stabilizer G v)) : ↥(MulAction.stabilizer G v))
        = ((Work.ORBassSerre.Action.Structure.hnnPhi v t e' ⟨x, hx'⟩ :
          Work.ORBassSerre.Action.Structure.hnnB v t e') : ↥(MulAction.stabilizer G v)) :=
    fun x hx hx' => Work.OROneRel.hnnConjEquiv_eq_hnnPhi v t e' x hx hx'
  obtain ⟨E, hE_of, hE_t⟩ := Work.OROneRel.exists_hnnExtension_iso_of_data
    (H := MulAction.stabilizer G v) hA hB
    (Work.OROneRel.hnnConjEquiv (MulAction.stabilizer G v) t)
    (Work.ORBassSerre.Action.Structure.hnnPhi v t e') hφ
  -- ## `hnnConjMap` is `hnnMap` composed with that isomorphism
  have hcomp : Work.OROneRel.hnnConjMap (MulAction.stabilizer G v) t
      = (Work.ORBassSerre.Action.Structure.hnnMap v t e').comp E.toMonoidHom := by
    apply HNNExtension.hom_ext
    · ext h
      simp only [MonoidHom.comp_apply]
      rw [Work.OROneRel.hnnConjMap_of]
      rw [show E.toMonoidHom (HNNExtension.of h) = HNNExtension.of h from hE_of h]
      rw [Work.ORBassSerre.Action.Structure.hnnMap_of]
    · simp only [MonoidHom.comp_apply]
      rw [Work.OROneRel.hnnConjMap_t]
      rw [show E.toMonoidHom HNNExtension.t = HNNExtension.t from hE_t]
      rw [Work.ORBassSerre.Action.Structure.hnnMap_t]
  intro x y hxy
  have h1 : Work.ORBassSerre.Action.Structure.hnnMap v t e' (E.toMonoidHom x)
      = Work.ORBassSerre.Action.Structure.hnnMap v t e' (E.toMonoidHom y) := by
    have hx := DFunLike.congr_fun hcomp x
    have hy := DFunLike.congr_fun hcomp y
    rw [hx, hy] at hxy
    exact hxy
  exact E.injective (Work.ORBassSerre.Action.Structure.hnnMap_injective
    (v := v) (t := t) (e := e') hT hninv h1)

end Work.OROneRel
