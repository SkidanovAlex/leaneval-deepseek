/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Edge stabilisers of the lifted graph

The companion file `Submission.Work.ORBassSerre.Action.Lift.Basic` lifts a graph `V` carrying an
action of a group `G` to a graph `VLx G V` carrying an action of the lifted group
`LGroup G V = ULift G`, so that the arrows of the lifted graph live in the same universe as the
lifted group.  The bijection on arrows is `totalEquiv G V : Total (VLx G V) ≃ Total V`, and
`totalEquiv` is equivariant:  for `u : LGroup G V` and `e : Total (VLx G V)`,

`u • e = (totalEquiv G V).symm (u.down • totalEquiv G V e)`  (`smulTotal_VLx_apply`).

Consequently an element `u` of the lifted group stabilises `e` exactly when `u.down` stabilises
the corresponding arrow of `V`:

`u ∈ stabilizer (LGroup G V) e ↔ u.down ∈ stabilizer G (totalEquiv G V e)`.

Since `LGroupEquiv G V : LGroup G V ≃* G` is an isomorphism (it is `MulEquiv.ulift`), this says
that the stabiliser of `e` in the lifted group is the image of the stabiliser of
`totalEquiv G V e` in `G` under `(LGroupEquiv G V).symm`.

The content of the present file is that **finite generation of edge stabilisers transfers to the
lifted graph**: if every edge stabiliser of `V` is finitely generated, then so is every edge
stabiliser of `VLx G V`.  This is needed to trade a `G`-tree on `V` for an `LGroup G V`-tree on
`VLx G V` (where the Bass--Serre presentation machinery, whose `orbitE` is pinned to a single
universe, applies) and then to pull the resulting conclusions back.

## Main result

* `Work.ORBassSerre.Action.Lift.fg_stabilizer_VLx`
-/
import Mathlib
import Submission.Work.ORBassSerre.Action.Lift.Basic

namespace Work.ORBassSerre.Action.Lift

/-- **Edge stabilisers of the lifted graph are finitely generated if those of `V` are.**

For `u : LGroup G V` and `e : Quiver.Total (VLx G V)` the lifted action is
`u • e = (totalEquiv G V).symm (u.down • totalEquiv G V e)`, so `u` lies in the stabiliser of `e`
if and only if `u.down` lies in the stabiliser of `totalEquiv G V e` in `G`.  Hence
`stabilizer (LGroup G V) e` is the image of `stabilizer G (totalEquiv G V e)` under the group
isomorphism `G ≃* LGroup G V` given by `(LGroupEquiv G V).symm`, and finite generation transfers
along it. -/
theorem fg_stabilizer_VLx {G : Type*} {V : Type*} [Group G] [Quiver V]
    [Quiver.HasInvolutiveReverse V] [MulAction G V] [Work.ORBassSerre.GraphAction G V]
    (hedge : ∀ e : Quiver.Total V, Group.FG (MulAction.stabilizer G e)) :
    ∀ e' : Quiver.Total (Work.ORBassSerre.Action.Lift.VLx G V),
      Group.FG (MulAction.stabilizer (Work.ORBassSerre.Action.Lift.LGroup G V) e') := by
  intro e'
  -- A lifted element stabilises `e'` iff its underlying element stabilises `totalEquiv G V e'`.
  have hmem : ∀ g : LGroup G V,
      g ∈ MulAction.stabilizer (LGroup G V) e' ↔
        g.down ∈ MulAction.stabilizer G (totalEquiv G V e') := by
    intro g
    rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
    constructor
    · intro h
      have h2 := congrArg (totalEquiv G V) h
      rwa [smulTotal_VLx_apply, Equiv.apply_symm_apply] at h2
    · intro h
      rw [smulTotal_VLx_apply, h, Equiv.symm_apply_apply]
  -- So the stabiliser of `e'` is the preimage of the stabiliser of `totalEquiv G V e'`.
  have hsub : (MulAction.stabilizer G (totalEquiv G V e')).comap
      (LGroupEquiv G V).toMonoidHom = MulAction.stabilizer (LGroup G V) e' := by
    ext g
    rw [Subgroup.mem_comap]
    exact (hmem g).symm
  -- Equivalently, it is the image under the inverse isomorphism.
  have heq : (MulAction.stabilizer G (totalEquiv G V e')).map
      (LGroupEquiv G V).symm.toMonoidHom = MulAction.stabilizer (LGroup G V) e' :=
    (Subgroup.comap_equiv_eq_map_symm' (LGroupEquiv G V)
      (MulAction.stabilizer G (totalEquiv G V e'))).symm.trans hsub
  -- The corresponding isomorphism of the two stabilisers.
  have hφ : MulAction.stabilizer G (totalEquiv G V e') ≃*
      MulAction.stabilizer (LGroup G V) e' :=
    (MulEquiv.subgroupMap (LGroupEquiv G V).symm
      (MulAction.stabilizer G (totalEquiv G V e'))).trans (MulEquiv.subgroupCongr heq)
  exact Group.fg_of_surjective (f := hφ.toMonoidHom) (hG := hedge _) hφ.surjective

end Work.ORBassSerre.Action.Lift
