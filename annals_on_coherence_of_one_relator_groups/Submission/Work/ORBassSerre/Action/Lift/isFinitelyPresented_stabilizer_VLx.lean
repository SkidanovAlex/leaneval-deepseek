import Mathlib
import Submission.Work.ORBassSerre.Action.Lift.Basic

namespace Work.ORBassSerre.Action.Lift

/-- **Vertex stabilisers of the lifted graph are finitely presented.**

For `g : LGroup G V` and `a : VLx G V` we have `g • a = VLx.up (g.down • a.down)`, hence `g`
stabilises `a` exactly when `g.down` stabilises `a.down`.  In other words the stabiliser of `a`
in the lifted group is the preimage of the stabiliser of `a.down` under the isomorphism
`LGroupEquiv G V : LGroup G V ≃* G`, so the two stabilisers are isomorphic, and finite
presentability transfers along the isomorphism. -/
theorem isFinitelyPresented_stabilizer_VLx {G : Type*} {V : Type*} [Group G] [Quiver V]
    [Quiver.HasInvolutiveReverse V] [MulAction G V] [Work.ORBassSerre.GraphAction G V]
    (hstab : ∀ v : V, Group.IsFinitelyPresented (MulAction.stabilizer G v)) :
    ∀ a : Work.ORBassSerre.Action.Lift.VLx G V,
      Group.IsFinitelyPresented (MulAction.stabilizer (Work.ORBassSerre.Action.Lift.LGroup G V) a) := by
  intro a
  -- A lifted group element stabilises `a` iff its underlying element stabilises `a.down`.
  have hmem : ∀ g : LGroup G V,
      g ∈ MulAction.stabilizer (LGroup G V) a ↔ g.down ∈ MulAction.stabilizer G a.down := by
    intro g
    rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
    constructor
    · intro h
      simpa using congrArg ULift.down h
    · intro h
      show g • a = a
      rw [smul_VLx]
      exact congrArg ULift.up h
  -- So the stabiliser of `a` is the preimage of the stabiliser of `a.down`.
  have hsub : (MulAction.stabilizer G a.down).comap (LGroupEquiv G V).toMonoidHom =
      MulAction.stabilizer (LGroup G V) a := by
    ext g
    rw [Subgroup.mem_comap]
    exact (hmem g).symm
  -- Transporting along the isomorphism `LGroup G V ≃* G` identifies the two stabilisers.
  have heq : (MulAction.stabilizer G a.down).map (LGroupEquiv G V).symm.toMonoidHom =
      MulAction.stabilizer (LGroup G V) a :=
    (Subgroup.comap_equiv_eq_map_symm' (LGroupEquiv G V)
      (MulAction.stabilizer G a.down)).symm.trans hsub
  exact Group.IsFinitelyPresented.equiv
    ((MulEquiv.subgroupMap (LGroupEquiv G V).symm (MulAction.stabilizer G a.down)).trans
      (MulEquiv.subgroupCongr heq))
    (h := hstab a.down)

end Work.ORBassSerre.Action.Lift
