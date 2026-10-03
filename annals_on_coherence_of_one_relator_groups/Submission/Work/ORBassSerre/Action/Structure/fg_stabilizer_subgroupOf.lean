import Mathlib
import Submission.Work.ORBassSerre.Action.Basic

set_option linter.style.haveILetI false

namespace Work.ORBassSerre.Action.Structure

/-- For a subgroup `H ≤ G`, the stabiliser of `X` for the restricted action of `↥H` is the
`H`-part of the stabiliser of `X` in `G`. -/
theorem stabilizer_subgroupOf_eq {G : Type*} {V : Type*} [Group G] [Quiver V]
    [Quiver.HasInvolutiveReverse V] [MulAction G V] [Work.ORBassSerre.GraphAction G V]
    {H : Subgroup G} {X : Quiver.Total V} :
    MulAction.stabilizer ↥H X = (MulAction.stabilizer G X).subgroupOf H := by
  ext h
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff,
    Subgroup.smul_def]

theorem fg_stabilizer_subgroupOf {G : Type*} {V : Type*} [Group G] [Quiver V]
    [Quiver.HasInvolutiveReverse V] [MulAction G V] [Work.ORBassSerre.GraphAction G V]
    {H : Subgroup G} {X : Quiver.Total V} (hle : MulAction.stabilizer G X ≤ H)
    (h : Group.FG (MulAction.stabilizer G X)) :
    Group.FG (MulAction.stabilizer ↥H X) := by
  letI : Group.FG ↥(MulAction.stabilizer G X) := h
  rw [stabilizer_subgroupOf_eq]
  exact Group.fg_of_surjective
    (f := (Subgroup.subgroupOfEquivOfLe hle).symm.toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe hle).symm.surjective

end Work.ORBassSerre.Action.Structure
