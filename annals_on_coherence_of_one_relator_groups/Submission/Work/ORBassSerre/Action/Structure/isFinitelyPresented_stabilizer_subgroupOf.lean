import Mathlib
import Submission.Work.ORBassSerre.Action.Basic

namespace Work.ORBassSerre.Action.Structure

variable {G : Type*} [Group G]

/-- If `S ≤ H` are subgroups of `G`, then `S.comap H.subtype` (a subgroup of `H`) is
isomorphic to `S`, via the coercion `H → G`. -/
def comapSubtypeMulEquiv {H S : Subgroup G} (hle : S ≤ H) :
    S.comap H.subtype ≃* S where
  toFun x := ⟨(x : G), x.2⟩
  invFun y := ⟨⟨(y : G), hle y.2⟩, y.2⟩
  left_inv x := by ext; rfl
  right_inv y := by ext; rfl
  map_mul' x y := by ext; rfl

/-- The stabilizer in a subgroup `H` of a point `v` -- when `H` contains the stabilizer of `v`
in `G` -- is isomorphic to the stabilizer of `v` in `G`; hence it is finitely presented as
soon as the latter is. -/
theorem isFinitelyPresented_stabilizer_subgroupOf {G : Type*} {V : Type*} [Group G]
    [Quiver V] [Quiver.HasInvolutiveReverse V] [MulAction G V]
    [Work.ORBassSerre.GraphAction G V] {H : Subgroup G} {v : V}
    (hle : MulAction.stabilizer G v ≤ H)
    (h : Group.IsFinitelyPresented (MulAction.stabilizer G v)) :
    Group.IsFinitelyPresented (MulAction.stabilizer ↥H v) := by
  -- `MulAction.stabilizer ↥H v` is by definition `(MulAction.stabilizer G v).comap H.subtype`
  exact Group.IsFinitelyPresented.equiv (comapSubtypeMulEquiv hle).symm

end Work.ORBassSerre.Action.Structure
