import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Submission.Work.GroupCohomology.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.GroupCohomology

/-- `H²π` is the quotient map `Z²(G, A) → H²(G, A)`, so its kernel is the subgroup of
`2`-cocycles that are `2`-coboundaries; hence `H²π c = 0` exactly when `c` is a coboundary. -/
theorem H2pi_eq_zero_iff {G : Type*} {A : Type*} [Group G] [AddCommGroup A]
    [DistribMulAction G A] (c : Work.GroupCohomology.Z2 G A) :
    Work.GroupCohomology.H2π G A c = 0 ↔ (c : (G × G) → A) ∈ Work.GroupCohomology.B2 G A := by
  rw [← AddMonoidHom.mem_ker, H2π, QuotientAddGroup.ker_mk', AddSubgroup.mem_comap,
    AddSubgroup.coe_subtype]

end Work.GroupCohomology
