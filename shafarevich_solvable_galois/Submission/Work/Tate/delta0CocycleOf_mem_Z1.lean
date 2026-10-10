import Mathlib.Tactic.Abel
import Mathlib.Data.Fintype.Defs
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Submission.Work.Tate.Delta0
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Tate

/-- The cocycle `γ ↦ f⁻¹(γ • b - b)` attached to a lift `b` of a fixed point is indeed a
`1`-cocycle of `A`.  Since `S.f` is injective it suffices to check the cocycle identity after
applying `S.f`, where it reduces to `(g * h) • b - b = g • (h • b - b) + (g • b - b)`. -/
theorem delta0CocycleOf_mem_Z1 {G : Type*} {A B C : Type*} [Group G] [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [DistribMulAction G A] [DistribMulAction G B]
    [DistribMulAction G C] [Fintype G] (S : Work.Tate.SES G A B C) (b : B)
    (hb : ∀ γ : G, S.g (γ • b - b) = 0) :
    S.delta0CocycleOf b hb ∈ Work.GroupCohomology.Z1 G A := by
  rw [Work.GroupCohomology.mem_Z1_iff]
  intro g h
  apply S.f_injective
  rw [map_add, S.f_delta0CocycleOf b hb (g * h), S.f_equiv g, S.f_delta0CocycleOf b hb h,
    S.f_delta0CocycleOf b hb g, smul_sub, mul_smul]
  abel

end Work.Tate
