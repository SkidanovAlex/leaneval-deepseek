import Mathlib.Data.Fintype.Defs
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Submission.Work.Tate.Coinvariants
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Tate

/-- The natural map `Ĥ⁻¹(G, A) → A_G` is injective: it is the map induced on the quotient
`ker N / I_G·A` by the composite `ker N ↪ A → A_G`, whose kernel is exactly the image of
`I_G·A` in `ker N` (because `I_G·A ⊆ ker N`). -/
theorem Hm1ToCoinv_injective {G : Type*} {A : Type*} [Group G] [AddCommGroup A]
    [DistribMulAction G A] [Fintype G] :
    Function.Injective (Work.Tate.Hm1ToCoinv G A) := by
  rw [injective_iff_map_eq_zero]
  intro z
  refine Hm1_induction_on (C := fun w => Hm1ToCoinv G A w = 0 → w = 0) z (fun a hz => ?_)
  rw [Hm1ToCoinv_apply, coinvMk_eq_zero_iff] at hz
  exact (Hm1π_eq_zero_iff a).mpr hz

end Work.Tate
