import Mathlib
import Submission.Work.Models.Port.BenderSetup
import Submission.Work.Models.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Models.Abstract

/-- The number of involutions of `B = U ⋊ T` inside the subgroup `B` is the number of elements
of `B` of order `2`: `Set.ncard` of a set is the `Nat.card` of the corresponding subtype, and
`orderOf` in `↥B` agrees with `orderOf` in `G` (`Subgroup.orderOf_coe`). -/
theorem ncard_involutions_eq_subtype {G : Type*} [Group G] [Finite G]
    (P : Submission.BenderPair G) :
    (Submission.Blueprint.involutions (P.B : Set G)).ncard
      = Nat.card {t : ↥P.B // orderOf t = 2} := by
  rw [← Set.ncard_coe (Submission.Blueprint.involutions (P.B : Set G)), Set.ncard_univ]
  refine Nat.card_congr ?_
  refine
    { toFun := fun x => ⟨⟨x.1, x.2.1⟩, ?_⟩
      invFun := fun t => ⟨t.1.1, ⟨t.1.2, ?_⟩⟩
      left_inv := ?_
      right_inv := ?_ }
  · rw [← Subgroup.orderOf_coe]; exact x.2.2
  · rw [Subgroup.orderOf_coe]; exact t.2
  · intro x; rfl
  · intro t; rfl

/-- **The involution count of a Bender group.** `#Inv(B) · [G : B] = #Inv(G)`: by the strongly
embedded involution count `card_involutions`, `#Inv(G) = [G : B] · #Inv(B)` where the involutions
of `B` are counted inside the subgroup, and `#Inv(B) = Nat.card {t : ↥B // orderOf t = 2}` by
`ncard_involutions_eq_subtype`. -/
theorem ncard_involutions_B {G : Type*} [Group G] [Finite G] (P : Submission.BenderPair G) :
    (Submission.Blueprint.involutions (P.B : Set G)).ncard * P.B.index
      = Nat.card {t : G // orderOf t = 2} := by
  rw [ncard_involutions_eq_subtype P, Nat.mul_comm]
  exact P.card_involutions.symm

end Work.Models.Abstract
