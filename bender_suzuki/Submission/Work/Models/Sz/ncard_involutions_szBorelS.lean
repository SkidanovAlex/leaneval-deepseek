import Mathlib
import Submission.Work.Models.Port.BenderPairModels
import Submission.Work.Models.Port.Sz.Involutions
import Submission.Work.Models.Abstract.ModelData

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Models.Sz

open LeanEval.GroupTheory.Defs

/-- The involutions of a subgroup `K ≤ G` (as a subset of `G`) correspond to the elements of
the group `K` of order `2`: `orderOf` agrees between `K` and `G` (`Subgroup.orderOf_coe`). -/
private lemma ncard_involutions_subgroup {G : Type*} [Group G] [Finite G] (K : Subgroup G) :
    (Submission.Blueprint.involutions (K : Set G)).ncard =
      Nat.card {u : ↥K // orderOf u = 2} := by
  rw [← Nat.card_coe_set_eq]
  refine Nat.card_congr ?_
  refine
    { toFun := fun x => ⟨⟨x.1, x.2.1⟩, ?_⟩
      invFun := fun u => ⟨(u.1 : G), ⟨u.1.2, ?_⟩⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun u => Subtype.ext (Subtype.ext rfl) }
  · rw [← Subgroup.orderOf_coe]; exact x.2.2
  · rw [Subgroup.orderOf_coe]; exact u.2

/-- The Borel subgroup `B` of `Sz(2^(2n+1))` has `q - 1 = 2^(2n+1) - 1` involutions, where
`q = 2^(2n+1)` is the order of the Suzuki field.  The involutions of `B = U ⋊ T` are those of
the Suzuki `2`-group `U` (`B/U ≅ T` has odd order), of which there are `q - 1`. -/
theorem ncard_involutions_szBorelS (n : ℕ) :
    (Submission.Blueprint.involutions
      (Submission.Sz.szBorelS n : Set (LeanEval.GroupTheory.Defs.SzModel n))).ncard
      = 2 ^ (2 * n + 1) - 1 := by
  rw [ncard_involutions_subgroup (Submission.Sz.szBorelS n),
    Submission.Sz.card_orderOf_eq_two_szBorelS n, Submission.Sz.card_szField n]

end Work.Models.Sz
