import Mathlib
import Submission.Work.Higman.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageA.BranchTwo

/-- Fibres of squaring inside a subgroup: the set of elements of `Q` whose square is `s` has the
same cardinality as the fibre of the squaring map of the group `↥Q` over the element `⟨s, hs⟩`. -/
theorem ncard_sqFibre_subgroup_eq {G : Type} [Group G] {Q : Subgroup G} {s : G} (hs : s ∈ Q) :
    {x : G | x ∈ Q ∧ x ^ 2 = s}.ncard = Nat.card {y : ↥Q // y ^ 2 = ⟨s, hs⟩} := by
  rw [← Nat.card_coe_set_eq]
  refine Nat.card_congr ?_
  exact {
    toFun := fun x => ⟨⟨x.1, x.2.1⟩, by
      apply Subtype.ext
      simpa using x.2.2⟩
    invFun := fun y => ⟨y.1.1, y.1.2, by
      have h := congrArg (fun z : ↥Q => (z : G)) y.2
      simpa using h⟩
    left_inv := fun x => Subtype.ext rfl
    right_inv := fun y => Subtype.ext (Subtype.ext rfl)
  }

end Work.PSU3.StageA.BranchTwo
