import Mathlib
import Submission.Work.NormalComplement.Sec5Fix.Prelim

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NormalComplement.Sec5Fix

theorem no_fourGroup_of_involutions_ncard_eq_one {G : Type} [Group G] {S : Subgroup G}
    (h : (Submission.Blueprint.involutions (S : Set G)).ncard = 1) :
    ¬ Submission.Blueprint.HasFourGroup ↥S := by
  -- If two distinct commuting involutions of `↥S` existed, their images in `G` would be two
  -- distinct elements of `S` of order two, contradicting `ncard = 1`.
  intro h4
  obtain ⟨a, b, ha2, hb2, hne, _⟩ := h4
  obtain ⟨c, hc⟩ := Set.ncard_eq_one.mp h
  have key : ∀ x : ↥S, orderOf x = 2 → (x : G) = c := by
    intro x hx
    have hmem : (x : G) ∈ Submission.Blueprint.involutions (S : Set G) := by
      refine ⟨x.2, ?_⟩
      rw [Subgroup.orderOf_coe]
      exact hx
    rw [hc] at hmem
    simpa using hmem
  exact hne (Subtype.ext ((key a ha2).trans (key b hb2).symm))

end Work.NormalComplement.Sec5Fix
