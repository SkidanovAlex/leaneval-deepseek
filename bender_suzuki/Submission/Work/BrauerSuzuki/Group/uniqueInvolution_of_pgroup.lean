import Mathlib
import Submission.Work.BrauerSuzuki.Defs
import Submission.Work.BrauerSuzuki.Group.central_involution_of_isPGroup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.BrauerSuzuki.Group.uniqueInvolution_of_pgroup`

In a finite group `G` with no four-group (`¬ HasFourGroup G`), a `2`-subgroup `S ≤ G` contains
at most one involution: any two elements of `S` of order `2` are equal.

The argument is the contrapositive.  A nontrivial finite `2`-group has a *central* involution
`z` (`Work.BrauerSuzuki.Group.central_involution_of_isPGroup`); an involution `w ∈ S` distinct
from `z` commutes with `z` (as `z` is central in `S`), so `z` and `w` generate a four-group in
`G`, contradicting `h4`.  Hence every involution of `S` equals `z`, and in particular
`u = z = v`.
-/

namespace Work.BrauerSuzuki.Group

theorem uniqueInvolution_of_pgroup {G : Type*} [Group G] [Finite G] {S : Subgroup G}
    (hS : IsPGroup 2 S) (h4 : ¬ Submission.Blueprint.HasFourGroup G) {u v : G}
    (hu : u ∈ S) (hv : v ∈ S) (hu2 : orderOf u = 2) (hv2 : orderOf v = 2) : u = v := by
  -- `S` contains the element `u` of order `2`, so it is nontrivial.
  have hnt : Nontrivial ↥S :=
    ⟨⟨u, hu⟩, 1, fun h => by
      have hu1 : u = 1 := congrArg Subtype.val h
      rw [hu1] at hu2
      simp at hu2⟩
  -- a central involution of `S`, whose existence is the delegated `2`-group fact
  obtain ⟨z, hzc, hz2⟩ := central_involution_of_isPGroup hS hnt
  -- every involution of `S` is `z`: another one would give a four-group together with `z`
  have key : ∀ w : ↥S, orderOf w = 2 → w = z := by
    intro w hw
    by_contra hwz
    have hcomm : (w : G) * (z : G) = (z : G) * (w : G) := by
      have h := (Subgroup.mem_center_iff.mp hzc) w
      simpa using congrArg (Subtype.val) h
    exact h4
      ⟨(w : G), (z : G), by rw [Subgroup.orderOf_coe, hw], by rw [Subgroup.orderOf_coe, hz2],
        (fun h => hwz (Subtype.ext h)), hcomm⟩
  have h1 : (⟨u, hu⟩ : ↥S) = z := key ⟨u, hu⟩ (by rw [Subgroup.orderOf_mk, hu2])
  have h2 : (⟨v, hv⟩ : ↥S) = z := key ⟨v, hv⟩ (by rw [Subgroup.orderOf_mk, hv2])
  exact congrArg Subtype.val (h1.trans h2.symm)

end Work.BrauerSuzuki.Group
