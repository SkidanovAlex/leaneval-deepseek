import Mathlib
import Submission.Work.PSU3.StageA.BranchTwo.sq_mem_Q0sub
import Submission.Work.PSU3.StageA.caseWbot_setup
import Submission.Work.PSU3.StageA.caseC_data
import Submission.Work.ThmF.ChV12.L5Base
import Submission.Work.PSU3.StageA.sq_fiber_card_of_card_cube
import Submission.Work.PSU3.StageA.BranchTwo.ncard_sqFibre_subgroup_eq

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.PSU3.StageA.BranchTwo.ncard_sqFibre_eq`

The fibre of the squaring map `x ↦ x²` over an involution `s ≠ 1` of a **non-abelian** `Q` of
order `q³` (`q = |Q0sub H|`) has `q * (q + 1)` elements.

## Route

By Peterfalvi II Ch. V §1 Cor. of Prop. 2 (with `FeitThompsonProp`), `Q` is a Suzuki `2`-group
(`caseWbot_isSuzukiTwoGroup`) whose centre is `Q₀ = Q0sub H` (`caseWbot_center_subgroupOf`).
Higman's Theorem 1 (`Work.Higman.higmanProp`) then gives the count of the squaring fibre over a
non-identity central element of a Suzuki `2`-group of order `q³`
(`Work.PSU3.StageA.sq_fiber_card_of_card_cube`), and the elementary bijection
`↥Q ≃ {x : G // x ∈ Q ∧ x² = s}` transports it back to the ambient group
(`Work.PSU3.StageA.BranchTwo.ncard_sqFibre_subgroup_eq`).
-/

namespace Work.PSU3.StageA.BranchTwo

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

theorem ncard_sqFibre_eq {G : Type} [Group G] [Finite G]
    {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hFT : Submission.Blueprint.FeitThompsonProp)
    (hnab : ¬ Submission.Blueprint.IsAbelianSubgroup Q)
    (hcard : Nat.card Q = Nat.card ↥(Work.ThmF.Q0sub H) ^ 3)
    {s : G} (hs : s ∈ Q) (hs2 : orderOf s = 2) (hs1 : s ≠ 1) :
    {x : G | x ∈ Q ∧ x ^ 2 = s}.ncard =
      Nat.card ↥(Work.ThmF.Q0sub H) * (Nat.card ↥(Work.ThmF.Q0sub H) + 1) := by
  -- `Q` is a Suzuki `2`-group and its centre is `Q₀ = Q0sub H`
  have hSuz : Submission.Blueprint.IsSuzukiTwoGroup ↥Q :=
    Work.PSU3.StageA.caseWbot_isSuzukiTwoGroup hS hFT hC4 hnab
  obtain ⟨hSuz2⟩ := Work.Higman.isSuzukiTwoGroup_iff_nonempty_isSuzuki2Grp.mp hSuz
  have hZeq : Subgroup.center ↥Q = (Work.ThmF.Q0sub H).subgroupOf Q :=
    Work.PSU3.StageA.caseWbot_center_subgroupOf hS hFT hC4 hnab
  have hZcard : Nat.card ↥(Subgroup.center ↥Q) = Nat.card ↥(Work.ThmF.Q0sub H) := by
    rw [hZeq]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (Work.PSU3.StageA.Q0sub_le_Q hS.split)).toEquiv
  have hcardQ : Nat.card ↥Q = Nat.card ↥(Subgroup.center ↥Q) ^ 3 := by
    rw [hZcard, ← hcard]
  -- `s` is a non-identity central element of `Q`
  have hzs : (⟨s, hs⟩ : ↥Q) ∈ Subgroup.center ↥Q := by
    rw [hZeq, Subgroup.mem_subgroupOf]
    exact Work.ThmF.Q0_le_Q0sub H (Work.ThmF.involutions_subset_Q0 H ⟨hS.split.le hs, hs2⟩)
  have hzs1 : (⟨s, hs⟩ : ↥Q) ≠ 1 := fun h => hs1 (Subtype.ext_iff.mp h)
  rw [ncard_sqFibre_subgroup_eq hs,
    Work.PSU3.StageA.sq_fiber_card_of_card_cube Work.Higman.higmanProp hSuz2 hcardQ hzs hzs1,
    hZcard]

end Work.PSU3.StageA.BranchTwo
