import Mathlib
import Submission.Work.BG.invJCard
import Submission.Work.BG.conjClassCard

namespace Work.BG

set_option maxHeartbeats 2000000 in
theorem card_conjClassF_subtype {G : Type} [Group G] (H : Subgroup G) [Fintype ↥H]
    (x : G) (hx : x ∈ H) :
    (Work.BG.conjClassF (↥H) ⟨x, hx⟩).card =
      (Subgroup.centralizer ({x} : Set G)).relIndex H := by
  classical
  -- The Finset `conjClassF` is exactly the conjugacy class as a subtype.
  have hcardCls : (conjClassF (↥H) ⟨x, hx⟩).card =
      Nat.card {y : ↥H // IsConj y ⟨x, hx⟩} := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_coe (conjClassF (↥H) ⟨x, hx⟩)]
    refine Fintype.card_congr ?_
    refine
      { toFun := fun y => ⟨y.1, (mem_conjClassF ⟨x, hx⟩ y.1).mp y.2⟩
        invFun := fun y => ⟨y.1, (mem_conjClassF ⟨x, hx⟩ y.1).mpr y.2⟩
        left_inv := ?_
        right_inv := ?_ }
    · intro y; ext; rfl
    · intro y; ext; rfl
  -- The centralizer inside `↥H` is the trace of the centralizer in `G`.
  have hcent : Subgroup.centralizer ({⟨x, hx⟩} : Set ↥H) =
      (Subgroup.centralizer ({x} : Set G)).subgroupOf H := by
    ext y
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h; simpa using congrArg (fun z : ↥H => (z : G)) h
    · intro h; exact Subtype.ext (by simpa using h)
  rw [hcardCls, conjClassCard, Subgroup.relIndex, hcent]

end Work.BG
