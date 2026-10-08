import Mathlib
import Submission.Work.BG.isFrobeniusGroupOfIsFrobeniusWith
import Submission.Work.BG.mapSubgroupOfEqSubgroupOfSubgroupOf

/-!
# `Work.BG.c3FrobFrobeniusGroupOfWith`

Let `BF = F ⋊ B` be a Frobenius group with kernel `F` and complement `B` inside a group `G`
(`Work.GW2.IsFrobeniusWith BF F B`), and let `BF ≤ T` be any subgroup of `G` containing `BF`.
Then, viewed inside `T`, the same pair is a Frobenius group: the kernel
`(F.subgroupOf T).subgroupOf (BF.subgroupOf T)` is normal in `↥(BF.subgroupOf T)` with complement
`(B.subgroupOf T).subgroupOf (BF.subgroupOf T)`, in the sense of Isaacs Thm 6.4
(`OddOrder.Isaacs.Ch06.IsFrobeniusGroup`, the subgroup-pair form).

The proof has two ingredients:

* `Work.BG.isFrobeniusGroupOfIsFrobeniusWith`: `Work.GW2.IsFrobeniusWith BF F B` already gives the
  Frobenius group structure on the group `↥BF` itself, with kernel `F.subgroupOf BF` and complement
  `B.subgroupOf BF`;
* `OddOrder.Isaacs.Ch06.isFrobeniusGroup_map_equiv`: a Frobenius group transports across a group
  isomorphism `e`, with kernel `N.map e` and complement `A.map e`.  Applying it to the canonical
  isomorphism `Subgroup.subgroupOfEquivOfLe hT : ↥(BF.subgroupOf T) ≃* ↥BF` (or rather its
  inverse) and rewriting with the coherence lemma
  `Work.BG.mapSubgroupOfEqSubgroupOfSubgroupOf` (which identifies the image of `F.subgroupOf BF`
  with `(F.subgroupOf T).subgroupOf (BF.subgroupOf T)`, and similarly for `B`) yields the claim.
-/

namespace Work.BG

theorem c3FrobFrobeniusGroupOfWith {G : Type} [Group G] (BF F B T : Subgroup G) (hT : BF ≤ T)
    (h : Work.GW2.IsFrobeniusWith BF F B) :
    OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(BF.subgroupOf T)
      ((F.subgroupOf T).subgroupOf (BF.subgroupOf T))
      ((B.subgroupOf T).subgroupOf (BF.subgroupOf T)) := by
  -- the Frobenius group structure on `↥BF`
  have h1 := isFrobeniusGroupOfIsFrobeniusWith BF F B h
  obtain ⟨hFle, _, hsup, _, _, _, _⟩ := h
  -- `B ≤ BF`, since `B ⊔ F = BF`
  have hBle : B ≤ BF := hsup ▸ le_sup_left
  -- transport it along the canonical isomorphism `↥(BF.subgroupOf T) ≃* ↥BF`
  have h2 := OddOrder.Isaacs.Ch06.isFrobeniusGroup_map_equiv h1
    (Subgroup.subgroupOfEquivOfLe hT).symm
  -- identify the images of `F.subgroupOf BF` and `B.subgroupOf BF`
  rw [mapSubgroupOfEqSubgroupOfSubgroupOf hFle hT,
    mapSubgroupOfEqSubgroupOfSubgroupOf hBle hT] at h2
  exact h2

end Work.BG
