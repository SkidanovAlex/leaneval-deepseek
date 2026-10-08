import Mathlib
import Submission.Work.ZJB.Step1.Defs
import Submission.Work.ZJB.ZJBasic
import Submission.Work.ZJB.ZJApi.ZJ_ne_bot
import Submission.Work.ZJB2.zsNeBotOfIsPGroup
import Submission.Work.ZJB2.Step1.zsLeZJProp
import Submission.Work.ZJB2.sylowInConj

namespace Work.ZJB2.Step1

open Work.ZJB
open Subgroup

/-- **Extension.**  A `p`-subgroup `V` of a subgroup `M` lies in a Sylow `p`-subgroup `T` of `M`
(in the sense of `IsSylowIn p T M`).  Pass to the group `↥M`, use `IsPGroup.exists_le_sylow`, and
push the resulting Sylow subgroup back into the ambient group. -/
theorem exists_isSylowIn_le {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {M V : Subgroup G} (hVM : V ≤ M) (hVp : IsPGroup p V) :
    ∃ T : Subgroup G, Work.ZJB.IsSylowIn p T M ∧ V ≤ T := by
  have hV'p : IsPGroup p ↥(V.subgroupOf M) :=
    hVp.of_equiv (Subgroup.subgroupOfEquivOfLe hVM).symm
  obtain ⟨P, hVP⟩ := hV'p.exists_le_sylow
  refine ⟨(P : Subgroup ↥M).map M.subtype, ⟨Subgroup.map_subtype_le _, ?_, ?_⟩, ?_⟩
  · exact P.isPGroup'.map M.subtype
  · intro Q hTQ hQM hQp
    have hQ'p : IsPGroup p ↥(Q.subgroupOf M) :=
      hQp.comap_of_injective M.subtype M.subtype_injective
    have hPle : (P : Subgroup ↥M) ≤ Q.subgroupOf M := by
      intro x hx
      rw [Subgroup.mem_subgroupOf]
      exact hTQ (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
    have hPQ : Q.subgroupOf M = (P : Subgroup ↥M) := P.is_maximal' hQ'p hPle
    rw [← Subgroup.map_subgroupOf_eq_of_le hQM, hPQ]
  · intro v hv
    exact Subgroup.mem_map.mpr ⟨⟨v, hVM hv⟩, hVP (Subgroup.mem_subgroupOf.mpr hv), rfl⟩

/-- **A normal `p`-subgroup of a group lies in every Sylow `p`-subgroup.**  Here `H` is a
`p`-subgroup which is normal in `N_G(H)` (its own normalizer), and `T ∈ Syl_p(N_G(H))`; hence
`H ≤ T`.  (Used only to have `Z(S₃) ≤ C(H) ≤ N_G(H)` for a Sylow `S₃ ⊇ T`.) -/
theorem le_of_isSylowIn_normalizer_of_normal_isPGroup {G : Type*} [Group G] {p : ℕ}
    [Fact p.Prime] {H T : Subgroup G} (hH : IsPGroup p H) (hT : Work.ZJB.IsSylowIn p T
      (Subgroup.normalizer (H : Set G))) : H ≤ T := by
  haveI : (H.subgroupOf (Subgroup.normalizer (H : Set G))).Normal :=
    Subgroup.normal_in_normalizer
  have hH'p : IsPGroup p (H.subgroupOf (Subgroup.normalizer (H : Set G))) :=
    hH.of_equiv (Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer (H := H))).symm
  have hle : H.subgroupOf (Subgroup.normalizer (H : Set G)) ≤
      ((Work.ZJB2.subgroupOfIsSylow hT : Sylow p ↥(Subgroup.normalizer (H : Set G))) :
        Subgroup ↥(Subgroup.normalizer (H : Set G))) :=
    hH'p.le_sylow_of_normal (Work.ZJB2.subgroupOfIsSylow hT)
  intro h hh
  have hmem : (⟨h, Subgroup.le_normalizer hh⟩ :
      ↥(Subgroup.normalizer (H : Set G))) ∈
      T.subgroupOf (Subgroup.normalizer (H : Set G)) := by
    simpa only [Work.ZJB2.subgroupOfIsSylow_coe] using
      hle (Subgroup.mem_subgroupOf.mpr hh)
  exact Subgroup.mem_subgroupOf.mp hmem

theorem zjtMemProp {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] :
    Work.ZJB.ZJTMemProp p G := by
  intro S D H T a n hH hT hZT hZaT hcard hnN hZn
  obtain ⟨hHne, _hpart1, S₂, hZS₂H, hHS₂⟩ := hH
  have hHp : IsPGroup p H := S₂.isPGroup'.to_le hHS₂
  -- `H` (normal in `N(H)`) lies in the Sylow `T` of `N(H)`
  have hHleT : H ≤ T := le_of_isSylowIn_normalizer_of_normal_isPGroup hHp hT
  -- `T` is nontrivial: `N(H)` contains the nontrivial `p`-subgroup `Z(S₂)`
  have hTne : T ≠ ⊥ := by
    intro hTbot
    have hS₂ne : (S₂ : Subgroup G) ≠ ⊥ := by
      intro hb
      exact hHne (le_bot_iff.mp (hHS₂.trans (le_of_eq hb)))
    have hZS₂ne : Work.ZJB.ZS (S₂ : Subgroup G) ≠ ⊥ :=
      Work.ZJB.ZJApi.centralizer_inf_ne_bot_of_isPGroup S₂.isPGroup' hS₂ne
    have hZS₂N : Work.ZJB.ZS (S₂ : Subgroup G) ≤ Subgroup.normalizer (H : Set G) :=
      hZS₂H.trans Subgroup.le_normalizer
    have hp : IsPGroup p (Work.ZJB.ZS (S₂ : Subgroup G)) :=
      S₂.isPGroup'.to_le inf_le_right
    have hmax := hT.2.2 (Work.ZJB.ZS (S₂ : Subgroup G)) (hTbot.le.trans bot_le) hZS₂N hp
    exact hZS₂ne (hmax.trans hTbot)
  -- `Z(J(T)) ≠ 1`
  have hZTne : Work.GW2.ZJ T ≠ ⊥ := Work.ZJB.ZJApi.ZJ_ne_bot hT.2.1 hTne
  -- a Sylow `p`-subgroup `S₃` of `G` containing `T`
  obtain ⟨S₃, hTS₃⟩ := hT.2.1.exists_le_sylow
  have hInter : (S₃ : Subgroup G) ⊓ Subgroup.normalizer (H : Set G) = T :=
    hT.2.2 _ (le_inf hTS₃ hT.1) inf_le_right (S₃.isPGroup'.to_le inf_le_left)
  -- `Z(S₃) ≤ T` :  `Z(S₃) ≤ C(S₃) ≤ C(H) ≤ N(H)` and `Z(S₃) ≤ S₃`
  have hZS₃leT : Work.ZJB.ZS (S₃ : Subgroup G) ≤ T := by
    rw [← hInter]
    refine le_inf inf_le_right ?_
    exact (inf_le_left :
        Work.ZJB.ZS (S₃ : Subgroup G) ≤
          Subgroup.centralizer ((S₃ : Subgroup G) : Set G)).trans
      ((Subgroup.centralizer_le
          (SetLike.coe_subset_coe.mpr (hHleT.trans hTS₃))).trans
        (Subgroup.centralizer_le_normalizer (H : Set G)))
  -- `Z(S₃) ≤ Z(T) ≤ Z(J(T))`
  have hZS₃leZJT : Work.ZJB.ZS (S₃ : Subgroup G) ≤ Work.GW2.ZJ T := by
    have hle : Work.ZJB.ZS (S₃ : Subgroup G) ≤ Work.ZJB.ZS T := by
      rw [Work.ZJB.ZS, Work.ZJB.ZS]
      exact le_inf
        ((inf_le_left : Work.ZJB.ZS (S₃ : Subgroup G) ≤
            Subgroup.centralizer ((S₃ : Subgroup G) : Set G)).trans
          (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hTS₃)))
        hZS₃leT
    exact hle.trans (Work.ZJB2.Step1.zsLeZJProp (G := G) T)
  refine ⟨hZTne, ?_, ?_⟩
  · -- a Sylow `p`-subgroup `T'` of `N(Z(J(T)))` containing `T`
    obtain ⟨T', hT'syl, hTT'⟩ := exists_isSylowIn_le (Work.ZJB.le_normalizer_ZJ T) hT.2.1
    refine ⟨T', n, hnN, hT'syl, hZT.trans hTT', hZn, hZaT.trans hTT', ?_⟩
    -- `|D| < |N(J(S)) ∩ T| ≤ |N(J(S)) ∩ T'|`
    refine hcard.trans_le (Nat.card_le_card_of_injective
      (fun x : ↥(Subgroup.normalizer (Work.GW2.thompsonJ (S : Subgroup G) : Set G) ⊓ T) =>
        (⟨(x : G), inf_le_inf_left _ hTT' x.2⟩ :
          ↥(Subgroup.normalizer (Work.GW2.thompsonJ (S : Subgroup G) : Set G) ⊓ T'))) ?_)
    intro x y hxy
    exact Subtype.ext (by simpa using congrArg Subtype.val hxy)
  · -- `Z(S₃) ≤ Z(J(T)) ≤ S₃`
    exact ⟨S₃, hZS₃leZJT, (Work.GW2.ZJ_le T).trans hTS₃⟩

end Work.ZJB2.Step1
