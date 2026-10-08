import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE3.MDataAux
import Submission.Work.CORE3.Case1aA7
import Submission.Work.CORE3.Case1aBothInvert
import Submission.Work.CORE3.Case1aFrattiniConj
import Submission.Work.CORE3.Case1aFrattiniSAct
import Submission.Work.CORE3.Case1aThmCInputs
import Submission.Work.CORE3.Case1aBFpf
import Submission.Work.CORE3.Core13InfNeBot
import Submission.Work.CORE3.Core13LeOfInverted
import Submission.Work.CORE3.Core13PcoreLeM
import Submission.Work.CORE3.Core13CUt1
import Submission.Work.CORE3.Core13CommPB

namespace Work.CORE3

namespace Work.CORE3

open Subgroup
open Work.GW2

/-- Design pass 13 §1, the assembly: `Case1aDirectProp` follows from the §3a inputs and the
leaves D1–D6.

Preamble exactly as in `Work.CORE3.Case1aThmCInputs`: `p ∣ |C_U(S)|` (`hFr` at `⊥`),
`P₂ ∈ Syl_p(C_U(S))` (`bfpf_exists_pSubgroup_le_of_dvd`), a coatom `M ⊇ N_G(P₂)`
(`bfpf_exists_isCoatom_le_of_ne_top`), and `p = 3` (from `hA7`'s `|P₀| = 3`).  Then D6
(`Work.CORE3.Core13CUt1`, import `Submission.Work.CORE3.Core13CUt1`) gives the join and D5
(`Work.CORE3.Core13CommPB`, import `Submission.Work.CORE3.Core13CommPB`) the elementwise
commutation. -/
theorem Case1aDirectV13 (I : Case1Inputs) (hFr : Case1aFrattiniProp) (hAb : Case1aAbelianProp)
    (hA7 : Case1aA7Prop) (hMD : Case1aMDataProp) (hInv : Case1aBothInvertProp) :
    Case1aDirectProp := by
  intro G _instG _finG hFT hCtx B hCase1 hHhat D
  classical
  haveI : Fact D.p.Prime := ⟨D.hp⟩
  haveI : IsSimpleGroup G := hCtx.simple
  -- ## Step 0: the preamble of `Work.CORE3.Case1aThmCInputs`
  -- `Bc = C_U(S)` collects a `p`-element (`hFr` at `P₂ = ⊥`), so it has a Sylow `p`-subgroup.
  set Bc : Subgroup G := B.U ⊓ Subgroup.centralizer ((B.S : Subgroup G) : Set G) with hBcdef
  have hpB : D.p ∣ Nat.card Bc := by
    by_contra hpdvd
    have hrel : ¬ D.p ∣ (⊥ : Subgroup G).relIndex Bc := by
      rwa [Subgroup.relIndex_bot_left]
    exact (hFr G hFT hCtx B hCase1 hHhat D ⊥ bot_le IsPGroup.of_bot hrel).2.2 rfl
  obtain ⟨P2, hP2le, hP2grp, hP2ndvd⟩ := bfpf_exists_pSubgroup_le_of_dvd D.p Bc hpB
  have hP2Hhat : P2 ≤ B.Hhat :=
    hP2le.trans (le_trans inf_le_left (Work.CORE2A.bSetup_U_le_Hhat B))
  -- `N_G(P₂)` is a proper subgroup of the simple `G`, hence lies in a coatom `M`.
  have hNHat_ne : Subgroup.normalizer (P2 : Set G) ≠ ⊤ := by
    intro htop
    haveI : P2.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal P2 with h | h
    · exact (hFr G hFT hCtx B hCase1 hHhat D P2 hP2le hP2grp hP2ndvd).2.2 h
    · rw [h] at hP2Hhat
      exact B.Hhat_coatom.ne_top (top_le_iff.mp hP2Hhat)
  obtain ⟨M, hMcoat, hNM⟩ := bfpf_exists_isCoatom_le_of_ne_top _ hNHat_ne
  -- ## Step 1: `p = 3`, from `|O_p(U) ⊓ M| = 3` (`hA7`)
  have hP0card : Nat.card (pCoreIn D.p B.U ⊓ M : Subgroup G) = 3 :=
    (hA7 G hFT hCtx B hCase1 hHhat D P2 M hP2le hP2grp hP2ndvd hMcoat hNM).2.2.2.2
  have hP0pg : IsPGroup D.p (pCoreIn D.p B.U ⊓ M : Subgroup G) :=
    (c1aIsPGroup_pCoreIn D.p B.U).to_le inf_le_left
  have hp3 : D.p = 3 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP0pg
    have hk3 : D.p ^ k = 3 := by rw [← hk, hP0card]
    have hk1 : k ≠ 0 := by rintro rfl; simp at hk3
    have hd : D.p ∣ 3 := by
      have h := dvd_pow_self D.p hk1
      rwa [hk3] at h
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
    · exact absurd h1 D.hp.ne_one
    · exact h3
  -- ## Step 2: D6 gives the join, D5 the elementwise commutation
  exact ⟨Core13CUt1 G I hInv hFT hCtx B hCase1 hHhat D hp3,
    Core13CommPB G I hAb hA7 hMD hFT hCtx B hCase1 hHhat D P2 M hP2le hP2grp hP2ndvd
      hMcoat hNM⟩

end Work.CORE3

open Subgroup
open Work.GW2

/-- The same lemma, mirrored at the namespace of the file path, so that it can be cited both as
`Work.CORE3.Case1aDirectV13` (the name the area requests) and as
`Work.CORE3.Work.CORE3.Case1aDirectV13` (the skeleton's namespace layout). -/
theorem Case1aDirectV13 (I : Case1Inputs) (hFr : Case1aFrattiniProp) (hAb : Case1aAbelianProp)
    (hA7 : Case1aA7Prop) (hMD : Case1aMDataProp) (hInv : Case1aBothInvertProp) :
    Case1aDirectProp :=
  _root_.Work.CORE3.Work.CORE3.Case1aDirectV13 I hFr hAb hA7 hMD hInv

end Work.CORE3
