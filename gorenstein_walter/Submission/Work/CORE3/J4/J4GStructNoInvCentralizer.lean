import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE3.J4.VUInvSetTrivial
import Submission.Work.CORE3.CentralizerPcoreEqVU
import Submission.Work.CORE3.J4.CardDvdSixOfDisjoint
import Submission.Work.CORE3.CosetInvCountLeSix
import Submission.Work.CORE3.FourGroupOrderThreeFixed
import Submission.Work.CORE3.NormalizerPcoreEqHhat
import Submission.Work.CORE3.RelIndexHHhat
import Submission.Work.CORE3.Case1bEightNineDefs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE3.J4.J4QuotientStep
import Submission.Work.CORE3.J4.J4CardDvdSix
import Submission.Work.CORE3.J4.J4InvolutionMemOfSup

namespace Work.CORE3.J4

open Subgroup

set_option linter.style.haveILetI false

/-- **Bender 1981 §3, step (7) preliminary** (`J4` area): in case (1) of Theorem 2.10 with
`V = O₂(Ĥ)` a four-group, an involution `y ∉ Ĥ` inverting a non-trivial odd-order subgroup
`X ≤ Ĥ` admits **no** involution of `Ĥ` centralizing `X`.

Route.  Bender's (5) (`Work.CORE3.J4.VUInvSetTrivial`) gives `X ⊓ VU = 1`, and
`[Ĥ : VU] = 6` with `Ĥ/VU` non-abelian (`Thm26Concl`) forces `|X| = 3`.  For `1 ≠ x ∈ X`,
`x ∈ Ĥ`, `orderOf x = 3`, `x ∉ VU`: an involution `s ∈ Ĥ` commuting with `x` forces
`s ∈ VU` (`J4QuotientStep`, the quotient `Ĥ/VU ≅ S₃` has no abelian subgroup of order `6`),
and then `s ∈ V = O₂(Ĥ)` (`J4InvolutionMemOfSup`, `VU/V ≅ O(Ĥ)` has odd order).  Finally
`s ∈ V` is impossible: either `x` centralizes `V`, whence `x ∈ C_Ĥ(V) = VU`
(`CentralizerPcoreEqVU`) — contradiction — or `C_V(x) = 1` (`FourGroupOrderThreeFixed`),
whence `s = 1` — contradiction. -/
theorem J4GStructNoInvCentralizer {G : Type} [Group G] [Finite G] (I : Work.CORE3.Case1Inputs)
    (hBc : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B)
    (D : Work.GW2.Case1bData B) {y : G} (hy2 : orderOf y = 2) (hyH : y ∉ B.Hhat)
    {X : Subgroup G} (hXH : X ≤ B.Hhat) (hX1 : X ≠ ⊥) (hXodd : Odd (Nat.card X))
    (hinv : Work.GW2.Inverts y X) :
    ¬ ∃ s ∈ B.Hhat, orderOf s = 2 ∧ s ∈ Subgroup.centralizer (X : Set G) := by
  classical
  rintro ⟨s, hsHhat, hs2, hsC⟩
  -- ### Bender's Theorem 2.6 and the notation `V = O₂(Ĥ)`, `U = O(Ĥ)`, `W = VU`
  have h26 : Work.GW2.Thm26Concl B := I.h26 G I.T.ft hBc B
  set V : Subgroup G := Work.GW2.pCoreIn 2 B.Hhat with hV
  set W : Subgroup G := V ⊔ B.U with hW
  set Ws : Subgroup ↥B.Hhat := W.subgroupOf B.Hhat with hWs
  have hVleH : V ≤ B.Hhat := by rw [hV]; exact Work.CORE2A.thm26Concl_O2_le_Hhat h26
  have hUleH : B.U ≤ B.Hhat := Work.CORE2A.thm26Concl_U_le_Hhat h26
  have hWleH : W ≤ B.Hhat := by rw [hW]; exact sup_le hVleH hUleH
  have hVpS : V ≤ (B.S : Subgroup G) := by rw [hV]; exact Work.CORE2A.thm26Concl_O2_le_S h26
  have hV4 : Work.GW2.IsFourGroup V := by rw [hV]; exact D.four
  have hUodd : Odd (Nat.card B.U) := Work.CORE2A.bSetup_U_odd B
  -- `W ⊴ Ĥ`
  have hWnorm : Ws.Normal := by
    rw [hWs, hW, hV]
    exact Work.CORE3.normal_VU_subgroupOf G I hBc B h1 D
  have hrel : W.relIndex B.Hhat = 6 := by
    rw [hW, hV]
    exact Work.CORE3.relIndex_VU_Hhat G I hBc B h1 D
  have hWeq : Ws.map B.Hhat.subtype = W := by
    rw [hWs, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hWleH]
  have hNW : B.Hhat ≤ Subgroup.normalizer (W : Set G) := by
    haveI : Ws.Normal := hWnorm
    have h := Work.CORE3.le_normalizer_map_subtype B.Hhat Ws
    rw [hWeq] at h
    exact h
  -- ### Step 1: `X ⊓ W = 1` (Bender (5))
  have hXW : X ⊓ W = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    rw [Subgroup.mem_inf] at hz
    obtain ⟨hzX, hzW⟩ := hz
    have h5 : Work.GW2.invSet W y = {1} := by
      rw [hW, hV]
      exact Work.CORE3.J4.VUInvSetTrivial I hBc B h1 D y hy2 hyH
    have hmem : z ∈ Work.GW2.invSet W y := ⟨hzW, hinv z hzX⟩
    rw [h5] at hmem
    exact Set.mem_singleton_iff.mp hmem
  -- ### Step 2: `|X| = 3`
  have hXcard : Nat.card X = 3 := by
    have hdvd6 : Nat.card X ∣ 6 :=
      Work.CORE3.J4.J4CardDvdSix hXW hXH hWleH hNW hrel
    have hne1 : Nat.card X ≠ 1 := fun h =>
      hX1 (Work.BSW.Cases.K4.eq_bot_of_card_eq_one h)
    have hcop : Nat.Coprime (Nat.card X) 2 := Nat.coprime_two_right.mpr hXodd
    have h3 : Nat.card X ∣ 3 := by
      have h4 : Nat.card X ∣ 2 * 3 := by norm_num at hdvd6 ⊢; exact hdvd6
      exact Nat.Coprime.dvd_of_dvd_mul_left hcop h4
    rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h | h
    · exact absurd h hne1
    · exact h
  -- ### Step 3: pick `1 ≠ x ∈ X`; then `orderOf x = 3` and `x ∉ W`
  have hex : ∃ x ∈ X, x ≠ 1 := by
    by_contra h
    apply hX1
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    by_contra hx1
    exact h ⟨x, hx, hx1⟩
  obtain ⟨x, hxX, hx1⟩ := hex
  have hx3 : orderOf x = 3 := by
    have hdvd : orderOf x ∣ 3 := by
      rw [← hXcard]; exact Subgroup.orderOf_dvd_natCard X hxX
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hx1
    · exact h
  have hxnotW : x ∉ W := by
    intro hxW'
    have hmem : x ∈ X ⊓ W := ⟨hxX, hxW'⟩
    rw [hXW] at hmem
    exact hx1 (Subgroup.mem_bot.mp hmem)
  have hcommxs : x * s = s * x := (Subgroup.mem_centralizer_iff.mp hsC) x hxX
  -- ### Step 4: `s ∈ W` (the quotient `Ĥ/VU ≅ S₃` argument)
  have hsW : s ∈ W := by
    haveI : Ws.Normal := hWnorm
    have hN : Ws.index = 6 := by
      have h1 := Subgroup.relIndex_subgroupOf (H := W) (K := B.Hhat) (L := B.Hhat) le_rfl
      rw [Subgroup.subgroupOf_self, Subgroup.relIndex_top_right, hrel] at h1
      rw [hWs]
      exact h1
    have hnab : ¬ IsMulCommutative (↥B.Hhat ⧸ Ws) := by
      rcases h26.2.2 with hbad | ⟨-, -, a, ha, b, hb, hcom⟩
      · exact absurd (Work.CORE3.isCyclic_of_le_of_isCyclic' hbad.1 B.S0_cyclic)
          (Work.CORE3.not_isCyclic_of_isFourGroup' D.four)
      · intro hcomm'
        have hq : (QuotientGroup.mk' Ws)
            ((⟨a, ha⟩ : ↥B.Hhat) * ⟨b, hb⟩ * (⟨a, ha⟩ : ↥B.Hhat)⁻¹ *
              (⟨b, hb⟩ : ↥B.Hhat)⁻¹) = 1 := by
          have h1 : (QuotientGroup.mk' Ws) (⟨a, ha⟩ : ↥B.Hhat) *
              (QuotientGroup.mk' Ws) (⟨b, hb⟩ : ↥B.Hhat) =
              (QuotientGroup.mk' Ws) (⟨b, hb⟩ : ↥B.Hhat) *
              (QuotientGroup.mk' Ws) (⟨a, ha⟩ : ↥B.Hhat) := hcomm'.is_comm.comm _ _
          simp only [map_mul, map_inv, h1]
          group
        have hmem : (⟨a, ha⟩ : ↥B.Hhat) * ⟨b, hb⟩ * (⟨a, ha⟩ : ↥B.Hhat)⁻¹ *
            (⟨b, hb⟩ : ↥B.Hhat)⁻¹ ∈ Ws := by
          have h2 := MonoidHom.mem_ker.mpr hq
          rw [QuotientGroup.ker_mk'] at h2
          exact h2
        refine hcom ?_
        have h3 : (((⟨a, ha⟩ : ↥B.Hhat) * ⟨b, hb⟩ * (⟨a, ha⟩ : ↥B.Hhat)⁻¹ *
            (⟨b, hb⟩ : ↥B.Hhat)⁻¹ : ↥B.Hhat) : G) ∈ W := Subgroup.mem_subgroupOf.mp hmem
        rw [hW, hV] at h3
        simpa using h3
    have hx'3 : orderOf (⟨x, hXH hxX⟩ : ↥B.Hhat) = 3 := by
      rw [← Subgroup.orderOf_coe (⟨x, hXH hxX⟩ : ↥B.Hhat)]
      exact hx3
    have hs'2 : orderOf (⟨s, hsHhat⟩ : ↥B.Hhat) = 2 := by
      rw [← Subgroup.orderOf_coe (⟨s, hsHhat⟩ : ↥B.Hhat)]
      exact hs2
    have hx'not : (⟨x, hXH hxX⟩ : ↥B.Hhat) ∉ Ws := by
      rw [hWs, Subgroup.mem_subgroupOf]
      exact hxnotW
    have hc' : (⟨x, hXH hxX⟩ : ↥B.Hhat) * ⟨s, hsHhat⟩ =
        ⟨s, hsHhat⟩ * ⟨x, hXH hxX⟩ := by
      refine Subtype.ext ?_
      show x * s = s * x
      exact hcommxs
    have hs'mem : (⟨s, hsHhat⟩ : ↥B.Hhat) ∈ Ws :=
      Work.CORE3.J4.J4QuotientStep Ws hN hnab hx'3 hx'not hs'2 hc'
    rw [hWs, Subgroup.mem_subgroupOf] at hs'mem
    exact hs'mem
  -- ### Step 5: `s ∈ V`
  have hVUdisj : V ⊓ B.U = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    rw [Subgroup.mem_inf] at hz
    obtain ⟨hzV, hzU⟩ := hz
    have h3 : z ∈ (B.S : Subgroup G) ⊓ B.U := ⟨hVpS hzV, hzU⟩
    rw [inf_comm, Work.CORE2A.inf_U_S_eq_bot B] at h3
    exact Subgroup.mem_bot.mp h3
  have hUnormV : B.U ≤ Subgroup.normalizer (V : Set G) := by
    rw [hV, Work.CORE3.NormalizerPcoreEqHhat G hBc B D.four]
    exact hUleH
  have hsV : s ∈ V :=
    Work.CORE3.J4.J4InvolutionMemOfSup (V := V) (U := B.U) hV4 hVUdisj hUnormV hUodd
      (by rw [hW] at hsW; exact hsW) hs2
  -- ### Step 6: contradiction
  have hxN : x ∈ Subgroup.normalizer (V : Set G) := by
    rw [hV, Work.CORE3.NormalizerPcoreEqHhat G hBc B D.four]
    exact hXH hxX
  have hxnc : x ∉ Subgroup.centralizer (V : Set G) := by
    intro hxc
    have hmem : x ∈ W := by
      have hxmem : x ∈ Subgroup.centralizer
          ((Work.GW2.pCoreIn 2 B.Hhat : Subgroup G) : Set G) := by
        simpa only [hV] using hxc
      have h2 : x ∈ Subgroup.centralizer
          ((Work.GW2.pCoreIn 2 B.Hhat : Subgroup G) : Set G) ⊓ B.Hhat :=
        Subgroup.mem_inf.mpr ⟨hxmem, hXH hxX⟩
      rw [Work.CORE3.CentralizerPcoreEqVU G I hBc B h1 D] at h2
      rw [hW, hV]
      exact h2
    exact hxnotW hmem
  have hfix : V ⊓ Subgroup.centralizer ({x} : Set G) = ⊥ :=
    Work.CORE3.FourGroupOrderThreeFixed (V := V) (x := x) hV4 hxN hx3 hxnc
  have hsVcx : s ∈ V ⊓ Subgroup.centralizer ({x} : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨hsV, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact hcommxs
  rw [hfix] at hsVcx
  have hs1 : s = 1 := Subgroup.mem_bot.mp hsVcx
  exact absurd hs2 (by rw [hs1]; norm_num)

end Work.CORE3.J4
