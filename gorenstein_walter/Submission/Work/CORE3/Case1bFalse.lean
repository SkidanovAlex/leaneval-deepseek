import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE2A.inf_U_S_eq_bot
import Submission.Work.CORE3.NormalizerPcoreEqHhat
import Submission.Work.CORE3.SylowDihedral
import Submission.Work.CORE3.H_eq_U_sup_S
import Submission.Work.CORE3.RelIndexHHhat
import Submission.Work.BSW.Cases.K4.CardSup
import Submission.Work.CORE3.LePCoreInOfNormal
import Submission.Work.CORE3.LeSylowOfNormal
import Submission.Work.CORE3.LeCentralizerOfCoprimeNormal

namespace Work.CORE3

set_option linter.dupNamespace false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open Subgroup
open Work.GW2

/-- If `M` is a maximal subgroup of a simple group `G` and `U ≤ M` is a nontrivial subgroup
normalized by `M`, then `N_G(U) = M`: otherwise maximality forces `N_G(U) = ⊤`, so `U` would be
normal in `G` and hence trivial or everything, and both are excluded. -/
theorem normalizer_eq_of_isCoatom {G : Type} [Group G] [IsSimpleGroup G]
    (M : Subgroup G) (hM : IsCoatom M) (U : Subgroup G) (hUM : U ≤ M)
    (hUn : M ≤ Subgroup.normalizer (U : Set G)) (hUbot : U ≠ ⊥) :
    Subgroup.normalizer (U : Set G) = M := by
  refine le_antisymm ?_ hUn
  by_contra hcon
  have hlt : M < Subgroup.normalizer (U : Set G) := lt_of_le_not_ge hUn hcon
  have htop : Subgroup.normalizer (U : Set G) = ⊤ := hM.lt_iff.mp hlt
  haveI hUnorm : U.Normal := Subgroup.normalizer_eq_top_iff.mp htop
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal U with h | h
  · exact hUbot h
  · exact hM.ne_top (top_le_iff.mp (h ▸ hUM))

/-- A subgroup `H` which is normal in a bigger subgroup `K` is normalized by `K`. -/
theorem le_normalizer_of_subgroupOf_normal {G : Type} [Group G] {H K : Subgroup G}
    (hHK : H ≤ K) (h : (H.subgroupOf K).Normal) : K ≤ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro k hk x hx
  exact (Subgroup.normal_subgroupOf_iff hHK).mp h x k hx hk

/-- `O₂(K)` is a `2`-group, for any subgroup `K` of an ambient group. -/
theorem isPGroup_pCoreIn_two' {G : Type} [Group G] [Finite G] (K : Subgroup G) :
    IsPGroup 2 (pCoreIn 2 K) := by
  have hsup : IsPGroup 2 ↥(sSup {N : Subgroup ↥K | N.Normal ∧ IsPGroup 2 N}) :=
    Sylow.sSup_of_normal (G := ↥K) (p := 2) {N : Subgroup ↥K | N.Normal ∧ IsPGroup 2 N}
      (fun N hN => hN.2) (fun N hN => hN.1)
  have hcore : IsPGroup 2 (pCore 2 ↥K) := hsup.to_le (Subgroup.normalCore_le _)
  unfold pCoreIn
  exact hcore.map K.subtype

/-- **Bender 1981 §3, Theorem 2.6 in subcase (1b).**  If `O₂(Ĥ) = S ⊓ C_G(U)` (the conclusion of
Theorem 2.6) then `O₂(Ĥ) = O₂(H)` for `H = C_G(t)`: `O₂(Ĥ)` is normal in `H` (it is normal in
`Ĥ ≥ H`) and a `2`-group, so it lies in `O₂(H)`; conversely `O₂(H) ⊴ H` is a `2`-group, hence lies
in the Sylow `2`-subgroup `S` of `H`, and `O₂(H)` commutes with `U = O(H)` (normal subgroups of
`H` of coprime order), so `O₂(H) ≤ S ⊓ C_G(U) = O₂(Ĥ)`. -/
theorem pCoreIn_two_H_eq_Hhat {G : Type} [Group G] [Finite G] (B : BenderSetup G)
    (hVS : (B.S : Subgroup G) ⊓ Subgroup.centralizer (B.U : Set G) = pCoreIn 2 B.Hhat) :
    pCoreIn 2 B.H = pCoreIn 2 B.Hhat := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSH : (B.S : Subgroup G) ≤ B.H := Work.CORE2A.bSetup_S_le_H B
  have hHhatN : B.Hhat ≤ Subgroup.normalizer (pCoreIn 2 B.Hhat : Set G) :=
    Work.CORE3.le_normalizer_map_subtype B.Hhat (pCore 2 ↥B.Hhat)
  have hHN : B.H ≤ Subgroup.normalizer (pCoreIn 2 B.H : Set G) :=
    Work.CORE3.le_normalizer_map_subtype B.H (pCore 2 ↥B.H)
  have hUN : B.H ≤ Subgroup.normalizer (B.U : Set G) :=
    Work.CORE3.le_normalizer_map_subtype_of_normal' (K := B.H)
      (N := Work.GW2.oddCore ↥B.H) inferInstance
  have hV_le_H : pCoreIn 2 B.Hhat ≤ B.H := by
    rw [← hVS]
    exact le_trans inf_le_left hSH
  refine le_antisymm ?_ ?_
  · have hT2 : IsPGroup 2 (pCoreIn 2 B.H) := isPGroup_pCoreIn_two' B.H
    have hTS : pCoreIn 2 B.H ≤ (B.S : Subgroup G) :=
      Work.CORE3.LeSylowOfNormal (K := B.H) (N := pCoreIn 2 B.H) B.S hSH
        (Subgroup.map_subtype_le (Work.GW2.pCore 2 ↥B.H)) hHN hT2
    have hTU : pCoreIn 2 B.H ≤ Subgroup.centralizer (B.U : Set G) := by
      have hcop : (Nat.card (pCoreIn 2 B.H)).Coprime (Nat.card B.U) := by
        obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hT2
        rw [hk]
        exact Nat.Coprime.pow_left k (Work.CORE2A.bSetup_U_odd B).coprime_two_left
      exact Work.CORE3.LeCentralizerOfCoprimeNormal (K := B.H)
        (Subgroup.map_subtype_le (Work.GW2.pCore 2 ↥B.H))
        (Work.CORE2A.bSetup_U_le_H B) hHN hUN hcop
    rw [← hVS]
    exact le_inf hTS hTU
  · exact Work.CORE3.LePCoreInOfNormal hV_le_H (le_trans B.H_le_Hhat hHhatN)
      (isPGroup_pCoreIn_two' B.Hhat)

/-- **Sylow counting lemma (Bender 1.8(ii)).**  Let `G` be a finite simple group of order `2520`
and `M` a maximal subgroup of order `72`.  If `U ≤ M` is normal in `M` of order `3`, then some
conjugate of `U` is contained in `M` and different from `U`.

Proof: `N_G(U) = M` (`normalizer_eq_of_isCoatom`).  Let `Q` be a Sylow `3`-subgroup of `↥M`
containing `U.subgroupOf M` (Sylow's theorem inside `M`) and let `P ≤ M` be its image in `G`; both
have order `9`, so `P` is a Sylow `3`-subgroup of `M` and of `G`.  If `N_G(P) ≤ M`, then the
normalizer of `P` inside `M` is the normalizer of `Q` inside `↥M`
(`Subgroup.subgroupOf_normalizer_eq`), so `|M : N_M(P)| = n₃(M) ≡ 1 (mod 3)`; but
`n₃(G) = |G : N_G(P)| = 35 · |M : N_G(P)| ≡ 35 ≡ 2 (mod 3)`, contradicting Sylow's congruence
`n₃(G) ≡ 1 (mod 3)`.  So there is `g ∈ N_G(P)`, `g ∉ M`; then `U^g ≤ P^g = P ≤ M`, and
`U^g ≠ U` because `U^g = U` would give `g ∈ N_G(U) = M`. -/
theorem exists_conj_le_of_coatom_of_card (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (M : Subgroup G) (hM : IsCoatom M) (hMcard : Nat.card M = 72) (hGcard : Nat.card G = 2520)
    (U : Subgroup G) (hUM : U ≤ M) (hUn : (U.subgroupOf M).Normal) (hUcard : Nat.card U = 3) :
    ∃ g : G, U.map (MulAut.conj g).toMonoidHom ≤ M ∧
      U.map (MulAut.conj g).toMonoidHom ≠ U := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (Sylow 3 ↥M) := inferInstance
  haveI : Finite (Sylow 3 G) := inferInstance
  -- (1) `N_G(U) = M`
  have hUbot : U ≠ ⊥ := by
    intro h
    have h1 : Nat.card ↥U = 1 := by rw [h]; exact Subgroup.card_bot
    omega
  have hNU : Subgroup.normalizer (U : Set G) = M :=
    normalizer_eq_of_isCoatom M hM U hUM (le_normalizer_of_subgroupOf_normal hUM hUn) hUbot
  -- (2) a Sylow `3`-subgroup of `↥M` containing `U.subgroupOf M`
  have hU'3 : IsPGroup 3 (U.subgroupOf M) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv, hUcard]
    norm_num
  obtain ⟨Q, hU'Q⟩ := IsPGroup.exists_le_sylow hU'3
  have hQcard : Nat.card ↥(Q : Subgroup ↥M) = 9 := by
    rw [Sylow.card_eq_multiplicity, hMcard]
    norm_num [Nat.factorization]
  set P : Subgroup G := (Q : Subgroup ↥M).map M.subtype with hPdef
  have hPcard : Nat.card P = 9 := by
    rw [hPdef, Subgroup.card_map_of_injective M.subtype_injective, hQcard]
  have hP3 : IsPGroup 3 P := Q.isPGroup'.map M.subtype
  have hPM : P ≤ M := Subgroup.map_subtype_le _
  have hU_le_P : U ≤ P := by
    intro x hx
    rw [hPdef]
    refine Subgroup.mem_map.mpr ⟨⟨x, hUM hx⟩, ?_, rfl⟩
    exact hU'Q (by rw [Subgroup.mem_subgroupOf]; exact hx)
  -- (3) `P` is a Sylow `3`-subgroup of `G`
  have hPindex : P.index = 280 := by
    have h := Subgroup.card_mul_index P
    rw [hPcard, hGcard] at h
    omega
  let P' : Sylow 3 G := hP3.toSylow (by rw [hPindex]; norm_num)
  have hP'coe : (P' : Subgroup G) = P := rfl
  -- (4) the Sylow numbers
  have hM_count : Nat.card (Sylow 3 ↥M) = (Subgroup.normalizer (Q : Set ↥M)).index :=
    Sylow.card_eq_index_normalizer Q
  have hM_mod : Nat.card (Sylow 3 ↥M) ≡ 1 [MOD 3] := card_sylow_modEq_one 3 ↥M
  have hG_mod : Nat.card (Sylow 3 G) ≡ 1 [MOD 3] := card_sylow_modEq_one 3 G
  have hG_count : Nat.card (Sylow 3 G) = (Subgroup.normalizer (P : Set G)).index := by
    rw [← hP'coe]
    exact Sylow.card_eq_index_normalizer P'
  -- (5) `N_G(P) ⊄ M`
  have hnotle : ¬ (Subgroup.normalizer (P : Set G) ≤ M) := by
    intro hle
    -- the normalizer of `P` inside `M` is the normalizer of `Q` inside `↥M`
    have hid : (Subgroup.normalizer (P : Set G)).subgroupOf M =
        Subgroup.normalizer (Q : Set ↥M) := by
      rw [hPdef, Subgroup.subgroupOf_normalizer_eq (Subgroup.map_subtype_le (Q : Subgroup ↥M))]
      have hQM : ((Q : Subgroup ↥M).map M.subtype).subgroupOf M = (Q : Subgroup ↥M) := by
        ext y
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
        constructor
        · rintro ⟨z, hz, hzy⟩
          have hzy' : z = y := Subtype.ext hzy
          rwa [hzy'] at hz
        · intro hy
          exact ⟨y, hy, rfl⟩
      exact congrArg (fun H : Subgroup ↥M => Subgroup.normalizer (H : Set ↥M)) hQM
    have hm : (Subgroup.normalizer (P : Set G)).relIndex M = Nat.card (Sylow 3 ↥M) := by
      have h1 : (Subgroup.normalizer (P : Set G)).relIndex M =
          ((Subgroup.normalizer (P : Set G)).subgroupOf M).index := rfl
      rw [h1, hid, ← hM_count]
    have hm_mod : (Subgroup.normalizer (P : Set G)).relIndex M ≡ 1 [MOD 3] := by
      rw [hm]; exact hM_mod
    have hMindex : M.index = 35 := by
      have h := Subgroup.card_mul_index M
      rw [hMcard, hGcard] at h
      omega
    have hNindex : (Subgroup.normalizer (P : Set G)).index =
        35 * (Subgroup.normalizer (P : Set G)).relIndex M := by
      have h := Subgroup.relIndex_mul_index (H := Subgroup.normalizer (P : Set G)) (K := M) hle
      rw [hMindex] at h
      omega
    have hG_mod' : (Subgroup.normalizer (P : Set G)).index ≡ 1 [MOD 3] := by
      rw [← hG_count]; exact hG_mod
    have h4 : 35 * (Subgroup.normalizer (P : Set G)).relIndex M ≡ 1 [MOD 3] := by
      rw [← hNindex]; exact hG_mod'
    have h5 : 35 * (Subgroup.normalizer (P : Set G)).relIndex M ≡ 35 * 1 [MOD 3] :=
      Nat.ModEq.mul_left 35 hm_mod
    have h6 : (35 : ℕ) ≡ 1 [MOD 3] := h5.symm.trans h4
    norm_num at h6
  -- (6) the witness
  obtain ⟨g, hgN, hgM⟩ := Set.not_subset.mp hnotle
  refine ⟨g, ?_, ?_⟩
  · have hPg : P.map (MulAut.conj g).toMonoidHom = P := by
      refine Subgroup.eq_of_le_of_card_ge ?_ ?_
      · rintro x ⟨y, hy, rfl⟩
        have h1 := (Subgroup.mem_normalizer_iff.mp hgN y).mp hy
        simpa [MulAut.conj_apply] using h1
      · have hc : Nat.card ↥(P.map (MulAut.conj g).toMonoidHom) = Nat.card ↥P := by
          rw [← Work.CORE2A.conjSub_eq_map]
          exact Work.CORE2A.card_conjSub g P
        rw [hc]
    calc U.map (MulAut.conj g).toMonoidHom ≤ P.map (MulAut.conj g).toMonoidHom :=
          Subgroup.map_mono hU_le_P
      _ = P := hPg
      _ ≤ M := hPM
  · intro hconj
    have hmem : g ∈ Subgroup.normalizer (U : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        have h1 : g * y * g⁻¹ ∈ U.map (MulAut.conj g).toMonoidHom :=
          ⟨y, hy, by simp [MulAut.conj_apply]⟩
        rwa [hconj] at h1
      · intro hy
        have h1 : g * y * g⁻¹ ∈ U.map (MulAut.conj g).toMonoidHom := by rwa [hconj]
        obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp h1
        have hzy' : g * z * g⁻¹ = g * y * g⁻¹ := by simpa [MulAut.conj_apply] using hzy
        have hzy'' : z = y := by
          calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
            _ = g⁻¹ * (g * y * g⁻¹) * g := by rw [hzy']
            _ = y := by group
        rwa [hzy''] at hz
    rw [hNU] at hmem
    exact hgM hmem

namespace Work.CORE3

/-- Bender 1981 §3, p. 224, end of §3.  Deliverable `Work.GW2.Case1bFalseProp`.

From the earlier leaves (`hSetup : Case1bSetupProp` gives `D : Case1bData B`; `hCount`, `hFive`,
`h89`, `hIndex`): `K = U` has order 3, `|S| = 8`, `|G| = 2520` and `|G:Ĥ| = 35`, and `Ĥ` is the
normalizer of `U` (order 72) and of the four-group `V = O₂(Ĥ) = pCoreIn 2 (U ⊔ S)`, with `U` not
normal in `G` and `U^g ≤ N_G(V)` for suitable `g` (Bender 1.8(ii)).  These are exactly the
hypotheses of `I.hA7 : A7Rec2Prop` (`Work.A7REC.A7Rec2Prop`, design pass 4) with the extra premise
`SmallerDGroups G` supplied by `BenderCtx.ih`; its conclusion
`Nonempty (G ≃* alternatingGroup (Fin 7))` contradicts `BenderCtx.notA7`. -/
theorem Case1bFalse (I : Case1Inputs) (hSetup : Case1bSetupProp) (hCount : Case1bCountProp)
    (hFive : Case1bFiveProp) (h89 : Case1bEightNineProp) (hIndex : Case1bIndexProp) :
    Case1bFalseProp := by
  intro G hGrp hFin hFT hBc B h1 h4
  classical
  obtain ⟨D⟩ := hSetup G hFT hBc B h1 h4
  have h26 := I.h26 G hFT hBc B
  have hCnt := hCount G hFT hBc B h1 D
  have hIdx := hIndex G hFT hBc B h1 D
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsSimpleGroup G := hBc.simple
  -- ## Cardinalities
  have hHhatIdx : B.Hhat.index = 35 := hIdx.1
  have hcardG : Nat.card G = 2520 := hIdx.2
  have hcardHhat : Nat.card ↥B.Hhat = 72 := by
    have h := Subgroup.card_mul_index B.Hhat
    rw [hHhatIdx, hcardG] at h
    omega
  have hIdxH : B.H.index = 105 := by
    obtain ⟨-, -, h3, -, -⟩ := hCnt
    rw [h3, hHhatIdx]
  have hcardH : Nat.card ↥B.H = 24 := by
    have h := Subgroup.card_mul_index B.H
    rw [hIdxH, hcardG] at h
    omega
  have hSH : (B.S : Subgroup G) ≤ B.H := Work.CORE2A.bSetup_S_le_H B
  have hcardS : Nat.card ↥(B.S : Subgroup G) = 8 := D.S8
  have hUS : B.U ⊔ (B.S : Subgroup G) = B.H := Work.CORE3.H_eq_U_sup_S G I.T hBc B
  have hUSbot : B.U ⊓ (B.S : Subgroup G) = ⊥ := Work.CORE2A.inf_U_S_eq_bot B
  -- `U = O(H)` is normal in `H`
  have hHN : B.H ≤ Subgroup.normalizer (B.U : Set G) :=
    Work.CORE3.le_normalizer_map_subtype_of_normal' (K := B.H)
      (N := Work.GW2.oddCore ↥B.H) inferInstance
  have hSUN : (B.S : Subgroup G) ≤ Subgroup.normalizer (B.U : Set G) := le_trans hSH hHN
  have hcardU : Nat.card ↥B.U = 3 := by
    have h := Work.BSW.Cases.K4.card_sup_of_le_normalizer_of_inf_eq_bot hSUN hUSbot
    rw [hUS, hcardH, hcardS] at h
    omega
  -- ## A Sylow 2-subgroup of order `8` is dihedral of order `8`
  obtain ⟨n, hn2, hdih⟩ := Work.CORE3.SylowDihedral G hBc B
  have hn4 : n = 4 := by
    obtain ⟨e⟩ := hdih
    have h1 : Nat.card ↥(B.S : Subgroup G) = 2 * n := by
      rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    omega
  have hSdih : Nonempty ((B.S : Subgroup G) ≃* DihedralGroup 4) := hn4 ▸ hdih
  -- ## `V = O₂(Ĥ) = O₂(U ⊔ S)`
  have hVeq : pCoreIn 2 (B.U ⊔ (B.S : Subgroup G)) = pCoreIn 2 B.Hhat := by
    rw [hUS]
    exact pCoreIn_two_H_eq_Hhat B h26.2.1
  have hV4 : IsFourGroup (pCoreIn 2 (B.U ⊔ (B.S : Subgroup G))) := by
    rw [hVeq]
    exact h4
  -- ## `Ĥ = N_G(U) = N_G(V)`
  have hU_le_Hhat : B.U ≤ B.Hhat := Work.CORE2A.bSetup_U_le_Hhat B
  have hUnH : (B.U.subgroupOf B.H).Normal := by
    have h1 : B.U = Subgroup.map B.H.subtype (Work.GW2.oddCore ↥B.H) := rfl
    rw [h1]
    rw [Subgroup.normal_subgroupOf_iff (Subgroup.map_subtype_le (Work.GW2.oddCore ↥B.H))]
    intro x k hx hk
    rw [Subgroup.mem_map] at hx ⊢
    obtain ⟨y, hy, hyx⟩ := hx
    subst hyx
    exact ⟨⟨k, hk⟩ * y * ⟨k, hk⟩⁻¹,
      Subgroup.Normal.conj_mem (inferInstance : (Work.GW2.oddCore ↥B.H).Normal) y hy
        ⟨k, hk⟩, by simp⟩
  have hUn : (B.U.subgroupOf B.Hhat).Normal := by
    have h1 : B.U = Work.GW2.oddCoreIn B.Hhat := h26.1.symm
    have hmain : ((Work.GW2.oddCoreIn B.Hhat).subgroupOf B.Hhat).Normal := by
      show ((Subgroup.map B.Hhat.subtype (Work.GW2.oddCore ↥B.Hhat)).subgroupOf B.Hhat).Normal
      rw [Subgroup.normal_subgroupOf_iff (Subgroup.map_subtype_le (Work.GW2.oddCore ↥B.Hhat))]
      intro x k hx hk
      rw [Subgroup.mem_map] at hx ⊢
      obtain ⟨y, hy, hyx⟩ := hx
      subst hyx
      exact ⟨⟨k, hk⟩ * y * ⟨k, hk⟩⁻¹,
        Subgroup.Normal.conj_mem (inferInstance : (Work.GW2.oddCore ↥B.Hhat).Normal) y hy
          ⟨k, hk⟩, by simp⟩
    rwa [h1]
  have hHhat_le_NU : B.Hhat ≤ Subgroup.normalizer (B.U : Set G) :=
    le_normalizer_of_subgroupOf_normal hU_le_Hhat hUn
  have hUbot : B.U ≠ ⊥ := by
    intro h
    have h1 : Nat.card ↥B.U = 1 := by rw [h]; exact Subgroup.card_bot
    omega
  have hNU : Subgroup.normalizer (B.U : Set G) = B.Hhat :=
    normalizer_eq_of_isCoatom B.Hhat B.Hhat_coatom B.U hU_le_Hhat hHhat_le_NU hUbot
  have hNV : Subgroup.normalizer (pCoreIn 2 B.Hhat : Set G) = B.Hhat :=
    Work.CORE3.NormalizerPcoreEqHhat G hBc B h4
  have hNUV :
      Subgroup.normalizer (B.U : Set G) =
        Subgroup.normalizer (pCoreIn 2 (B.U ⊔ (B.S : Subgroup G)) : Set G) := by
    rw [hVeq, hNU, hNV]
  have hNUcard : Nat.card (Subgroup.normalizer (B.U : Set G)) = 72 := by
    rw [hNU]
    exact hcardHhat
  -- ## A conjugate of `U` inside `N_G(V)`
  obtain ⟨g, hgM, hgne⟩ :=
    exists_conj_le_of_coatom_of_card G B.Hhat B.Hhat_coatom hcardHhat hcardG B.U
      hU_le_Hhat hUn hcardU
  have hgle : B.U.map (MulAut.conj g).toMonoidHom ≤
      Subgroup.normalizer (pCoreIn 2 (B.U ⊔ (B.S : Subgroup G)) : Set G) := by
    rw [hVeq, hNV]
    exact hgM
  -- ## Bender's 1.8 data, hence `A7Rec2Prop`
  have hY : Work.A7REC.A7RecHyps G B.S B.t B.U
      (pCoreIn 2 (B.U ⊔ (B.S : Subgroup G))) :=
    ⟨hBc.simple, hcardG, hSdih, Work.CORE2A.bSetup_t_mem_S B, B.t_order,
      (fun x hx => (Subgroup.mem_centralizer_iff.mp (hSH hx) B.t (by simp)).symm),
      hUS.symm, hcardU, hUnH, rfl, hV4, ⟨g, hgne, hgle⟩, hNUV, hNUcard⟩
  exact hBc.notA7.false (I.hA7 G B.S B.t B.U (pCoreIn 2 (B.U ⊔ (B.S : Subgroup G))) hY hBc.ih).some

end Work.CORE3

open Subgroup
open Work.GW2

/-- The lemma at the namespace of the file path, for callers that do not want the doubly nested
name (the statement is the same). -/
theorem Case1bFalse (I : Case1Inputs) (hSetup : Case1bSetupProp) (hCount : Case1bCountProp)
    (hFive : Case1bFiveProp) (h89 : Case1bEightNineProp) (hIndex : Case1bIndexProp) :
    Case1bFalseProp :=
  _root_.Work.CORE3.Work.CORE3.Case1bFalse I hSetup hCount hFive h89 hIndex

end Work.CORE3
