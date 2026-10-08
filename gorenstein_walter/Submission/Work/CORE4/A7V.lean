import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.Defs10
import Submission.Work.CORE4.API
import Submission.Work.CORE4.CountSetup
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.A7Vsylow
import Submission.Work.CORE4.A7VnotCyclic

namespace Work.CORE4

open scoped MatrixGroups
open Subgroup

variable {G : Type} [Group G] [Finite G]

/-- `O_p(K)` is a `p`-group. -/
theorem A7V_isPGroup_pCoreIn (p : ℕ) (K : Subgroup G) : IsPGroup p (Work.GW2.pCoreIn p K) := by
  have hsup : IsPGroup p ↥(sSup {N : Subgroup ↥K | N.Normal ∧ IsPGroup p N}) :=
    Sylow.sSup_of_normal {N : Subgroup ↥K | N.Normal ∧ IsPGroup p N}
      (fun N hN => hN.2) (fun N hN => hN.1)
  exact (hsup.to_le (Subgroup.normalCore_le _)).map K.subtype

/-- `O_p(K)` is normalised by `K`. -/
theorem A7V_conj_mem_pCoreIn (p : ℕ) (K : Subgroup G) {h x : G} (hh : h ∈ K)
    (hx : x ∈ Work.GW2.pCoreIn p K) : h * x * h⁻¹ ∈ Work.GW2.pCoreIn p K := by
  obtain ⟨y, hy, hyx⟩ := hx
  have hmem : (⟨h, hh⟩ : ↥K) * y * (⟨h, hh⟩ : ↥K)⁻¹ ∈ Work.GW2.pCore p ↥K :=
    (Work.GW2.pCore_normal p ↥K).conj_mem y hy ⟨h, hh⟩
  exact ⟨_, hmem, by rw [← hyx]; simp⟩

/-- If `A ≤ K` is a normal `p`-subgroup of `K`, then `A ≤ O_p(K)`. -/
theorem A7V_le_pCoreIn_of_normal_isPGroup (p : ℕ) (K : Subgroup G)
    {A : Subgroup G} (hA : A ≤ K) (hAn : (A.subgroupOf K).Normal)
    (hAp : IsPGroup p (A.subgroupOf K)) : A ≤ Work.GW2.pCoreIn p K := by
  haveI := hAn
  have h1 : A.subgroupOf K ≤ Work.GW2.pCore p (↥K) :=
    Subgroup.normal_le_normalCore.mpr (le_sSup ⟨hAn, hAp⟩)
  calc A = (A.subgroupOf K).map K.subtype := (Subgroup.map_subgroupOf_eq_of_le hA).symm
    _ ≤ (Work.GW2.pCore p (↥K)).map K.subtype := Subgroup.map_mono h1
    _ = Work.GW2.pCoreIn p K := rfl

/-- If `A, B ≤ H` are normal in `H` with `A ⊓ B = ⊥`, then `A ≤ C(B)` in `G`. -/
theorem A7V_le_centralizer_of_normal_inf_eq_bot {H A Bc : Subgroup G}
    (hA : A ≤ H) (hB : Bc ≤ H) (hAn : (A.subgroupOf H).Normal)
    (hBn : (Bc.subgroupOf H).Normal) (hinf : A ⊓ Bc = ⊥) :
    A ≤ Subgroup.centralizer (Bc : Set G) := by
  have hinf' : (A.subgroupOf H) ⊓ (Bc.subgroupOf H) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.mp hy
    have h3 : (y : G) ∈ A ⊓ Bc :=
      ⟨Subgroup.mem_subgroupOf.mp hy1, Subgroup.mem_subgroupOf.mp hy2⟩
    rw [hinf] at h3
    exact Subtype.ext (Subgroup.mem_bot.mp h3)
  haveI := hAn
  haveI := hBn
  have hcomm : ⁅A.subgroupOf H, Bc.subgroupOf H⁆ = ⊥ := by
    have h := Subgroup.commutator_le_inf (A.subgroupOf H) (Bc.subgroupOf H)
    exact le_bot_iff.mp (hinf' ▸ h)
  have hcent := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have h1 : (⟨x, hA hx⟩ : ↥H) ∈ Subgroup.centralizer ((Bc.subgroupOf H : Subgroup ↥H) : Set ↥H) :=
    hcent (Subgroup.mem_subgroupOf.mpr hx)
  have h2 := (Subgroup.mem_centralizer_iff.mp h1) ⟨u, hB hu⟩ (Subgroup.mem_subgroupOf.mpr hu)
  exact Subtype.ext_iff.mp h2

/-- (G2) `O₂(Ĥ) = O₂(H)` (Bender's `V = O₂(H) = O₂(Ĥ)`), using Theorem 2.6 for
`O₂(Ĥ) = S ⊓ C_G(U)`. -/
theorem A7V_pCoreIn_Hhat_eq_pCoreIn_H
    (h26 : (B : Work.GW2.BenderSetup G) →
      (B.S : Subgroup G) ⊓ Subgroup.centralizer (B.U : Set G) = Work.GW2.pCoreIn 2 B.Hhat)
    (B : Work.GW2.BenderSetup G) :
    Work.GW2.pCoreIn 2 B.Hhat = Work.GW2.pCoreIn 2 B.H := by
  apply le_antisymm
  · -- `O₂(Ĥ) ≤ O₂(H)`
    have hleH : Work.GW2.pCoreIn 2 B.Hhat ≤ B.H := by
      rw [← h26 B]; exact le_trans inf_le_left B.S_le_H
    have hnorm : ((Work.GW2.pCoreIn 2 B.Hhat).subgroupOf B.H).Normal := by
      rw [Subgroup.normal_subgroupOf_iff hleH]
      intro h k hh hk
      exact A7V_conj_mem_pCoreIn 2 B.Hhat (B.H_le_Hhat hk) hh
    have hp : IsPGroup 2 ((Work.GW2.pCoreIn 2 B.Hhat).subgroupOf B.H) :=
      (A7V_isPGroup_pCoreIn 2 B.Hhat).of_equiv (Subgroup.subgroupOfEquivOfLe hleH).symm
    exact A7V_le_pCoreIn_of_normal_isPGroup 2 B.H hleH hnorm hp
  · -- `O₂(H) ≤ O₂(Ĥ)`
    rw [← h26 B]
    have hWleH : Work.GW2.pCoreIn 2 B.H ≤ B.H := Subgroup.map_subtype_le _
    have hWn : ((Work.GW2.pCoreIn 2 B.H).subgroupOf B.H).Normal := by
      rw [Subgroup.normal_subgroupOf_iff hWleH]
      intro h k hh hk
      exact A7V_conj_mem_pCoreIn 2 B.H hk hh
    have hWp : IsPGroup 2 ((Work.GW2.pCoreIn 2 B.H).subgroupOf B.H) :=
      (A7V_isPGroup_pCoreIn 2 B.H).of_equiv (Subgroup.subgroupOfEquivOfLe hWleH).symm
    have hleS : Work.GW2.pCoreIn 2 B.H ≤ (B.S : Subgroup G) := by
      haveI := hWn
      have h := IsPGroup.le_sylow_of_normal hWp ((B.S).subtype B.S_le_H)
      intro x hx
      have h2 := h (Subgroup.mem_subgroupOf.mpr hx :
        (⟨x, hWleH hx⟩ : ↥B.H) ∈ (Work.GW2.pCoreIn 2 B.H).subgroupOf B.H)
      exact Subgroup.mem_subgroupOf.mp h2
    have hinfG : Work.GW2.pCoreIn 2 B.H ⊓ B.U = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
      have hodd : Odd (orderOf x) :=
        Odd.of_dvd_nat B.U_odd (Subgroup.orderOf_dvd_natCard B.U hx2)
      obtain ⟨n, hn⟩ := (A7V_isPGroup_pCoreIn 2 B.H).exists_card_eq
      have hdvd : orderOf x ∣ 2 ^ n := by
        rw [← hn]; exact Subgroup.orderOf_dvd_natCard _ hx1
      obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      have hk0 : k = 0 := by
        rcases Nat.eq_zero_or_pos k with h | h
        · exact h
        · exact absurd (hk' ▸ hodd) (Nat.not_odd_iff_even.mpr
            (even_iff_two_dvd.mpr (dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp h))))
      exact orderOf_eq_one_iff.mp (by rw [hk', hk0, pow_zero])
    have hleC : Work.GW2.pCoreIn 2 B.H ≤ Subgroup.centralizer (B.U : Set G) :=
      A7V_le_centralizer_of_normal_inf_eq_bot hWleH B.U_le_H hWn B.U_normal hinfG
    exact le_inf hleS hleC

/-- **LEAF C10.A2 `A7V`** (Bender p. 226): "`V := O₂(H∩M) = O₂(H) = O₂(Ĥ)` is of type (2,2),
whence `Ĥ/VU ≅ D₆` and `S` (having order 8) lies in `E`".

`A7VProp I` gives, from `Hyp9 G B C`, `IsA7Case C.D` and `A7Facts1 C.D`:

    A7Facts2 B C.D  =  IsFourGroup (pCoreIn 2 (B.H ⊓ C.D.M))   ∧
                       pCoreIn 2 B.Hhat = pCoreIn 2 (B.H ⊓ C.D.M)  ∧
                       (B.S : Subgroup G) ≤ layerIn C.D.M  ∧  |S| = 8  ∧
                       layerIn C.D.M ⊓ normalizer V ≤ B.Hhat   (V = O₂(H∩M)) -/
theorem A7V (I : Work.GW2.C4Inputs) : Work.GW2.A7VProp I := by
  intro G _ _ B C h hA hf
  have hHyp : Work.GW2.Hyp9 G B C := h
  obtain ⟨hbc, hc2, hplus, hseven, height⟩ := h
  have hft : Work.GW2.FeitThompsonProp := I.toolkit.ft
  have h26 := I.thm26 G hft hbc B
  have hSc : (B.S : Subgroup G) ⊓ Subgroup.centralizer (B.U : Set G) =
      Work.GW2.pCoreIn 2 B.Hhat := h26.2.1
  have hnotcyc : ¬ (Work.GW2.pCoreIn 2 B.Hhat ≤ B.S0) := A7VnotCyclic I G B C hHyp hA hf
  have key : Work.GW2.IsFourGroup (Work.GW2.pCoreIn 2 B.Hhat) ∧
      (Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U).relIndex B.Hhat = 6 := by
    rcases h26.2.2 with ⟨h1, _⟩ | ⟨hf4, hrel, _⟩
    · exact absurd h1 hnotcyc
    · exact ⟨hf4, hrel⟩
  -- the subgroup `V = O₂(Ĥ)`
  set V : Subgroup G := Work.GW2.pCoreIn 2 B.Hhat with hVdef
  have hVcard : Nat.card ↥V = 4 := key.1.1
  have hVleS : V ≤ (B.S : Subgroup G) := by rw [← hSc]; exact inf_le_left
  have hVleHhat : V ≤ B.Hhat := by rw [hVdef]; exact Subgroup.map_subtype_le _
  have hVne : V ≠ ⊥ := by
    intro hbot; rw [hbot] at hVcard; simp at hVcard
  have hVne_top : V ≠ ⊤ := fun htop =>
    B.Hhat_coatom.left (top_le_iff.mp (htop ▸ hVleHhat))
  have hUleHhat : B.U ≤ B.Hhat := h26.1 ▸ Subgroup.map_subtype_le _
  have hSuper : V ⊔ B.U ≤ B.Hhat := sup_le hVleHhat hUleHhat
  -- `V` is normalised by `Ĥ`
  have hVn : ∀ k ∈ B.Hhat, ∀ v ∈ V, k * v * k⁻¹ ∈ V := by
    intro k hk v hv
    rw [hVdef] at hv ⊢
    exact A7V_conj_mem_pCoreIn 2 B.Hhat hk hv
  have hUn : ∀ u ∈ B.U, ∀ k ∈ B.Hhat, k * u * k⁻¹ ∈ B.U := by
    intro u hu k hk
    rw [← h26.1] at hu ⊢
    obtain ⟨y, hy, rfl⟩ := hu
    exact ⟨⟨k, hk⟩ * y * ⟨k, hk⟩⁻¹, (Work.GW2.oddCore_normal ↥B.Hhat).conj_mem y hy ⟨k, hk⟩,
      by simp⟩
  -- `V` and `U` are each mapped to themselves by conjugation in `Ĥ`
  have hconjV : ∀ k ∈ B.Hhat, V.map (MulAut.conj k).toMonoidHom = V := by
    intro k hk
    apply le_antisymm
    · rintro x ⟨v, hv, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact hVn k hk v hv
    · intro x hx
      refine Subgroup.mem_map.mpr ⟨k⁻¹ * x * k, ?_, ?_⟩
      · simpa using hVn k⁻¹ (B.Hhat.inv_mem hk) x hx
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group
  have hconjU : ∀ k ∈ B.Hhat, B.U.map (MulAut.conj k).toMonoidHom = B.U := by
    intro k hk
    apply le_antisymm
    · rintro x ⟨v, hv, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact hUn v hv k hk
    · intro x hx
      refine Subgroup.mem_map.mpr ⟨k⁻¹ * x * k, ?_, ?_⟩
      · simpa using hUn x hx k⁻¹ (B.Hhat.inv_mem hk)
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group
  have hNnorm : ((V ⊔ B.U).subgroupOf B.Hhat).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hSuper]
    intro p k hp hk
    have hmap : (V ⊔ B.U).map (MulAut.conj k).toMonoidHom = V ⊔ B.U := by
      rw [Subgroup.map_sup, hconjV k hk, hconjU k hk]
    have hmem : (MulAut.conj k).toMonoidHom p ∈ (V ⊔ B.U).map (MulAut.conj k).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hp
    simp only [hmap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hmem
    exact hmem
  -- `(S ⊓ (V ⊔ U)).relIndex S` divides `6`
  have hdvd6 : ((B.S : Subgroup G) ⊓ (V ⊔ B.U)).relIndex (B.S : Subgroup G) ∣ 6 := by
    haveI : ((V ⊔ B.U).subgroupOf B.Hhat).Normal := hNnorm
    have hdvd : ((V ⊔ B.U).subgroupOf B.Hhat).relIndex ((B.S : Subgroup G).subgroupOf B.Hhat) ∣
        ((V ⊔ B.U).subgroupOf B.Hhat).index :=
      Subgroup.relIndex_dvd_index_of_normal _ _
    have hidx : ((V ⊔ B.U).subgroupOf B.Hhat).index = 6 := key.2
    rw [Subgroup.relIndex_subgroupOf B.S_le_Hhat, hidx,
      ← Subgroup.inf_relIndex_left (B.S : Subgroup G) (V ⊔ B.U)] at hdvd
    exact hdvd
  -- `S ⊓ (V ⊔ U) = V`
  have hSnN : (B.S : Subgroup G) ⊓ (V ⊔ B.U) = V := by
    have hUnorm : (B.U.subgroupOf B.Hhat).Normal :=
      (Subgroup.normal_subgroupOf_iff hUleHhat).mpr (fun u k hu hk => hUn u hu k hk)
    have hsupSub : (V ⊔ B.U).subgroupOf B.Hhat =
        (V.subgroupOf B.Hhat) ⊔ (B.U.subgroupOf B.Hhat) := by
      apply Subgroup.map_injective (f := (B.Hhat).subtype) ((B.Hhat).subtype_injective)
      rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
        Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hVleHhat,
        inf_eq_left.mpr hUleHhat, inf_eq_left.mpr hSuper]
    apply le_antisymm
    · intro x hx
      obtain ⟨hxS, hxN⟩ := Subgroup.mem_inf.mp hx
      have hxH : x ∈ B.Hhat := hSuper hxN
      have hx' : (⟨x, hxH⟩ : ↥B.Hhat) ∈ ((V ⊔ B.U).subgroupOf B.Hhat) :=
        Subgroup.mem_subgroupOf.mpr hxN
      rw [hsupSub] at hx'
      haveI := hUnorm
      rw [Subgroup.mem_sup_of_normal_right] at hx'
      obtain ⟨v', hv', u', hu', hvu⟩ := hx'
      have hv : (v' : G) ∈ V := Subgroup.mem_subgroupOf.mp hv'
      have hu : (u' : G) ∈ B.U := Subgroup.mem_subgroupOf.mp hu'
      have hvx : (v' : G) * (u' : G) = x := by
        have := congrArg (fun z : ↥B.Hhat => (z : G)) hvu
        simpa using this
      have huS : (u' : G) ∈ (B.S : Subgroup G) := by
        have : (u' : G) = (v' : G)⁻¹ * x := by rw [← hvx]; group
        rw [this]
        exact (B.S).mul_mem ((B.S).inv_mem (hVleS hv)) hxS
      have hu_bot : (u' : G) ∈ (⊥ : Subgroup G) := by
        have : (u' : G) ∈ B.U ⊓ (B.S : Subgroup G) := ⟨hu, huS⟩
        rwa [B.U_inf_S] at this
      have hu1 : (u' : G) = 1 := Subgroup.mem_bot.mp hu_bot
      have hvx' : (v' : G) = x := by
        rw [hu1, mul_one] at hvx
        exact hvx
      rw [← hvx']; exact hv
    · exact le_inf hVleS le_sup_left
  -- `|S| = 8`
  have hIS : IsPGroup 2 (B.S : Subgroup G) := (B.S).isPGroup'
  have hcardS : Nat.card (B.S : Subgroup G) = 8 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := hIS.exists_card_eq
    have hcard : Nat.card (B.S : Subgroup G) =
        ((B.S : Subgroup G) ⊓ (V ⊔ B.U)).relIndex (B.S : Subgroup G) * 4 := by
      have hcardN : Nat.card ↥((B.S : Subgroup G) ⊓ (V ⊔ B.U)) = 4 := by rw [hSnN, hVcard]
      have h := Subgroup.relIndex_mul_card ((B.S : Subgroup G) ⊓ (V ⊔ B.U)) (B.S : Subgroup G)
      rw [inf_eq_left.mpr inf_le_left, hcardN] at h
      exact h.symm
    have hd2 : ((B.S : Subgroup G) ⊓ (V ⊔ B.U)).relIndex (B.S : Subgroup G) ∣ 2 := by
      have h3d : ¬ 3 ∣ ((B.S : Subgroup G) ⊓ (V ⊔ B.U)).relIndex (B.S : Subgroup G) := by
        intro h3
        have h3S : 3 ∣ Nat.card (B.S : Subgroup G) := by
          rw [hcard]; exact dvd_mul_of_dvd_left h3 4
        rw [hn] at h3S
        exact absurd (Nat.prime_three.dvd_of_dvd_pow h3S) (by norm_num)
      exact Nat.Coprime.dvd_of_dvd_mul_right
        (Nat.prime_three.coprime_iff_not_dvd.mpr h3d).symm (by simpa using hdvd6)
    have hle8 : Nat.card (B.S : Subgroup G) ≤ 8 := by
      rw [hcard]
      have := Nat.le_of_dvd (by norm_num : 0 < 2) hd2
      omega
    have hge8 : 8 ≤ Nat.card (B.S : Subgroup G) := by
      have h8 : Nat.card ↥((B.S : Subgroup G) ⊓ Work.GW2.layerIn C.D.M) = 8 :=
        A7Vsylow G B C hHyp hA hf
      have hdiv := Subgroup.card_dvd_of_le
        (inf_le_left : (B.S : Subgroup G) ⊓ Work.GW2.layerIn C.D.M ≤ (B.S : Subgroup G))
      rw [h8] at hdiv
      exact Nat.le_of_dvd Nat.card_pos hdiv
    omega
  -- `S ≤ E`
  have hSleE : (B.S : Subgroup G) ≤ Work.GW2.layerIn C.D.M := by
    have h8 : Nat.card ↥((B.S : Subgroup G) ⊓ Work.GW2.layerIn C.D.M) = 8 :=
      A7Vsylow G B C hHyp hA hf
    have hSeq : (B.S : Subgroup G) ⊓ Work.GW2.layerIn C.D.M = (B.S : Subgroup G) :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h8, hcardS])
    intro x hx
    have : x ∈ (B.S : Subgroup G) ⊓ Work.GW2.layerIn C.D.M := by rw [hSeq]; exact hx
    exact (Subgroup.mem_inf.mp this).2
  -- conjunct 2
  have hconj2 : Work.GW2.pCoreIn 2 B.Hhat = Work.GW2.pCoreIn 2 (B.H ⊓ C.D.M) :=
    (A7V_pCoreIn_Hhat_eq_pCoreIn_H (fun B => (I.thm26 G hft hbc B).2.1) B).trans hseven.1.symm
  -- the normalizer statement
  have hconj5 :
      Work.GW2.layerIn C.D.M ⊓ Subgroup.normalizer
        ((Work.GW2.pCoreIn 2 (B.H ⊓ C.D.M) : Subgroup G) : Set G) ≤ B.Hhat := by
    have hnormalizer_eq : Subgroup.normalizer (V : Set G) = B.Hhat := by
      have hHleN : B.Hhat ≤ Subgroup.normalizer (V : Set G) := by
        rw [Subgroup.le_normalizer_iff]
        intro p hp v hv
        exact hVn p hp v hv
      have hNne_top : Subgroup.normalizer (V : Set G) ≠ ⊤ := by
        intro htop
        haveI hVnorm : V.Normal := Subgroup.normalizer_eq_top_iff.mp htop
        rcases hbc.simple.eq_bot_or_eq_top_of_normal V with hb | ht
        · exact hVne hb
        · exact hVne_top ht
      rcases lt_or_eq_of_le hHleN with hlt | heq
      · exact absurd (B.Hhat_coatom.lt_iff.mp hlt) hNne_top
      · exact heq.symm
    rw [← hconj2, ← hVdef, hnormalizer_eq]
    exact inf_le_right
  exact ⟨by rw [← hconj2, ← hVdef]; exact key.1, hconj2, hSleE, hcardS, hconj5⟩

end Work.CORE4
