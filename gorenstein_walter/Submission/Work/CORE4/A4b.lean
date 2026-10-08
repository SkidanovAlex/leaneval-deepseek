import Mathlib
import Submission.Work.CORE4.Defs10
import Submission.Work.CORE4.NotA7Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.DihOrCycSub
import Submission.Work.CORE4.LayerCtx6
import Submission.Work.CORE4.A7K
import Submission.Work.CORE4.A7V
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.A7KBound.K_le_layerIn_and_inf_center
import Submission.Work.CORE4.A4bAux.center_quot_commute
import Submission.Work.CORE4.A4bAux.map_conjSub
import Submission.Work.CORE4.A4bAux.card_map_quot
import Submission.Work.CORE4.A4bAux.normalizer_sup_of_central
import Submission.Work.CORE4.A4bAux.inverts_conjSub
import Submission.Work.CORE4.A4bAux.mem_normalizer_subgroupOf
import Submission.Work.CORE4.A4bAux.conjSub_subgroupOf
import Submission.Work.CORE4.A4bAux.le_centralizer_map

namespace Work.CORE4

/-- **A4b (lift of A4s to `E = E(M)`, `E/Z(E) ≅ A₇`), design pass 15.**  There is `e ∈ E` with
`e s = s e`, `K^e ≤ Ĥ`, `K^e ≠ K`, and `s` inverts `K^e`.

Statement copied verbatim from `_design_gw/Core15C4.lean` / `NotA7Defs.lean`
(`Work.CORE4.C15.A4bProp`): from `A7S4ConjProp` (the leaf `CORE4/A4s`), `Hyp9 G B C`,
`IsA7Case C.D`, `A7Facts1 C.D`, `A7Facts2 B C.D` and `A7UData B C.D`:

    ∃ e ∈ layerIn C.D.M, e * C.D.s = C.D.s * e ∧ conjSub e C.D.K ≤ B.Hhat ∧
      conjSub e C.D.K ≠ C.D.K ∧ Inverts C.D.s (conjSub e C.D.K)

Route (design pass 15 §1.3, A4b):
* apply A4s in `Ē = E/Z(E)` to `V̄, s̄, K̄`.  The hypotheses hold there: `V ∩ Z(E) = K ∩ Z(E) = 1`
  (`Z(E) ≤ O(M) = F` is odd and centralized by `s`; `K ∩ F ≤ K ∩ B₀ = 1`); `K ≤ U ≤ C(V)`
  (`U, V ⊴ Ĥ` of coprime orders, `I.thm26`); `s ∈ S ≤ Ĥ`;
* lift `ē` to `e ∈ E`.  `s^e ∈ s·Z(E)` and both are involutions with `Z(E)` central of odd order
  (the proved `LayerCtx6` gives `Odd |Z(E)|`), so `s^e = s`; hence `s` inverts `K^e`;
* the preimage of `N_Ē(V̄)` is `N_E(V·Z(E)) = N_E(V)` (`V` is the Sylow 2-subgroup of `V × Z(E)`),
  so `K^e ≤ N_E(V) ≤ Ĥ` (`A7Facts2`, last conjunct);
* `K̄^ē ≠ K̄` gives `K^e ≠ K`. -/
theorem A4b (I : Work.GW2.C4Inputs) : Work.CORE4.C15.A4bProp I := by
  intro hA4s G _ _ B C h9 hA f1 f2 hU
  obtain ⟨hbc, hcase2, hplus, hseven, height⟩ := h9
  obtain ⟨hKcard, hFcard, hK0K, hpiFU⟩ := f1
  obtain ⟨hVfour, hVeq, hSleE, hScard, hNnorm⟩ := f2
  set E : Subgroup G := Work.GW2.layerIn C.D.M with hEdef
  set V : Subgroup G := Work.GW2.pCoreIn 2 B.Hhat with hVdef
  set Z : Subgroup ↥E := Subgroup.center ↥E with hZdef
  set Q : Type := ↥E ⧸ Z with hQdef
  set π : ↥E →* Q := QuotientGroup.mk' Z with hπdef
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite ↥E := inferInstance
  haveI : Finite Q := inferInstance
  have hft : Work.GW2.FeitThompsonProp := I.toolkit.ft
  have h26 := I.thm26 G hft hbc B
  have hZodd : Odd (Nat.card ↥Z) := by
    rw [hZdef]
    exact (LayerCtx6 I hbc C (DihOrCycSub hbc.sylow C.D.M)).2.1
  have hVfourV : Work.GW2.IsFourGroup V := by
    rw [hVeq]; exact hVfour
  have hVleS : V ≤ (B.S : Subgroup G) := by
    rw [hVdef]
    rw [← h26.2.1]
    exact inf_le_left
  have hVE : V ≤ E := le_trans hVleS hSleE
  have hKE : C.D.K ≤ E :=
    (A7KBound.K_le_layerIn_and_inf_center hplus (Work.GW2.BenderSetup.U_odd B)).1
  have hsE : C.D.s ∈ E := Work.GW2.Case2Data.s_mem_layer B C.D
  set VH : Subgroup ↥E := V.subgroupOf E with hVHdef
  set KH : Subgroup ↥E := C.D.K.subgroupOf E with hKHdef
  set sH : ↥E := ⟨C.D.s, hsE⟩ with hsHdef
  -- `|V ∩ Z(E)| = 1` and `|K ∩ Z(E)| = 1`
  have hcardVH : Nat.card ↥VH = 4 := by
    have h1 : Nat.card ↥(V.subgroupOf E) = Nat.card ↥V :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVE).toEquiv
    rw [hVHdef, h1, hVfourV.1]
  have hVHZ : VH ⊓ Z = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hxV, hxZ⟩ := Subgroup.mem_inf.mp hx
    have h1 : orderOf x ∣ 2 ^ 2 := by
      have h : (2 : ℕ) ^ 2 = Nat.card ↥VH := by rw [hcardVH]; norm_num
      rw [h]
      exact Subgroup.orderOf_dvd_natCard _ hxV
    have h2 : Odd (orderOf x) := Odd.of_dvd_nat hZodd (Subgroup.orderOf_dvd_natCard _ hxZ)
    obtain ⟨k, hk, hkx⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
    have hk0 : k = 0 := by
      rcases Nat.eq_zero_or_pos k with h | h
      · exact h
      · exact absurd (hkx ▸ h2) (Nat.not_odd_iff_even.mpr
          (even_iff_two_dvd.mpr (dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp h))))
    have h3 : orderOf x = 1 := by rw [hkx, hk0, pow_zero]
    exact orderOf_eq_one_iff.mp h3
  have hKHZ : KH ⊓ Z = ⊥ := by
    have hKinf : C.D.K ⊓ Z.map E.subtype = ⊥ :=
      (A7KBound.K_le_layerIn_and_inf_center hplus (Work.GW2.BenderSetup.U_odd B)).2
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hxKH, hxZ⟩ := Subgroup.mem_inf.mp hx
    have hxK : (x : G) ∈ C.D.K :=
      Subgroup.mem_subgroupOf.mp (by rw [← hKHdef]; exact hxKH)
    have hxZG : (x : G) ∈ Z.map E.subtype := Subgroup.mem_map.mpr ⟨x, hxZ, rfl⟩
    have hbot : (x : G) ∈ (⊥ : Subgroup G) := by
      rw [← hKinf]
      exact Subgroup.mem_inf.mpr ⟨hxK, hxZG⟩
    exact Subtype.ext (Subgroup.mem_bot.mp hbot)
  -- `s`
  have hsHhat : C.D.s ∈ B.Hhat :=
    Work.GW2.BenderSetup.S_le_Hhat B (Work.GW2.Case2Data.s_mem_S B C.D)
  have hsHord : orderOf sH = 2 := by
    rw [← Subgroup.orderOf_coe sH]
    exact C.D.s_order
  have hsHpow : sH ^ 2 = 1 := by
    rw [← hsHord]
    exact pow_orderOf_eq_one sH
  have hsH2 : sH * sH = 1 := by rw [← pow_two]; exact hsHpow
  -- `V̄`, `K̄`, `s̄`
  set Vbar : Subgroup Q := VH.map π with hVbardef
  set Kbar : Subgroup Q := KH.map π with hKbardef
  set sbar : Q := π sH with hsbardef
  have hVbarFour : Work.GW2.IsFourGroup Vbar := by
    refine ⟨?_, ?_⟩
    · rw [hVbardef, A4bAux.card_map_quot Z hVHZ, hcardVH]
    · intro v hv
      rw [hVbardef] at hv
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hv
      have hxV : (x : G) ∈ V := Subgroup.mem_subgroupOf.mp (by rw [← hVHdef]; exact hx)
      have hx2 : x ^ 2 = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        exact hVfourV.2 (x : G) hxV
      rw [← map_pow, hx2, map_one]
  have hsNV : C.D.s ∈ Subgroup.normalizer (V : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hle : V.map (MulAut.conj C.D.s).toMonoidHom ≤ V := by
      rintro x ⟨v, hv, rfl⟩
      change C.D.s * v * C.D.s⁻¹ ∈ V
      rw [hVdef] at hv ⊢
      exact A7V_conj_mem_pCoreIn 2 B.Hhat hsHhat hv
    have hcard : Nat.card ↥(V.map (MulAut.conj C.D.s).toMonoidHom) = Nat.card ↥V :=
      Subgroup.card_map_of_injective (MulAut.conj C.D.s).injective
    exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)
  have hsHN : sH ∈ Subgroup.normalizer (VH : Set ↥E) := by
    rw [hVHdef]
    exact (A4bAux.mem_normalizer_subgroupOf hVE sH).mpr hsNV
  have hsbarN : sbar ∈ Subgroup.normalizer (Vbar : Set Q) := by
    rw [hsbardef, hVbardef]
    exact Subgroup.le_normalizer_map π (Subgroup.mem_map_of_mem π hsHN)
  have hsbar2 : sbar ^ 2 = 1 := by
    rw [hsbardef, ← map_pow, hsHpow, map_one]
  have hsbar_ne : sbar ≠ 1 := by
    intro h1
    have hsZ : sH ∈ Z := by
      rw [hsbardef, hπdef] at h1
      rw [← QuotientGroup.ker_mk' Z, MonoidHom.mem_ker]
      exact h1
    have hdvd : orderOf sH ∣ Nat.card ↥Z := Subgroup.orderOf_dvd_natCard Z hsZ
    rw [hsHord] at hdvd
    exact (Nat.not_even_iff_odd.mpr hZodd) (even_iff_two_dvd.mpr hdvd)
  have hsbarOrd : orderOf sbar = 2 := orderOf_eq_prime hsbar2 hsbar_ne
  -- `K̄ ≤ C(V̄)`
  have hUleHhat : B.U ≤ B.Hhat := h26.1 ▸ Subgroup.map_subtype_le _
  have hVleHhat : V ≤ B.Hhat := by rw [hVdef]; exact Subgroup.map_subtype_le _
  have hUn : ∀ (u k : G), u ∈ B.U → k ∈ B.Hhat → k * u * k⁻¹ ∈ B.U := by
    intro u k hu hk
    rw [← h26.1] at hu ⊢
    obtain ⟨y, hy, rfl⟩ := hu
    exact ⟨⟨k, hk⟩ * y * ⟨k, hk⟩⁻¹,
      (Work.GW2.oddCore_normal ↥B.Hhat).conj_mem y hy ⟨k, hk⟩, by simp⟩
  have hVn : ∀ (v k : G), v ∈ V → k ∈ B.Hhat → k * v * k⁻¹ ∈ V := by
    intro v k hv hk
    rw [hVdef] at hv ⊢
    exact A7V_conj_mem_pCoreIn 2 B.Hhat hk hv
  have hinfUV : B.U ⊓ V = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
    have hodd1 : Odd (orderOf x) :=
      Odd.of_dvd_nat (Work.GW2.BenderSetup.U_odd B) (Subgroup.orderOf_dvd_natCard B.U hx1)
    obtain ⟨m, hm⟩ := (A7V_isPGroup_pCoreIn 2 B.Hhat).exists_card_eq
    have hdvd : orderOf x ∣ 2 ^ m := by
      rw [← hm]
      exact Subgroup.orderOf_dvd_natCard _ (hVdef ▸ hx2)
    obtain ⟨k, hk, hkx⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have hk0 : k = 0 := by
      rcases Nat.eq_zero_or_pos k with h | h
      · exact h
      · exact absurd (hkx ▸ hodd1) (Nat.not_odd_iff_even.mpr
          (even_iff_two_dvd.mpr (dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp h))))
    exact orderOf_eq_one_iff.mp (by rw [hkx, hk0, pow_zero])
  have hUleCV : B.U ≤ Subgroup.centralizer (V : Set G) :=
    A7V_le_centralizer_of_normal_inf_eq_bot (H := B.Hhat) (A := B.U) (Bc := V)
      hUleHhat hVleHhat ((Subgroup.normal_subgroupOf_iff hUleHhat).mpr hUn)
      ((Subgroup.normal_subgroupOf_iff hVleHhat).mpr hVn) hinfUV
  have hKV : C.D.K ≤ Subgroup.centralizer (V : Set G) :=
    le_trans (Work.GW2.Case2Data.K_le_U B C.D) hUleCV
  have hKHcent : KH ≤ Subgroup.centralizer (VH : Set ↥E) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    apply Subtype.ext
    have hxK : (x : G) ∈ C.D.K := Subgroup.mem_subgroupOf.mp (by rw [← hKHdef]; exact hx)
    have hyV : (y : G) ∈ V := Subgroup.mem_subgroupOf.mp (by rw [← hVHdef]; exact hy)
    have hc := Subgroup.mem_centralizer_iff.mp (hKV hxK) (y : G) hyV
    simpa [Subgroup.coe_mul] using hc
  have hKbarCent : Kbar ≤ Subgroup.centralizer (Vbar : Set Q) := by
    rw [hKbardef, hVbardef]
    exact A4bAux.le_centralizer_map π hKHcent
  -- `|K̄| = 3` and `Inverts s̄ K̄`
  have hKHcard : Nat.card ↥KH = 3 := by
    rw [hKHdef,
      show Nat.card ↥(C.D.K.subgroupOf E) = Nat.card ↥C.D.K from
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKE).toEquiv, hKcard]
  have hKbarCard : Nat.card ↥Kbar = 3 := by
    rw [hKbardef, A4bAux.card_map_quot Z hKHZ, hKHcard]
  have hKHinv : Work.GW2.Inverts sH KH := by
    intro x hx
    apply Subtype.ext
    have hxK : (x : G) ∈ C.D.K := Subgroup.mem_subgroupOf.mp (by rw [← hKHdef]; exact hx)
    have hx := Work.GW2.Case2Data.K_inv B C.D x hxK
    simpa [Subgroup.coe_mul, Subgroup.coe_inv] using hx
  have hKbarInv : Work.GW2.Inverts sbar Kbar := by
    intro y hy
    rw [hKbardef] at hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    have hx' := hKHinv x hx
    rw [hsbardef, hπdef]
    calc (QuotientGroup.mk' Z) sH * (QuotientGroup.mk' Z) x * ((QuotientGroup.mk' Z) sH)⁻¹
        = (QuotientGroup.mk' Z) (sH * x * sH⁻¹) := by rw [map_mul, map_mul, map_inv]
      _ = (QuotientGroup.mk' Z) (x⁻¹) := by rw [hx']
      _ = ((QuotientGroup.mk' Z) x)⁻¹ := by rw [map_inv]
  -- apply `A4s` in `Q = E/Z(E)`
  obtain ⟨eiso⟩ := hA
  obtain ⟨eQ, heQcomm, heQN, heQne⟩ :=
    hA4s Q (⟨eiso⟩ : Nonempty (Q ≃* alternatingGroup (Fin 7)))
      Vbar hVbarFour sbar hsbarN hsbarOrd Kbar hKbarCent hKbarCard hKbarInv
  obtain ⟨eH, heH⟩ := QuotientGroup.mk'_surjective Z eQ
  -- translate the `A4s` conclusion back to `E ≤ G`
  have hconj_le : Work.GW2.conjSub (eH : G) C.D.K ≤ E := by
    intro x hx
    rw [Work.GW2.conjSub] at hx
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hx
    change (eH : G) * k * (eH : G)⁻¹ ∈ E
    exact E.mul_mem (E.mul_mem eH.2 (hKE hk)) (E.inv_mem eH.2)
  have hKH' : Work.GW2.conjSub eH KH = (Work.GW2.conjSub (eH : G) C.D.K).subgroupOf E := by
    rw [hKHdef]
    exact A4bAux.conjSub_subgroupOf hKE eH.2
  have hmap : (Work.GW2.conjSub eH KH).map π = Work.GW2.conjSub eQ Kbar := by
    rw [A4bAux.map_conjSub π eH KH, hπdef, heH, hKbardef]
  have hA2 : IsPGroup 2 VH := IsPGroup.of_card (n := 2) (by rw [hcardVH]; norm_num)
  have hle1 : Work.GW2.conjSub eH KH ≤ Subgroup.normalizer (VH : Set ↥E) := by
    have h1 : (Work.GW2.conjSub eH KH).map π ≤ Subgroup.normalizer (Vbar : Set Q) := by
      rw [hmap]; exact heQN
    have h2 : Work.GW2.conjSub eH KH ≤ (Subgroup.normalizer (Vbar : Set Q)).comap π :=
      Subgroup.map_le_iff_le_comap.mp h1
    have h3 : (Subgroup.normalizer (Vbar : Set Q)).comap π =
        Subgroup.normalizer ((Vbar.comap π : Subgroup ↥E) : Set ↥E) :=
      Subgroup.comap_normalizer_eq_of_surjective Vbar (QuotientGroup.mk'_surjective Z)
    rw [h3] at h2
    have h4 : Vbar.comap π = VH ⊔ Z := by
      rw [hVbardef, hVHdef, hπdef, Subgroup.comap_map_eq, QuotientGroup.ker_mk']
    rw [h4] at h2
    exact le_trans h2 (A4bAux.normalizer_sup_of_central le_rfl hVHZ hA2 hZodd)
  have hNnormV : E ⊓ Subgroup.normalizer (V : Set G) ≤ B.Hhat := by
    rw [hVeq]
    exact hNnorm
  have hKhat : Work.GW2.conjSub (eH : G) C.D.K ≤ B.Hhat := by
    refine le_trans (le_inf hconj_le ?_) hNnormV
    intro x hx
    have hx' : (⟨x, hconj_le hx⟩ : ↥E) ∈ Work.GW2.conjSub eH KH := by
      rw [hKH']
      exact Subgroup.mem_subgroupOf.mpr hx
    have := hle1 hx'
    exact (A4bAux.mem_normalizer_subgroupOf hVE ⟨x, hconj_le hx⟩).mp this
  have hcommG : (eH : G) * C.D.s = C.D.s * (eH : G) := by
    have hq : π eH * π sH = π sH * π eH := by
      rw [hπdef, heH, ← hsbardef]
      exact heQcomm
    have hHE : eH * sH = sH * eH := A4bAux.center_quot_commute hZodd hsH2 hq
    have := congrArg (fun w : ↥E => (w : G)) hHE
    simpa [Subgroup.coe_mul] using this
  refine ⟨(eH : G), eH.2, hcommG, hKhat, ?_, ?_⟩
  · intro hK
    have h2 : (Work.GW2.conjSub eH KH).map π = Kbar := by
      rw [hKH', hK, hKbardef]
    exact heQne (hmap.symm.trans h2)
  · exact A4bAux.inverts_conjSub hcommG (Work.GW2.Case2Data.K_inv B C.D)

end Work.CORE4
