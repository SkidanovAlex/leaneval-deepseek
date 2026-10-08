import Mathlib
import Submission.Work.ThompsonFrobenius.GTDefs
import Submission.Work.ThompsonFrobenius.pCore_ne_bot
import Submission.Work.ThompsonFrobenius.pCore_lt
import Submission.Work.ThompsonFrobenius.pPrimeCore_eq_bot
import Submission.Work.ThompsonFrobenius.npc_quotient
import Submission.Work.HallHigman.ModRep
import Submission.Work.NPC.All
import Submission.Work.NPC.Frobenius.exists_sylow_subgroupOf_inf

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# GT-4: `C_G(O_p(G)) ≤ O_p(G)` (area `ThompsonFrobenius`)

Step GT-4 of `NOTES_LEAD_bs_thompson.md` (Farris §3.4).  Let `G` be the minimal counterexample,
`H = O_p(G)`, `C = C_G(H)`, and let `K` be the preimage of the normal `p`-complement `M̄ = K/H` of
`G/H` provided by GT-3, so `K ⊴ G` with `|K/H|` coprime to `p`.

* `C₁ := C ⊓ K ⊴ G`, and `C₁ ⊓ H` is a Sylow `p`-subgroup of `C₁`
  (`|C₁ : C₁ ⊓ H| = [C₁ ⊔ H : H] ∣ [K : H] = |K/H|` is coprime to `p`); it is central in `C₁`
  because `C₁ ≤ C_G(H)`.
* Burnside's normal `p`-complement theorem (`Work.NPC.burnside_npc`) applied inside `↥C₁` gives a
  normal `p`-complement `R` of `C₁`; `R` is characteristic in `C₁` (uniqueness of normal
  `p`-complements), hence normal in `G`.
* `|R|` is coprime to `p`, so `R ≤ O_{p'}(G) = 1` by GT-2 (`pPrimeCore_eq_bot`); thus `R = 1` and
  `C₁` is a `p`-group, whence `C₁ ≤ O_p(G) = H`.
* Finally `C/(C ⊓ K)` is a subgroup of the `p`-group `G/K`, and `C ⊓ K ≤ H` is a `p`-group, so `C`
  is a `p`-group; being normal it lies in `O_p(G) = H`.
-/

set_option autoImplicit false

open scoped Pointwise

namespace Work.ThompsonFrobenius

theorem centralizer_pCore_le {p : ℕ} {G : Type} [Group G] [Finite G] {P : Sylow p G}
    (h : GTMinimal p G P) :
    Subgroup.centralizer (Work.HallHigman.pCore p G : Set G) ≤ Work.HallHigman.pCore p G := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  let H : Subgroup G := Work.HallHigman.pCore p G
  haveI hHnormal : H.Normal := inferInstance
  have hHpg : IsPGroup p H := Work.HallHigman.isPGroup_pCore
  -- the normal `p`-complement of `G/H` and its preimage `K`
  obtain ⟨Mbar, hMbar⟩ := npc_quotient h
  haveI hMbarNormal : Mbar.Normal := hMbar.normal
  let K : Subgroup G := Mbar.comap (QuotientGroup.mk' H)
  haveI hKnormal : K.Normal := Subgroup.normal_comap _
  have hHK : H ≤ K := by
    intro x hx
    show (QuotientGroup.mk' H) x ∈ Mbar
    have h1 : (QuotientGroup.mk' H) x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    simpa [h1] using Mbar.one_mem
  have hKmap : Subgroup.map (QuotientGroup.mk' H) K = Mbar := by
    show Subgroup.map (QuotientGroup.mk' H) (Mbar.comap (QuotientGroup.mk' H)) = Mbar
    rw [Subgroup.map_comap_eq, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective H),
      top_inf_eq]
  -- `[K : H] = |K/H| = |M̄|` is coprime to `p`
  have hrelK : H.relIndex K = Nat.card ↥Mbar := by
    have hφ : H.subgroupOf K = ((QuotientGroup.mk' H).comp K.subtype).ker := by
      rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
      rfl
    have hrange : ((QuotientGroup.mk' H).comp K.subtype).range = Mbar := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype, hKmap]
    calc H.relIndex K = (H.subgroupOf K).index := rfl
      _ = Nat.card (↥K ⧸ H.subgroupOf K) := Subgroup.index_eq_card _
      _ = Nat.card (↥K ⧸ ((QuotientGroup.mk' H).comp K.subtype).ker) := by rw [hφ]
      _ = Nat.card ↥((QuotientGroup.mk' H).comp K.subtype).range :=
            Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv
      _ = Nat.card ↥Mbar := by rw [hrange]
  have hcop_relK : ¬ p ∣ H.relIndex K := by
    rw [hrelK]
    exact fun hd => h.prime.ne_one ((hMbar.coprime_card.symm).eq_one_of_dvd hd)
  -- `C` and `C₁`
  let C : Subgroup G := Subgroup.centralizer (H : Set G)
  haveI hCnormal : C.Normal := inferInstance
  let C₁ : Subgroup G := C ⊓ K
  haveI hC₁normal : C₁.Normal := inferInstance
  have hC₁leK : C₁ ≤ K := inf_le_right
  have hC₁leC : C₁ ≤ C := inf_le_left
  have hC₁sup_le_K : C₁ ⊔ H ≤ K := sup_le hC₁leK hHK
  -- `C₁ ⊓ H` is a Sylow `p`-subgroup of `C₁`
  have hidx : ¬ p ∣ ((C₁ ⊓ H).subgroupOf C₁).index := by
    have h1 : (C₁ ⊓ H).relIndex C₁ = H.relIndex (C₁ ⊔ H) :=
      Work.NPC.Frobenius.relIndex_inf_eq_relIndex_sup_of_normal C₁ H
    have h2 : H.relIndex (C₁ ⊔ H) ∣ H.relIndex K := by
      refine ⟨(C₁ ⊔ H).relIndex K, ?_⟩
      exact (Subgroup.relIndex_mul_relIndex H (C₁ ⊔ H) K le_sup_right hC₁sup_le_K).symm
    intro hdvd
    rw [show ((C₁ ⊓ H).subgroupOf C₁).index = (C₁ ⊓ H).relIndex C₁ from rfl, h1] at hdvd
    exact hcop_relK (hdvd.trans h2)
  have hHpC₁ : IsPGroup p ((C₁ ⊓ H).subgroupOf C₁) := hHpg.to_inf_right.comap_subtype
  let S : Sylow p ↥C₁ := hHpC₁.toSylow hidx
  have hcent : Subgroup.normalizer (S : Set ↥C₁) ≤ Subgroup.centralizer (S : Set ↥C₁) := by
    intro x _hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    refine Subtype.ext ?_
    have hyH : (y : G) ∈ H := hy.2
    exact Subgroup.mem_centralizer_iff.mp x.2.1 (y : G) hyH
  -- Burnside inside `↥C₁`
  obtain ⟨R, hR⟩ := Work.NPC.burnside_npc S hcent
  haveI hRchar : R.Characteristic := by
    rw [Subgroup.characteristic_iff_map_eq]
    intro φ
    exact (Work.NPC.Basic.isNormalPComplement_unique hR
      (Work.NPC.Frobenius.isNormalPComplement_map_mulEquiv hR φ)).symm
  haveI hRnorm : (R.map C₁.subtype).Normal := inferInstance
  have hRcop : (Nat.card ↥(R.map C₁.subtype)).Coprime p := by
    rw [Subgroup.card_map_of_injective C₁.subtype_injective]
    exact hR.coprime_card
  have hRle : R.map C₁.subtype ≤ Submission.Blueprint.pPrimeCore p G :=
    le_sSup ⟨hRnorm, hRcop⟩
  have hRbot : R = ⊥ := by
    have h1 : R.map C₁.subtype = ⊥ :=
      le_bot_iff.mp (hRle.trans (le_of_eq (pPrimeCore_eq_bot h)))
    have h2 : R ≤ C₁.subtype.ker := (Subgroup.map_eq_bot_iff R).mp h1
    exact le_bot_iff.mp
      (h2.trans (le_of_eq ((MonoidHom.ker_eq_bot_iff _).mpr C₁.subtype_injective)))
  -- `C₁` is a `p`-group, hence lies in `O_p(G)`
  have hC₁pg : IsPGroup p ↥C₁ := by
    rw [hRbot] at hR
    exact IsPGroup.of_equiv hR.isPGroup_quotient (QuotientGroup.quotientBot)
  have hC₁leH : C₁ ≤ H := Work.HallHigman.le_pCore_of_isPGroup hC₁normal hC₁pg
  -- `C` is a `p`-group
  have hCpg : IsPGroup p ↥C := by
    let φ : ↥C →* G ⧸ K := (QuotientGroup.mk' K).comp C.subtype
    have hker : φ.ker = (C ⊓ K).subgroupOf C := by
      have h1 : φ.ker = K.subgroupOf C := by
        rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
        rfl
      rw [h1, Subgroup.inf_subgroupOf_left]
    have hkerpg : IsPGroup p φ.ker := by
      rw [hker]
      exact (IsPGroup.to_le hHpg (show C ⊓ K ≤ H from hC₁leH)).comap_subtype
    have hGK : IsPGroup p (G ⧸ K) := by
      have hiso : (G ⧸ H) ⧸ Mbar ≃* G ⧸ K :=
        (QuotientGroup.quotientMulEquivOfEq hKmap).symm.trans
          (QuotientGroup.quotientQuotientEquivQuotient H K hHK)
      exact IsPGroup.of_equiv hMbar.isPGroup_quotient hiso
    have htop : IsPGroup p (⊤ : Subgroup (G ⧸ K)) :=
      IsPGroup.of_equiv hGK (Subgroup.topEquiv (G := G ⧸ K)).symm
    have h2 : IsPGroup p (⊤ : Subgroup ↥C) :=
      IsPGroup.comap_of_ker_isPGroup htop φ hkerpg
    exact IsPGroup.of_equiv h2 (Subgroup.topEquiv (G := ↥C))
  exact Work.HallHigman.le_pCore_of_isPGroup hCnormal hCpg

end Work.ThompsonFrobenius
