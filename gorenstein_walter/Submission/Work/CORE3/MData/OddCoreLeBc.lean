import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE3.MDataAux
import Submission.Work.CORE3.H_eq_U_sup_S
import Submission.Work.CORE2A.exists_mul_of_mem_involutionSet_H
import Submission.Work.ASM.oddCore_odd
import Submission.Work.A7.Defs
import Submission.OddOrder.Mathlib.Subgroup
import Submission.Work.CORE3.MData.le_left_of_le_sup_of_coprime
import Submission.Work.CORE3.MData.odd_relIndex_sup_of_card

set_option linter.style.haveILetI false

namespace Work.CORE3.MData

open Subgroup
open Work.GW2

/-- A natural number coprime to `8` as soon as it is odd. -/
private theorem coprime_eight_of_odd {n : ℕ} (h : Odd n) : Nat.Coprime n 8 := by
  have h2 : Nat.Coprime n 2 := (Nat.coprime_two_left.mpr h).symm
  simpa using h2.pow_right 3

/-!
# CORE3 (`MData`): `O(M) ≤ B` in the subcase `Ĥ = H`

Bender 1981, J. Algebra 70, §3, p. 223, display: `B ∩ M = O(M)`, where `B = C_U(S)` and `M` is a
maximal subgroup containing `N_G(P₂)`.  This file proves the inclusion `O(M) ≤ B`, i.e.
`O(M) ≤ B.U ⊓ C_G(S)`.

The mathematical argument (no `M`-analysis needed beyond the `A₇`-data of `Case1aA7Prop`):

* `E = E(M)` is quasisimple with odd centre (`LayerProp`) and `|E|₂ = |M|₂ = 2³` (from
  `E/Z(E) ≅ A₇` and `|S| = 8`), so `[M : E·O(M)]` is odd; hence `S ≤ E·O(M)`.
* For `s ∈ S` write `s = e·k` with `e ∈ E`, `k ∈ O(M)`.  The class of `k` in `O(M)/Z(E)` is
  well defined and `s ↦ k·Z(E)` is a homomorphism `S → O(M)/Z(E)`; its image is a 2-group inside
  a group of odd order, hence trivial.  So `S ≤ E·Z(E) = E`.
* `[S, O(M)] ≤ [E, O(M)] = 1` (`O(M)` centralizes the quasisimple `E`), giving `O(M) ≤ C_G(S)`.
* `O(M) ≤ C_G(E) ≤ C_G(t) = H`, so `O(M) ≤ O(H) = U` since `H/U ≅ S` is a 2-group.
-/

theorem OddCoreLeBc (I : Work.CORE3.Case1Inputs) (hSetup : Work.GW2.Case1aSetupProp)
    (hFr : Work.GW2.Case1aFrattiniProp) (hAb : Work.GW2.Case1aAbelianProp)
    (hA7 : Work.GW2.Case1aA7Prop) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
      ∀ B : Work.GW2.BenderSetup G, Work.GW2.Case1 B → B.Hhat = B.H →
      ∀ D : Work.GW2.Case1aData B, ∀ P2 M : Subgroup G,
      P2 ≤ B.U ⊓ Subgroup.centralizer ((B.S : Subgroup G) : Set G) → IsPGroup D.p P2 →
      ¬ D.p ∣ P2.relIndex (B.U ⊓ Subgroup.centralizer ((B.S : Subgroup G) : Set G)) →
      IsCoatom M → Subgroup.normalizer (P2 : Set G) ≤ M →
      Work.GW2.oddCoreIn M ≤ B.U ⊓ Subgroup.centralizer ((B.S : Subgroup G) : Set G) := by
  intro G _instG _finG hFT hCtx B hCase hHhat D P2 M hP2le hP2grp hP2ndvd hMcoat hNM
  classical
  obtain ⟨hSM, hV2, hEiso, hScard, _hP0card⟩ :=
    hA7 G hFT hCtx B hCase hHhat D P2 M hP2le hP2grp hP2ndvd hMcoat hNM
  -- ## Step 0: the layer of `M` is non-trivial
  have htE : B.t ∈ Work.GW2.layerIn M :=
    hV2 (Subgroup.mem_sup_left (Subgroup.mem_zpowers B.t))
  have hlayerIn_ne : Work.GW2.layerIn M ≠ ⊥ := by
    intro hbot
    exact Work.CORE2A.bSetup_t_ne_one B (Subgroup.mem_bot.mp (hbot ▸ htE))
  have hlayer_ne : Work.GW2.layer ↥M ≠ ⊥ := by
    intro hbot
    refine hlayerIn_ne ?_
    show (Work.GW2.layer ↥M).map M.subtype = ⊥
    rw [hbot, Subgroup.map_bot]
  -- ## Step 1: `E = E(M)` is quasisimple with odd centre
  obtain ⟨hEq, hZodd⟩ := mdata_layer_quasisimple I hCtx B hMcoat hlayer_ne
  haveI hEnorm : (Work.GW2.layer ↥M).Normal := mdata_layer_normal M
  have hlayerIn_le : Work.GW2.layerIn M ≤ M := Subgroup.map_subtype_le _
  have hoddCoreIn_le : Work.GW2.oddCoreIn M ≤ M := Subgroup.map_subtype_le _
  -- ## Step 2: `O(M)` centralizes `E(M)`
  have hcomm : ⁅Work.GW2.oddCoreIn M, Work.GW2.layerIn M⁆ = ⊥ :=
    mdata_oddCore_commutator_layer M hFT hEq
  have hKcenE : Work.GW2.oddCoreIn M ≤
      Subgroup.centralizer ((Work.GW2.layerIn M : Subgroup G) : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hKodd : Odd (Nat.card (Work.GW2.oddCoreIn M)) := by
    rw [Work.GW2.oddCoreIn, Subgroup.card_map_of_injective M.subtype_injective]
    exact Work.ASM.oddCore_odd ↥M
  -- ## Step 3: `O(M) ≤ H = C_G(t)`
  have hKH : Work.GW2.oddCoreIn M ≤ B.H := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    have hyE : y ∈ Work.GW2.layerIn M := by rw [hy]; exact htE
    exact (Subgroup.mem_centralizer_iff.mp (hKcenE hx)) y hyE
  -- ## Step 4: `O(M) ≤ U` (inside `↥H`, where `U` is normal and `H/U ≅ S` is a 2-group)
  have hKU : Work.GW2.oddCoreIn M ≤ B.U := by
    haveI : ((B.U).subgroupOf B.H).Normal := Work.CORE2A.subgroupOf_oddCoreIn_normal B.H
    have hX : (Work.GW2.oddCoreIn M).subgroupOf B.H ≤
        (B.U).subgroupOf B.H ⊔ ((B.S : Subgroup G)).subgroupOf B.H := by
      have h1 : Work.GW2.oddCoreIn M ≤ B.U ⊔ (B.S : Subgroup G) := by
        rw [Work.CORE3.H_eq_U_sup_S G I.T hCtx B]
        exact hKH
      calc (Work.GW2.oddCoreIn M).subgroupOf B.H
          ≤ (B.U ⊔ (B.S : Subgroup G)).subgroupOf B.H := Subgroup.subgroupOf_mono B.H h1
        _ = (B.U).subgroupOf B.H ⊔ ((B.S : Subgroup G)).subgroupOf B.H :=
            Subgroup.subgroupOf_sup (Work.CORE2A.bSetup_U_le_H B) (Work.CORE2A.bSetup_S_le_H B)
    have hcop : Nat.Coprime (Nat.card ((Work.GW2.oddCoreIn M).subgroupOf B.H))
        (Nat.card (((B.S : Subgroup G)).subgroupOf B.H)) := by
      have hc1 : Nat.card ((Work.GW2.oddCoreIn M).subgroupOf B.H) =
          Nat.card (Work.GW2.oddCoreIn M) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv
      have hc2 : Nat.card (((B.S : Subgroup G)).subgroupOf B.H) = 8 := by
        rw [Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe (Work.CORE2A.bSetup_S_le_H B)).toEquiv, hScard]
      rw [hc1, hc2]
      exact coprime_eight_of_odd hKodd
    have hres := le_left_of_le_sup_of_coprime (G := ↥B.H) (A := (B.U).subgroupOf B.H)
      (C := ((B.S : Subgroup G)).subgroupOf B.H) (X := (Work.GW2.oddCoreIn M).subgroupOf B.H)
      inferInstance hX hcop
    intro x hx
    have hxH : x ∈ B.H := hKH hx
    have hmem : (⟨x, hxH⟩ : ↥B.H) ∈ (Work.GW2.oddCoreIn M).subgroupOf B.H :=
      Subgroup.mem_subgroupOf.mpr hx
    have := hres hmem
    rwa [Subgroup.mem_subgroupOf] at this
  -- ## Step 5: `S` is a Sylow 2-subgroup of `M`, and `|E|` is `8` times an odd number
  have hSodd : Odd (((B.S : Subgroup G)).relIndex M) := by
    have hnd : ¬ 2 ∣ (((B.S : Subgroup G)).relIndex M) := by
      have h := Sylow.not_dvd_index (B.S.subtype hSM)
      rwa [Sylow.coe_subtype] at h
    exact Nat.not_even_iff_odd.mp (by simpa [even_iff_two_dvd] using hnd)
  have hFactsB : ∃ b : ℕ, Odd b ∧ Nat.card (Work.GW2.layerIn M) = 8 * b := by
    obtain ⟨e⟩ := hEiso
    let ee : ↥(Work.GW2.layer ↥M) ≃* ↥(Work.GW2.layerIn M) :=
      Subgroup.equivMapOfInjective (Work.GW2.layer ↥M) M.subtype M.subtype_injective
    have hcen : Subgroup.map (ee : ↥(Work.GW2.layer ↥M) →* ↥(Work.GW2.layerIn M))
        (Subgroup.center ↥(Work.GW2.layer ↥M)) = Subgroup.center ↥(Work.GW2.layerIn M) :=
      Subgroup.map_center_eq ee
    have hq : Nat.card (↥(Work.GW2.layer ↥M) ⧸ Subgroup.center ↥(Work.GW2.layer ↥M)) = 2520 := by
      have hcongr := Nat.card_congr (QuotientGroup.congr
        (Subgroup.center ↥(Work.GW2.layer ↥M))
        (Subgroup.center ↥(Work.GW2.layerIn M)) ee hcen).toEquiv
      rw [hcongr, Nat.card_congr e.toEquiv, Work.A7.card_alternatingGroup_seven]
    refine ⟨Nat.card (Subgroup.center ↥(Work.GW2.layer ↥M)) * 315, hZodd.mul (by norm_num), ?_⟩
    have h1 : Nat.card (Work.GW2.layerIn M) = Nat.card ↥(Work.GW2.layer ↥M) :=
      Subgroup.card_map_of_injective (f := M.subtype) (K := Work.GW2.layer ↥M)
        M.subtype_injective
    have h2 : Nat.card ↥(Work.GW2.layer ↥M) =
        Nat.card ↥(Subgroup.center ↥(Work.GW2.layer ↥M)) *
          (Subgroup.center ↥(Work.GW2.layer ↥M)).index :=
      (Subgroup.card_mul_index (Subgroup.center ↥(Work.GW2.layer ↥M))).symm
    have h3 : (Subgroup.center ↥(Work.GW2.layer ↥M)).index = 2520 := by
      rw [Subgroup.index_eq_card]
      exact hq
    rw [h1, h2, h3]
    ring
  obtain ⟨b, hbodd, hEcard⟩ := hFactsB
  -- ## Step 6: `S ≤ E ⊔ O(M)`
  have hTodd : Odd ((Work.GW2.layerIn M ⊔ Work.GW2.oddCoreIn M).relIndex M) :=
    odd_relIndex_sup_of_card b hSM hlayerIn_le hoddCoreIn_le hScard hEcard hbodd hSodd
  have hsubEq : (Work.GW2.layerIn M ⊔ Work.GW2.oddCoreIn M).subgroupOf M =
      Work.GW2.layer ↥M ⊔ Work.GW2.oddCore ↥M := by
    show (((Work.GW2.layer ↥M).map M.subtype ⊔ (Work.GW2.oddCore ↥M).map M.subtype)).subgroupOf M
      = Work.GW2.layer ↥M ⊔ Work.GW2.oddCore ↥M
    rw [← Subgroup.comap_subtype, ← Subgroup.map_sup,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  have hHN : (Work.GW2.layer ↥M ⊔ Work.GW2.oddCore ↥M).Normal := by
    haveI : (Work.GW2.oddCore ↥M).Normal := Work.GW2.oddCore_normal ↥M
    rw [← Subgroup.normalizer_eq_top_iff]
    have h3 := Subgroup.inf_normalizer_le_normalizer_sup (Work.GW2.layer ↥M)
      (Work.GW2.oddCore ↥M)
    rw [Subgroup.normalizer_eq_top_iff.mpr hEnorm,
      Subgroup.normalizer_eq_top_iff.mpr (Work.GW2.oddCore_normal ↥M), top_inf_eq] at h3
    exact le_antisymm le_top h3
  haveI : ((Work.GW2.layerIn M ⊔ Work.GW2.oddCoreIn M).subgroupOf M).Normal := by
    rw [hsubEq]
    exact hHN
  have hKsub : (Work.GW2.oddCoreIn M).subgroupOf M = Work.GW2.oddCore ↥M := by
    show ((Work.GW2.oddCore ↥M).map M.subtype).subgroupOf M = Work.GW2.oddCore ↥M
    rw [← Subgroup.comap_subtype, Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  have hSEK : (B.S : Subgroup G) ≤ Work.GW2.layerIn M ⊔ Work.GW2.oddCoreIn M := by
    have hcop : Nat.Coprime (Nat.card (((B.S : Subgroup G)).subgroupOf M))
        (((Work.GW2.layerIn M ⊔ Work.GW2.oddCoreIn M).subgroupOf M).index) := by
      have hc1 : Nat.card (((B.S : Subgroup G)).subgroupOf M) = 8 := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSM).toEquiv, hScard]
      have hc2 : ((Work.GW2.layerIn M ⊔ Work.GW2.oddCoreIn M).subgroupOf M).index =
          (Work.GW2.layerIn M ⊔ Work.GW2.oddCoreIn M).relIndex M := rfl
      rw [hc1, hc2]
      exact (coprime_eight_of_odd hTodd).symm
    have hle : ((B.S : Subgroup G)).subgroupOf M ≤
        (Work.GW2.layerIn M ⊔ Work.GW2.oddCoreIn M).subgroupOf M :=
      Subgroup.le_of_coprime_card_index_of_normal hcop
    intro x hx
    have hxM : x ∈ M := hSM hx
    have hmem : (⟨x, hxM⟩ : ↥M) ∈ ((B.S : Subgroup G)).subgroupOf M :=
      Subgroup.mem_subgroupOf.mpr hx
    exact Subgroup.mem_subgroupOf.mp (hle hmem)
  -- ## Step 7: `S ≤ E`
  have hSE : (B.S : Subgroup G) ≤ Work.GW2.layerIn M := by
    have hX : ((B.S : Subgroup G)).subgroupOf M ≤
        (Work.GW2.layer ↥M) ⊔ ((Work.GW2.oddCoreIn M).subgroupOf M) := by
      have h1 : ((B.S : Subgroup G)).subgroupOf M ≤
          (Work.GW2.layerIn M ⊔ Work.GW2.oddCoreIn M).subgroupOf M :=
        Subgroup.subgroupOf_mono M hSEK
      rw [hsubEq] at h1
      rw [hKsub]
      exact h1
    have hcop : Nat.Coprime (Nat.card (((B.S : Subgroup G)).subgroupOf M))
        (Nat.card ((Work.GW2.oddCoreIn M).subgroupOf M)) := by
      have hc1 : Nat.card (((B.S : Subgroup G)).subgroupOf M) = 8 := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSM).toEquiv, hScard]
      have hc2 : Nat.card ((Work.GW2.oddCoreIn M).subgroupOf M) =
          Nat.card (Work.GW2.oddCoreIn M) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hoddCoreIn_le).toEquiv
      rw [hc1, hc2]
      exact (coprime_eight_of_odd hKodd).symm
    have hres := le_left_of_le_sup_of_coprime (G := ↥M) (A := Work.GW2.layer ↥M)
      (C := (Work.GW2.oddCoreIn M).subgroupOf M) (X := ((B.S : Subgroup G)).subgroupOf M)
      hEnorm hX hcop
    intro x hx
    have hxM : x ∈ M := hSM hx
    have hmem : (⟨x, hxM⟩ : ↥M) ∈ Work.GW2.layer ↥M :=
      hres (Subgroup.mem_subgroupOf.mpr hx)
    show x ∈ (Work.GW2.layer ↥M).map M.subtype
    exact Subgroup.mem_map.mpr ⟨⟨x, hxM⟩, hmem, rfl⟩
  -- ## Step 8: `O(M) ≤ C_G(S)`
  have hKcenS : Work.GW2.oddCoreIn M ≤
      Subgroup.centralizer ((B.S : Subgroup G) : Set G) :=
    Subgroup.le_centralizer_iff.mpr (hSE.trans (Subgroup.le_centralizer_iff.mp hKcenE))
  exact le_inf hKU hKcenS

end Work.CORE3.MData
