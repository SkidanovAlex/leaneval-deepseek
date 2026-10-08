import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE3.MDataAux
import Submission.Work.CORE3.MData.BcInfMLeOddCore
import Submission.Work.CORE3.MData.OddCoreLeBc
import Submission.Work.BMAX.Components.isComponent_map_subtype
import Submission.Work.CORE3.MData.MDataLayerLeLayerNormalizer
import Submission.Work.CORE3.MData.EqOfQuasisimpleOfA7QuotientNoNormal
import Submission.Work.CORE3.MData.NoA7SectionPSL2
import Submission.Work.CORE3.MData.A7QuotientSubgroupOf

namespace Work.CORE3



open Subgroup
open Work.GW2

/-- `E(K) ⊴ K`, i.e. `K ≤ N_G(E(K))`. -/
theorem mdataLayerIn_le_normalizer {G : Type} [Group G] (K : Subgroup G) :
    K ≤ Subgroup.normalizer ((layerIn K : Subgroup G) : Set G) := by
  have hnorm : (Work.GW2.layer ↥K).Normal := Work.CORE3.mdata_layer_normal K
  rw [Subgroup.le_normalizer_iff]
  intro m hm x hx
  rw [layerIn] at hx ⊢
  rcases hx with ⟨y, hy, rfl⟩
  exact ⟨⟨m, hm⟩ * y * ⟨m, hm⟩⁻¹, Subgroup.Normal.conj_mem hnorm y hy ⟨m, hm⟩, by simp⟩

/-- Bender 1981 §3, p. 223: local control in the §3a `M`-analysis, in the form Bender states it:
`N_G(X) ≤ M` for `1 ≠ X ⊆ B ∩ M`.  Since `B ⊓ M = O(M)`
(`Work.CORE3.MData/BcInfMLeOddCore.lean`, `Work.CORE3.MData/OddCoreLeBc.lean`, both proved), the
provable form of the clause is the one below, for `X ≤ oddCoreIn M = O(M)`.

Route: `X ≤ O(M)` centralizes `E(M)` (the three-subgroup argument: `O(M) ∩ E(M)` is a proper
normal subgroup of the quasisimple `E(M) = layer ↥M`, hence central, so
`[E(M), X] = 1` — `Work.CORE3.mdata_oddCore_commutator_layer` and
`Work.CORE3.mdata_oddCore_le_centralizer_layer` in `MDataAux`).  Then `E(M) ≤ N_G(X)`, and
applying Lemma 2.9 (`I.h29`, with `N_G(X) ≠ ⊤` since `X ≤ M ⊊ G` and `G` is simple) to
`N := N_G(X)` gives `E(N) = E(M)`, hence `N ≤ N_G(E(M)) = M` (maximality of `M`, since
`E(M) ⊴ M ≠ 1`). -/
theorem MDataLocalControlOddCore (I : Case1Inputs) (hSetup : Case1aSetupProp)
    (hFr : Case1aFrattiniProp) (hAb : Case1aAbelianProp) (hA7 : Case1aA7Prop) :
    ∀ (G : Type) [Group G] [Finite G], FeitThompsonProp → BenderCtx G →
      ∀ B : BenderSetup G, Case1 B → B.Hhat = B.H →
      ∀ D : Case1aData B, ∀ P2 M : Subgroup G,
      P2 ≤ B.U ⊓ centralizer ((B.S : Subgroup G) : Set G) → IsPGroup D.p P2 →
      ¬ D.p ∣ P2.relIndex (B.U ⊓ centralizer ((B.S : Subgroup G) : Set G)) →
      IsCoatom M → normalizer (P2 : Set G) ≤ M →
      ∀ X : Subgroup G, X ≠ ⊥ → X ≤ oddCoreIn M →
        normalizer (X : Set G) ≤ M := by
  intro G _instG _finG hFT hCtx B hCase hHhat D P2 M hPle hPgrp hPndvd hMcoat hNM X hXne hXle
  classical
  haveI : IsSimpleGroup G := hCtx.simple
  -- ## Bender's `A₇`-data for `M`
  obtain ⟨_hSM, hV2, hEiso, _hScard, _hP0⟩ :=
    hA7 G hFT hCtx B hCase hHhat D P2 M hPle hPgrp hPndvd hMcoat hNM
  have ht_mem : B.t ∈ layerIn M :=
    hV2 (Subgroup.mem_sup_left (Subgroup.mem_zpowers B.t))
  have hlayerM : Work.GW2.layer ↥M ≠ ⊥ := fun hbot =>
    Work.CORE2A.bSetup_t_ne_one B (by
      have h : B.t ∈ (Work.GW2.layer ↥M).map M.subtype := ht_mem
      rw [hbot, Subgroup.map_bot] at h
      exact h)
  -- ## `O(M)` centralizes `E(M) = layerIn M`
  obtain ⟨hEqM, _hZoddM⟩ := Work.CORE3.mdata_layer_quasisimple I hCtx B hMcoat hlayerM
  have hEqIn : Work.GW2.IsQuasisimple (layerIn M) :=
    Work.BMAX.Components.isQuasisimple_map_subtype (C := M) hEqM
  have hOcen : oddCoreIn M ≤ Subgroup.centralizer ((layerIn M : Subgroup G) : Set G) :=
    Work.CORE3.mdata_oddCore_le_centralizer_layer M hFT hEqM
  have hXcen : X ≤ Subgroup.centralizer ((layerIn M : Subgroup G) : Set G) := hXle.trans hOcen
  -- ## `E(M) ≤ N_G(X) =: N`
  set N : Subgroup G := Subgroup.normalizer (X : Set G) with hNdef
  have hEleN : layerIn M ≤ N := by
    rw [Subgroup.le_normalizer_iff]
    intro e he x hx
    have hcomm : e * x = x * e := Subgroup.mem_centralizer_iff.mp (hXcen hx) e he
    show e * x * e⁻¹ ∈ X
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    exact hx
  -- ## `X ≤ M ⊊ G` and `X ≠ ⊥` force `N ≠ ⊤`
  have hXM : X ≤ M := hXle.trans (Work.CORE3.oddCoreIn_le_self M)
  have hNne : N ≠ ⊤ := by
    intro htop
    haveI : X.Normal := Subgroup.normalizer_eq_top_iff.mp (by rw [← hNdef]; exact htop)
    rcases Subgroup.Normal.eq_bot_or_eq_top X with h | h
    · exact hXne h
    · exact hMcoat.ne_top (top_le_iff.mp (h ▸ hXM))
  -- ## Lemma 2.9 at `N`: `E(M) ≤ E(N) = layerIn N`
  have hEleN' : layerIn M ≤ layerIn N :=
    Work.CORE3.MData.MDataLayerLeLayerNormalizer I hA7 G hFT hCtx B hCase hHhat D P2 M
      hPle hPgrp hPndvd hMcoat hNM X hXne hXle
  -- ## `N` has a normal quasisimple subgroup, so Bender's `LayerProp` applies to `N`
  have hlayerInM : layerIn M ≠ ⊥ := fun h =>
    hlayerM (Subgroup.map_injective M.subtype_injective (by rw [← layerIn, h, Subgroup.map_bot]))
  have hEneN : layerIn N ≠ ⊥ := fun hbot =>
    hlayerInM (le_bot_iff.mp (hEleN'.trans (le_of_eq hbot)))
  have hlayerN : Work.GW2.layer ↥N ≠ ⊥ := fun hbot =>
    hEneN (by rw [layerIn, hbot, Subgroup.map_bot])
  have hex : ∃ E₀ : Subgroup ↥N, E₀.Normal ∧ Work.GW2.IsQuasisimple E₀ ∧ E₀ ≠ ⊥ := by
    by_contra hcon
    apply hlayerN
    rw [Work.GW2.layer, sSup_eq_bot]
    intro E₀ hE₀
    by_contra hne
    exact hcon ⟨E₀, hE₀.1, hE₀.2, hne⟩
  obtain ⟨E₀, hE₀n, hE₀q, _hE₀ne⟩ := hex
  have hdihN : Work.GW2.DihOrCycSylow ↥N := Work.CORE2A.dihOrCycSylow_subgroup hCtx.sylow N
  have hIsDN : Work.GW2.IsDGroup ↥N :=
    hCtx.ih ↥N (Subgroup.card_lt_card_of_ne_top hNne) hdihN
  obtain ⟨hlayerNeq, _hZoddN, hshapeN⟩ := I.T.lay ↥N I.T.ft hdihN hIsDN E₀ hE₀n hE₀q
  -- ## `(E(M)).subgroupOf N ≤ E₀ = E(N)`
  have hEleE₀ : (layerIn M).subgroupOf N ≤ E₀ := by
    have h : (layerIn M).subgroupOf N ≤ (layerIn N).subgroupOf N :=
      Subgroup.subgroupOf_mono N hEleN'
    have h₂ : (layerIn N).subgroupOf N = Work.GW2.layer ↥N := by
      rw [layerIn]
      exact Subgroup.comap_map_eq_self_of_injective N.subtype_injective (Work.GW2.layer ↥N)
    rwa [h₂, hlayerNeq] at h
  -- ## `E(N) = layerIn N` is quasisimple
  have hEqInN : Work.GW2.IsQuasisimple (layerIn N) := by
    have h : Work.GW2.IsQuasisimple (E₀.map N.subtype) :=
      Work.BMAX.Components.isQuasisimple_map_subtype (C := N) hE₀q
    rwa [← hlayerNeq] at h
  -- ## Case analysis on `E(N)/Z ≅ A₇` or `≅ PSL(2,q)`
  rcases hshapeN with hA7N | ⟨p, k, hpp, hpodd, hpk, hPSLN⟩
  · -- `A₇`-case: `E(N) = E(M)`, so `E(M) ⊴ N` and `N ≤ N_G(E(M)) = M`
    have hA7N' : Nonempty ((↥(layerIn N) ⧸ Subgroup.center ↥(layerIn N))
        ≃* alternatingGroup (Fin 7)) := by
      obtain ⟨e⟩ := hA7N
      have h₁ := (Work.CORE3.MData.QuotientCenterMapIso N.subtype N.subtype_injective E₀).some
      have hlin : layerIn N = E₀.map N.subtype := by rw [layerIn, hlayerNeq]
      rw [hlin]
      exact ⟨h₁.symm.trans e⟩
    have hEeq : layerIn M = layerIn N :=
      Work.CORE3.MData.EqOfQuasisimpleOfA7QuotientNoNormal hEleN' hEqIn hEqInN hEiso hA7N'
    have hNleM : N ≤ M := by
      have hle : N ≤ Subgroup.normalizer ((layerIn M : Subgroup G) : Set G) := by
        rw [hEeq]; exact Work.CORE3.mdataLayerIn_le_normalizer N
      have hMle : M ≤ Subgroup.normalizer ((layerIn M : Subgroup G) : Set G) :=
        Work.CORE3.mdataLayerIn_le_normalizer M
      have hne : Subgroup.normalizer ((layerIn M : Subgroup G) : Set G) ≠ ⊤ := by
        intro htop
        haveI : (layerIn M : Subgroup G).Normal := Subgroup.normalizer_eq_top_iff.mp htop
        rcases Subgroup.Normal.eq_bot_or_eq_top (layerIn M) with h | h
        · exact hlayerInM h
        · exact hMcoat.ne_top (top_le_iff.mp (h ▸ Subgroup.map_subtype_le (Work.GW2.layer ↥M)))
      rcases hMcoat.le_iff.mp hMle with h | h
      · exact absurd h hne
      · rwa [h] at hle
    exact hNleM
  · -- `PSL(2,q)`-case: excluded
    exfalso
    haveI : Fact p.Prime := hpp
    exact Work.CORE3.MData.NoA7SectionPSL2 p k hpodd hpk (↥N) E₀ hE₀n hPSLN
      ((layerIn M).subgroupOf N)
      (Work.BMAX.QuasiComm.isQuasisimple_subgroupOf hEleN hEqIn)
      hEleE₀
      (Work.CORE3.MData.A7QuotientSubgroupOf hEleN hEiso)

end Work.CORE3


