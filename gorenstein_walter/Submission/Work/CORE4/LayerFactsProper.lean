/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area CORE4, `Work.CORE4`)

# AREA CORE4 — `layer_facts_proper`: the layer facts at any proper subgroup

The helper requested in design pass 19: the proof of `Work.CORE4.layer_facts_coatom`, with the
coatom hypothesis weakened to `M ≠ ⊤` (which is all the proof uses, through
`card_lt_card_of_ne_top` and `BenderCtx.ih`).  It is used by the `S4`/`S5` leaves of design 19 at
`K := N_G(X)`, which is proper but not a coatom.
-/
import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.LayerCtx6
import Submission.Work.CORE4.Case2LayerOneInvClass
import Submission.Work.CORE4.Ecent.alt7_odd_centralizer_sylow
import Submission.Work.CORE4.Ecent.psl_odd_centralizer_sylow
import Submission.OddOrder.Isaacs.Ch09_MoreSubnormality.SylowSubnormal

open scoped MatrixGroups

namespace Work.CORE4

open Work.GW2 Subgroup

variable {G : Type} [Group G] [Finite G]

/-- **Bender §4, p. 224, first paragraph**, in the minimal form used here: for a coatom `M` of a
`BenderCtx` group with `t ∈ E(M)`, `layer ↥M` is a (unique) normal quasisimple subgroup of `↥M`,
of odd centre, with `E(M)/Z(E(M)) ≅ A₇` or `PSL(2,q)`. -/
theorem layer_facts_proper (I : Work.GW2.C4Inputs) (hbc : Work.GW2.BenderCtx G)
    {B : Work.GW2.BenderSetup G} {M : Subgroup G} (hMtop : M ≠ ⊤)
    (ht : B.t ∈ Work.GW2.layerIn M) :
    ∃ E1 : Subgroup ↥M, E1.Normal ∧ Work.GW2.layer ↥M = E1 ∧
      Odd (Nat.card (Subgroup.center ↥E1)) ∧
      (Nonempty (↥E1 ⧸ Subgroup.center ↥E1 ≃* alternatingGroup (Fin 7)) ∨
        ∃ p k : ℕ, ∃ _ : Fact p.Prime, Odd p ∧ 5 ≤ p ^ k ∧
          Nonempty (↥E1 ⧸ Subgroup.center ↥E1 ≃* PSL(2, GaloisField p k))) := by
  have ht1 : B.t ≠ 1 := by
    intro h1
    have ht2 := B.t_order
    rw [h1, orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  -- the layer of `M` is nontrivial
  have hlayer_ne : Work.GW2.layer ↥M ≠ ⊥ := by
    intro hbot
    have hbot' : Work.GW2.layerIn M = ⊥ := by
      rw [Work.GW2.layerIn, hbot, Subgroup.map_bot]
    exact ht1 (Subgroup.mem_bot.mp (hbot' ▸ ht))
  -- so `M` has a normal quasisimple subgroup
  obtain ⟨E1, hE1norm, hE1q⟩ : ∃ E1 : Subgroup ↥M, E1.Normal ∧ Work.GW2.IsQuasisimple E1 := by
    by_contra hcon
    apply hlayer_ne
    rw [Work.GW2.layer, sSup_eq_bot]
    intro F hF
    by_contra hFne
    exact hcon ⟨F, hF.1, hF.2⟩
  -- `M` is a proper subgroup of `G`, hence a D-group
  have hD : Work.GW2.DihOrCycSylow ↥M := DihOrCycSub hbc.sylow M
  have hcard : Nat.card ↥M < Nat.card G := card_lt_card_of_ne_top hMtop
  have hIsD : Work.GW2.IsDGroup ↥M := hbc.ih ↥M hcard hD
  -- Bender 1.6 / `LayerProp`
  obtain ⟨hlayer, hZodd, hshape⟩ :=
    I.toolkit.lay ↥M I.toolkit.ft hD hIsD E1 hE1norm hE1q
  exact ⟨E1, hE1norm, hlayer, hZodd, hshape⟩

/-- **Bender §4, p. 224, first paragraph**, in the minimal form used here: for a coatom `M` of a
`BenderCtx` group with `t ∈ E(M)`, `layer ↥M` is a (unique) normal quasisimple subgroup of `↥M`,
of odd centre, with `E(M)/Z(E(M)) ≅ A₇` or `PSL(2,q)`. -/
theorem layer_facts_proper_quasisimple (I : Work.GW2.C4Inputs) (hbc : Work.GW2.BenderCtx G)
    {B : Work.GW2.BenderSetup G} {M : Subgroup G} (hMtop : M ≠ ⊤)
    (ht : B.t ∈ Work.GW2.layerIn M) :
    ∃ E1 : Subgroup ↥M, E1.Normal ∧ Work.GW2.layer ↥M = E1 ∧
      Work.GW2.IsQuasisimple E1 ∧
      Odd (Nat.card (Subgroup.center ↥E1)) ∧
      (Nonempty (↥E1 ⧸ Subgroup.center ↥E1 ≃* alternatingGroup (Fin 7)) ∨
        ∃ p k : ℕ, ∃ _ : Fact p.Prime, Odd p ∧ 5 ≤ p ^ k ∧
          Nonempty (↥E1 ⧸ Subgroup.center ↥E1 ≃* PSL(2, GaloisField p k))) := by
  have ht1 : B.t ≠ 1 := by
    intro h1
    have ht2 := B.t_order
    rw [h1, orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  -- the layer of `M` is nontrivial
  have hlayer_ne : Work.GW2.layer ↥M ≠ ⊥ := by
    intro hbot
    have hbot' : Work.GW2.layerIn M = ⊥ := by
      rw [Work.GW2.layerIn, hbot, Subgroup.map_bot]
    exact ht1 (Subgroup.mem_bot.mp (hbot' ▸ ht))
  -- so `M` has a normal quasisimple subgroup
  obtain ⟨E1, hE1norm, hE1q⟩ : ∃ E1 : Subgroup ↥M, E1.Normal ∧ Work.GW2.IsQuasisimple E1 := by
    by_contra hcon
    apply hlayer_ne
    rw [Work.GW2.layer, sSup_eq_bot]
    intro F hF
    by_contra hFne
    exact hcon ⟨F, hF.1, hF.2⟩
  -- `M` is a proper subgroup of `G`, hence a D-group
  have hD : Work.GW2.DihOrCycSylow ↥M := DihOrCycSub hbc.sylow M
  have hcard : Nat.card ↥M < Nat.card G := card_lt_card_of_ne_top hMtop
  have hIsD : Work.GW2.IsDGroup ↥M := hbc.ih ↥M hcard hD
  -- Bender 1.6 / `LayerProp`
  obtain ⟨hlayer, hZodd, hshape⟩ :=
    I.toolkit.lay ↥M I.toolkit.ft hD hIsD E1 hE1norm hE1q
  exact ⟨E1, hE1norm, hlayer, hE1q, hZodd, hshape⟩

