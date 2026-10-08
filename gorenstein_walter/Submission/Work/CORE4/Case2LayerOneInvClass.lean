import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.DihOrCycSub

/-!
# CORE4: `E(M)` has one class of involutions

Bender 1981, §4 (p. 224), second sentence of the first paragraph: for the maximal subgroup `M`
with `t ∈ E(M)`, the layer `E = E(M)` has a single class of involutions, whence
`M = E·C_M(t)`.

This file isolates the part of that step that needs no §4 data at all beyond `M` being a coatom
with `t ∈ E(M)`:

* `M` is a proper subgroup of `G`, so by `BenderCtx.ih` (the minimal-counterexample hypothesis,
  `SmallerDGroups G`) and heredity of the Sylow 2-shape (`DihOrCycSub`) it is itself a D-group;
* `LayerProp` (the input `I.toolkit.lay`) then says that `E(M)` is the *unique* normal quasisimple
  subgroup of `M`, which is how `E(M)` is seen to be normal in `M` and quasisimple;
* DSTR's fusion input `I.layerOneInvClass` (`LayerOneInvClassPropC4`) gives the single class of
  involutions inside the layer of `M`, which is then transported along the inclusion `M ↪ G`.
-/

open scoped MatrixGroups

namespace Work.CORE4

open Subgroup

/-- **`OneInvClassIn` passes to the ambient group along a subgroup inclusion.**  If `E ≤ ↥K` has
one class of involutions under conjugation by `E`, then its image in the ambient group `X` has one
class of involutions under conjugation by that image. -/
theorem oneInvClassIn_map_subtype {X : Type*} [Group X] {K : Subgroup X} {E : Subgroup ↥K}
    (h : Work.GW2.OneInvClassIn E) : Work.GW2.OneInvClassIn (E.map K.subtype) := by
  intro x hx y hy
  simp only [Work.GW2.involutionSet, Set.mem_ofPred_eq] at hx hy
  obtain ⟨hxE, hx2⟩ := hx
  obtain ⟨hyE, hy2⟩ := hy
  obtain ⟨a, haE, rfl⟩ := Subgroup.mem_map.mp hxE
  obtain ⟨b, hbE, hby⟩ := Subgroup.mem_map.mp hyE
  have hby' : (b : X) = y := hby
  have ha2 : orderOf a = 2 := by rw [← orderOf_coe a]; exact hx2
  have hb2 : orderOf b = 2 := by rw [← orderOf_coe b, hby']; exact hy2
  obtain ⟨c, hcE, hc⟩ := h a ⟨haE, ha2⟩ b ⟨hbE, hb2⟩
  refine ⟨K.subtype c, Subgroup.mem_map_of_mem K.subtype hcE, ?_⟩
  rw [← hby]
  rw [show K.subtype c * K.subtype a * (K.subtype c)⁻¹ = K.subtype (c * a * c⁻¹) by
        simp [map_mul, map_inv]]
  rw [hc]

theorem Case2LayerOneInvClass (I : Work.GW2.C4Inputs) : ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G → ∀ B : Work.GW2.BenderSetup G, ∀ M : Subgroup G, IsCoatom M → B.t ∈ Work.GW2.layerIn M → Work.GW2.OneInvClassIn (Work.GW2.layerIn M) := by
  intro G _ _ hbc B M hcoat ht
  have ht1 : B.t ≠ 1 := by
    intro h1
    have ht2 := B.t_order
    rw [h1, orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  -- the layer of `M` is nontrivial, since `t` lies in it
  have hlayer_ne : Work.GW2.layer ↥M ≠ ⊥ := by
    intro hbot
    have hbot' : Work.GW2.layerIn M = ⊥ := by
      rw [Work.GW2.layerIn, hbot, Subgroup.map_bot]
    exact ht1 (Subgroup.mem_bot.mp (hbot' ▸ ht))
  -- so `M` has a normal quasisimple subgroup
  obtain ⟨E', hE'norm, hE'q⟩ : ∃ E' : Subgroup ↥M, E'.Normal ∧ Work.GW2.IsQuasisimple E' := by
    by_contra hcon
    apply hlayer_ne
    rw [Work.GW2.layer, sSup_eq_bot]
    intro F hF
    by_contra hFne
    exact hcon ⟨F, hF.1, hF.2⟩
  -- `M` is proper in `G`, hence inherits the Sylow 2-shape and is a D-group
  have hD : Work.GW2.DihOrCycSylow ↥M := DihOrCycSub hbc.sylow M
  have hcard : Nat.card ↥M < Nat.card G := by
    have hlt : M < ⊤ := hcoat.lt_top
    have h := Subgroup.card_lt_of_lt hlt
    rwa [Subgroup.card_top] at h
  have hIsD : Work.GW2.IsDGroup ↥M := hbc.ih ↥M hcard hD
  -- Bender 1.6 / `LayerProp`: `E(M) = E'` is the unique normal quasisimple subgroup of `M`
  obtain ⟨hlayer, -, -⟩ := I.toolkit.lay ↥M I.toolkit.ft hD hIsD E' hE'norm hE'q
  have hqs : Work.GW2.IsQuasisimple (Work.GW2.layer ↥M) := hlayer.symm ▸ hE'q
  have hnorm : (Work.GW2.layer ↥M).Normal := hlayer.symm ▸ hE'norm
  -- DSTR's fusion input gives the single class of involutions inside `E(M)`
  have hone : Work.GW2.OneInvClassIn (Work.GW2.layer ↥M) :=
    I.layerOneInvClass ↥M I.toolkit.ft hD (Work.GW2.layer ↥M) hnorm hqs
  exact oneInvClassIn_map_subtype hone

end Work.CORE4
