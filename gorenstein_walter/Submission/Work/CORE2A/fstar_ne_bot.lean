/-
Copyright (c) 2026 gorenstein_walter team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CORE2A area (fundmath3-gorenstein_walter)
-/
import Mathlib
import Submission.Work.CORE2A.Defs

/-!
# CORE2A: `F*(X) ≠ 1` for a nontrivial D-group

`F*(X) = F(X) E(X)` is never trivial for a nontrivial finite group `X`: if `F(X) = 1` then
`X` has a component, i.e. `E(X) ≠ 1`.  For a D-group this is read off Bender 1.6
(`Work.GW2.D16Prop`), whose four cases each exhibit a nontrivial normal nilpotent subgroup or a
nontrivial normal quasisimple subgroup:

* `C_X(F_{2'}(X)) ≤ F_{2'}(X)`: if `F_{2'}(X) = 1` then `C_X(1) = X ≤ 1`, contradicting
  `Nontrivial X`; otherwise `F_{2'}(X) ≠ 1` lies in `F(X)`;
* a central involution `z`: `Z(X)` is a nontrivial abelian (hence nilpotent) normal subgroup,
  so `F(X) ≠ 1`;
* `O₂(X)` a four-group: it is a nontrivial normal `2`-subgroup, hence nilpotent, so `F(X) ≠ 1`;
* a normal quasisimple `E`: `E ≤ E(X)`, and `E ≠ 1` because `E/Z(E)` is a nontrivial simple
  group, so `E(X) ≠ 1`.

The helper lemmas are stated for an arbitrary ambient group (`fstar`/`fitting`/`layer` of a
group `X`), so they are reusable outside CORE2A.
-/

open scoped MatrixGroups

namespace Work.CORE2A

open Subgroup
open Work.GW2

/-! ## 1. `F(X)` is the largest normal nilpotent subgroup -/

/-- A normal nilpotent subgroup of `X` lies in `F(X)`. -/
theorem le_fitting_of_normal_isNilpotent {X : Type*} [Group X] {N : Subgroup X} [N.Normal]
    [Group.IsNilpotent ↥N] : N ≤ Work.GW2.fitting X := by
  rw [Work.GW2.fitting]
  exact Subgroup.normal_le_normalCore.mpr (le_sSup ⟨inferInstance, inferInstance⟩)

/-- A nontrivial normal nilpotent subgroup forces `F(X) ≠ 1`. -/
theorem fitting_ne_bot_of_normal_isNilpotent_ne_bot {X : Type*} [Group X] {N : Subgroup X}
    [N.Normal] [Group.IsNilpotent ↥N] (hN : N ≠ ⊥) : Work.GW2.fitting X ≠ ⊥ := by
  intro hbot
  have h := le_fitting_of_normal_isNilpotent (X := X) (N := N)
  rw [hbot] at h
  exact hN (le_bot_iff.mp h)

/-! ## 2. The three source-of-nilpotency cases of Bender 1.6 -/

/-- A central involution forces `F(X) ≠ 1`. -/
theorem fitting_ne_bot_of_central_involution {X : Type*} [Group X]
    (h : ∃ z ∈ Subgroup.center X, orderOf z = 2) : Work.GW2.fitting X ≠ ⊥ := by
  obtain ⟨z, hz, hz2⟩ := h
  refine fitting_ne_bot_of_normal_isNilpotent_ne_bot (X := X)
    (N := Subgroup.center X) fun hbot => ?_
  have hz' : z ∈ (⊥ : Subgroup X) := by rw [← hbot]; exact hz
  have hz1 : z = 1 := Subgroup.mem_bot.mp hz'
  rw [hz1, orderOf_one] at hz2
  exact absurd hz2 (by norm_num)

/-- If `O₂(X)` is a four-group then `F(X) ≠ 1`. -/
theorem fitting_ne_bot_of_isFourGroup_pCore {X : Type*} [Group X] [Finite X]
    (h : Work.GW2.IsFourGroup (Work.GW2.pCore 2 X)) : Work.GW2.fitting X ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hp : IsPGroup 2 (Work.GW2.pCore 2 X) :=
    IsPGroup.iff_card.mpr ⟨2, by rw [h.1]; norm_num⟩
  have : Group.IsNilpotent ↥(Work.GW2.pCore 2 X) := hp.isNilpotent
  refine fitting_ne_bot_of_normal_isNilpotent_ne_bot (X := X)
    (N := Work.GW2.pCore 2 X) fun hbot => ?_
  have hc : Nat.card (Work.GW2.pCore 2 X) = 1 := by rw [hbot]; simp
  rw [h.1] at hc
  exact absurd hc (by norm_num)

/-! ## 3. The layer case of Bender 1.6 -/

/-- A nontrivial normal quasisimple subgroup forces `E(X) ≠ 1`. -/
theorem layer_ne_bot_of_quasisimple_normal {X : Type*} [Group X] {E : Subgroup X}
    (hE : E.Normal) (hQ : Work.GW2.IsQuasisimple E) : Work.GW2.layer X ≠ ⊥ := by
  have hle : E ≤ Work.GW2.layer X := by
    rw [Work.GW2.layer]
    exact le_sSup ⟨hE, hQ⟩
  intro hbot
  have hEbot : E ≤ (⊥ : Subgroup X) := by rw [hbot] at hle; exact hle
  have hEq : E = ⊥ := le_bot_iff.mp hEbot
  have hnt : Nontrivial ↥E := by
    have : Nontrivial (↥E ⧸ Subgroup.center ↥E) := hQ.2.toNontrivial
    exact Function.Surjective.nontrivial (QuotientGroup.mk'_surjective (Subgroup.center ↥E))
  obtain ⟨a, b, hab⟩ := hnt.exists_pair_ne
  refine hab (Subtype.ext ?_)
  have ha : (a : X) ∈ (⊥ : Subgroup X) := by rw [← hEq]; exact a.2
  have hb : (b : X) ∈ (⊥ : Subgroup X) := by rw [← hEq]; exact b.2
  rw [Subgroup.mem_bot.mp ha, Subgroup.mem_bot.mp hb]

/-! ## 4. The target -/

theorem fstar_ne_bot (h16 : Work.GW2.D16Prop) {X : Type} [Group X] [Finite X] (hnt : Nontrivial X)
    (hFT : Work.GW2.FeitThompsonProp) (hdih : Work.GW2.DihOrCycSylow X)
    (hD : Work.GW2.IsDGroup X) : Work.GW2.fstar X ≠ ⊥ := by
  intro hbot
  rw [Work.GW2.fstar] at hbot
  have hfit : Work.GW2.fitting X = ⊥ := by
    have h := le_sup_left (a := Work.GW2.fitting X) (b := Work.GW2.layer X)
    rw [hbot] at h
    exact le_bot_iff.mp h
  have hlay : Work.GW2.layer X = ⊥ := by
    have h := le_sup_right (a := Work.GW2.fitting X) (b := Work.GW2.layer X)
    rw [hbot] at h
    exact le_bot_iff.mp h
  rcases h16 X hFT hdih hD with hc | hz | hf | ⟨E, hEn, hEq, -⟩
  · -- Case 1: `C_X(F_{2'}(X)) ≤ F_{2'}(X)`.
    have hKne : Work.GW2.fittingPi {2}ᶜ X ≠ ⊥ := by
      intro hK
      rw [hK] at hc
      have hsub : Subsingleton X := by
        constructor
        intro a b
        have ha : a ∈ Subgroup.centralizer (((⊥ : Subgroup X)) : Set X) :=
          Subgroup.mem_centralizer_iff.mpr fun h hh => by
            rw [Subgroup.mem_bot.mp hh]; simp
        have hb : b ∈ Subgroup.centralizer (((⊥ : Subgroup X)) : Set X) :=
          Subgroup.mem_centralizer_iff.mpr fun h hh => by
            rw [Subgroup.mem_bot.mp hh]; simp
        rw [Subgroup.mem_bot.mp (hc ha), Subgroup.mem_bot.mp (hc hb)]
      obtain ⟨a, b, hab⟩ := hnt.exists_pair_ne
      exact hab (hsub.allEq a b)
    have hKle : Work.GW2.fittingPi {2}ᶜ X ≤ Work.GW2.fitting X := by
      rw [Work.GW2.fittingPi]; exact Subgroup.map_subtype_le _
    rw [hfit] at hKle
    exact hKne (le_bot_iff.mp hKle)
  · exact fitting_ne_bot_of_central_involution hz hfit
  · exact fitting_ne_bot_of_isFourGroup_pCore hf.1 hfit
  · exact layer_ne_bot_of_quasisimple_normal hEn hEq hlay

end Work.CORE2A
