import Mathlib
import Submission.Work.CORE3.CosetInvCountLeSix
import Submission.Work.CORE3.Case1bEightNineDefs
import Submission.Work.CORE3.Defs

/-!
# `Work.CORE3.J4.CardDvdSixOfDisjoint`

Bender 1981, §3, subcase `V = O₂(Ĥ)` of type `(2,2)`:  any subgroup `Y ≤ Ĥ` meeting the
characteristic subgroup `VU = O₂(Ĥ) ⊔ O(Ĥ)` trivially has order dividing `6`.

Indeed `VU ⊴ Ĥ` (`Work.CORE3.normal_VU_subgroupOf`) with `|Ĥ : VU| = 6`
(`Work.CORE3.relIndex_VU_Hhat`), so the composite `Y ↪ Ĥ → Ĥ/VU` is injective and exhibits
`|Y|` as the order of a subgroup of the group `Ĥ/VU` of order `6`; Lagrange's theorem finishes.

The hypotheses on `Y` are the natural ones for the application: `Y = Ĥ ⊓ Ĥ^y` (Bender's `D`),
whose order is the quantity `= 6` in step (7).
-/

namespace Work.CORE3.J4

open Subgroup

theorem CardDvdSixOfDisjoint {G : Type} [Group G] [Finite G] (I : Work.CORE3.Case1Inputs)
    (hBc : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B)
    (D : Work.GW2.Case1bData B) (Y : Subgroup G) (hY : Y ≤ B.Hhat)
    (hdisj : Y ⊓ (Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U) = ⊥) :
    Nat.card Y ∣ 6 := by
  -- `VU ⊴ Ĥ` and `|Ĥ : VU| = 6`.
  have hnorm : ((Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U).subgroupOf B.Hhat).Normal :=
    Work.CORE3.normal_VU_subgroupOf G I hBc B h1 D
  have hrel : (Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U).relIndex B.Hhat = 6 :=
    Work.CORE3.relIndex_VU_Hhat G I hBc B h1 D
  let W : Subgroup G := Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U
  let Ys : Subgroup ↥B.Hhat := Y.subgroupOf B.Hhat
  let Ws : Subgroup ↥B.Hhat := W.subgroupOf B.Hhat
  have hWs_normal : Ws.Normal := hnorm
  have hWs_index : Ws.index = 6 := hrel
  have hdisjW : Y ⊓ W = ⊥ := hdisj
  -- `Ws ⊓ Ys = ⊥`, transported from `Y ⊓ W = ⊥`.
  have hinf : Ws ⊓ Ys = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    have hxW : (x : G) ∈ W := Subgroup.mem_subgroupOf.mp hx.1
    have hxY : (x : G) ∈ Y := Subgroup.mem_subgroupOf.mp hx.2
    have hxbot : (x : G) ∈ (⊥ : Subgroup G) := by
      rw [← hdisjW]; exact ⟨hxY, hxW⟩
    exact Subtype.ext (Subgroup.mem_bot.mp hxbot)
  -- `|Y| = |Y Ys| = relIndex Ws Ys`, because `Ws ⊓ Ys = ⊥`.
  have hcardYs : Nat.card ↥Ys = Ws.relIndex Ys := by
    rw [← Subgroup.inf_relIndex_right Ws Ys, hinf, Subgroup.relIndex_bot_left]
  have hYcard : Nat.card ↥Ys = Nat.card Y := by
    have h := Subgroup.card_subtype B.Hhat (Y.subgroupOf B.Hhat)
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hY] at h
    exact h.symm
  -- `Ys` injects into the quotient `Ĥ/VU` of order `6`.
  let q : ↥B.Hhat →* (↥B.Hhat) ⧸ Ws := QuotientGroup.mk' Ws
  have hrelker : Ws.relIndex Ys = Nat.card ↥(Ys.map q) := by
    rw [← Subgroup.relIndex_ker Ys q, QuotientGroup.ker_mk']
  have hdvd : Nat.card ↥(Ys.map q) ∣ 6 := by
    rw [← hrelker, ← hWs_index]
    exact Subgroup.relIndex_dvd_index_of_normal Ws Ys
  rw [← hYcard, hcardYs, hrelker]
  exact hdvd

end Work.CORE3.J4
