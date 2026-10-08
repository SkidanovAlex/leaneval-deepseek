/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area CORE4, `Work.CORE4`)

# CORE4 — `F_{π}` transfers to a subgroup

`Work.GW2.fittingPiIn π K = (Work.GW2.fittingPi π ↥K).map K.subtype` realises `F_π(K)` inside
an ambient group `X`.  For `H ≤ Y ≤ X` the forgetful isomorphism
`Subgroup.subgroupOfEquivOfLe hHY : ↥(H.subgroupOf Y) ≃* ↥H` identifies the `π`-part of the
Fitting subgroup of the abstract group `↥H` with that of the abstract group `↥(H.subgroupOf Y)`.

The group-level input is `Work.CORE4.KFP.fittingPi_map_le_of_surjective` (from `Transport.lean`).
-/
import Mathlib
import Submission.Work.CORE4.KFP.Transport

open scoped MatrixGroups

namespace Work.CORE4.KFP

open Subgroup

/-- **`F_π` is preserved by a group isomorphism.** -/
theorem fittingPi_map_mulEquiv {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (e : G ≃* H) (π : Set ℕ) :
    (Work.GW2.fittingPi π G).map (e : G →* H) = Work.GW2.fittingPi π H := by
  refine le_antisymm
    (fittingPi_map_le_of_surjective (e : G →* H) e.surjective π) ?_
  have h := fittingPi_map_le_of_surjective (e.symm : H →* G) e.symm.surjective π
  have h2 := Subgroup.map_mono (f := (e : G →* H)) h
  have e2 : ((Work.GW2.fittingPi π H).map (e.symm : H →* G)).map (e : G →* H)
      = Work.GW2.fittingPi π H := by
    rw [Subgroup.map_map]
    have : (e : G →* H).comp (e.symm : H →* G) = MonoidHom.id H := by ext x; simp
    rw [this, Subgroup.map_id]
  rwa [e2] at h2

/-- The `2'`-part of the Fitting subgroup transfers to a subgroup: if `H ≤ Y ≤ X` and
`x ∈ H ∩ F_{2'}(H)`, then `x`, viewed inside `↥Y`, lies in `F_{2'}(H.subgroupOf Y)`. -/
theorem fittingPiIn_subgroupOf {X : Type*} [Group X] [Finite X]
    (H Y : Subgroup X) (hHY : H ≤ Y) (x : X) (hxH : x ∈ H)
    (hx : x ∈ Work.GW2.fittingPiIn {n : ℕ | n ≠ 2} H) :
    (⟨x, hHY hxH⟩ : ↥Y) ∈ Work.GW2.fittingPiIn {n : ℕ | n ≠ 2} (H.subgroupOf Y) := by
  simp only [Work.GW2.fittingPiIn] at hx ⊢
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
  have hyx' : (y : X) = x := hyx
  let e : ↥(H.subgroupOf Y) ≃* ↥H := Subgroup.subgroupOfEquivOfLe hHY
  have hkey : (Work.GW2.fittingPi {n : ℕ | n ≠ 2} ↥H).map
        (e.symm : ↥H →* ↥(H.subgroupOf Y)) = Work.GW2.fittingPi {n : ℕ | n ≠ 2} ↥(H.subgroupOf Y) :=
    fittingPi_map_mulEquiv e.symm {n : ℕ | n ≠ 2}
  have hzmem : e.symm y ∈ Work.GW2.fittingPi {n : ℕ | n ≠ 2} ↥(H.subgroupOf Y) := by
    rw [← hkey]
    exact Subgroup.mem_map_of_mem (e.symm : ↥H →* ↥(H.subgroupOf Y)) hy
  have hzval : (((e.symm y : ↥(H.subgroupOf Y)) : ↥Y) : X) = x := by
    have h1 := Subgroup.subgroupOfEquivOfLe_apply_coe hHY (e.symm y)
    have h2 : ((e (e.symm y) : ↥H) : X) = x := by
      rw [MulEquiv.apply_symm_apply]
      exact hyx'
    rw [h2] at h1
    exact h1.symm
  exact Subgroup.mem_map.mpr ⟨e.symm y, hzmem, Subtype.ext hzval⟩

end Work.CORE4.KFP
