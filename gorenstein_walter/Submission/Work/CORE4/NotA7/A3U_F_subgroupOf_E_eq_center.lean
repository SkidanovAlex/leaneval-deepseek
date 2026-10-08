/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area CORE4, `Work.CORE4`)

# `F = Z(E(M))` in the `A₇` case (Bender §4, p. 226)

In the §4 configuration, with `E = E(M) = layerIn D.M` the layer of `M` and `F = D.F` Bender's
cyclic subgroup of order `3`, the identity `oddCoreIn D.M = D.F` (`O(M) = F`) forces

    `F ⊓ E = Z(E)`,   equivalently   `F.subgroupOf E = center ↥E`.

Indeed `Z(E)` is a normal subgroup of `M` of odd order (`LayerCtx6`), hence
`Z(E) ≤ O(M) = F` (maximality of `oddCoreIn`, `le_oddCoreIn_of_normal_of_odd_aux`); and
conversely `F ≤ C_G(E)` (`Case2Pre.F_cent`) so `F ⊓ E ≤ Z(E)`.
-/
import Mathlib
import Submission.Work.CORE4.NotA7Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.LayerCtx6
import Submission.Work.CORE4.DihOrCycSub
import Submission.Work.CORE4.NotA7.A3UOddCore

namespace Work.CORE4.NotA7

open Subgroup

/-- **The centre of a normal subgroup is normal.**  If `E ≤ M` and `E` is normal in `M`, then the
centre of `E` (regarded as a subgroup of the ambient group `G`) is normal in `M`.

Element chase: for `m ∈ M` and `z ∈ Z(E)`, the conjugate `m z m⁻¹` lies in `E` (normality of `E`)
and is again central, because for `w ∈ E` the element `m⁻¹ w m ∈ E` commutes with `z`. -/
theorem center_map_subgroupOf_normal {G : Type} [Group G] {M E : Subgroup G}
    (hEM : E ≤ M) (hEn : (E.subgroupOf M).Normal) :
    (((Subgroup.center ↥E).map E.subtype).subgroupOf M).Normal := by
  have hconj : ∀ (m v : G), m ∈ M → v ∈ E → m * v * m⁻¹ ∈ E := by
    intro m v hm hv
    have h1 := hEn.conj_mem (⟨v, hEM hv⟩ : ↥M) (Subgroup.mem_subgroupOf.mpr hv) (⟨m, hm⟩ : ↥M)
    simpa using Subgroup.mem_subgroupOf.mp h1
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_map] at hn ⊢
  obtain ⟨z, hzcen, hz⟩ := hn
  have hzE : (z : G) ∈ E := z.2
  have hcomm : ∀ w : G, w ∈ E → w * (z : G) = (z : G) * w :=
    fun w hw => congrArg Subtype.val (Subgroup.mem_center_iff.mp hzcen (⟨w, hw⟩ : ↥E))
  refine ⟨⟨(g : G) * (z : G) * (g : G)⁻¹, hconj (g : G) (z : G) g.2 hzE⟩, ?_, ?_⟩
  · rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hy : (g : G)⁻¹ * (y : G) * (g : G) ∈ E := by
      simpa using hconj (g : G)⁻¹ (y : G) (M.inv_mem g.2) y.2
    have h1 := hcomm _ hy
    show (y : G) * ((g : G) * (z : G) * (g : G)⁻¹) = ((g : G) * (z : G) * (g : G)⁻¹) * (y : G)
    rw [show (y : G) * ((g : G) * (z : G) * (g : G)⁻¹)
          = (g : G) * (((g : G)⁻¹ * (y : G) * (g : G)) * (z : G)) * (g : G)⁻¹ from by
        group, h1]
    group
  · show (g : G) * (z : G) * (g : G)⁻¹ = (g : G) * ↑n * (g : G)⁻¹
    rw [show (z : G) = (n : G) from hz]

/-- **C10.A3' part 3, companion: `F = Z(E(M))`.**  With `E = E(M) = layerIn C.D.M`, `F = C.D.F`
and `O(M) = F` (`oddCoreIn C.D.M = C.D.F`), the subgroup `F` cut down to `E` is exactly the
centre of `E`: `F.subgroupOf E = center ↥E`.

* `Z(E) ≤ F`: `Z(E) ≤ E ≤ M` is normal in `M` (`center_map_subgroupOf_normal`) and of odd order
  (`LayerCtx6`), so it lies in `O(M) = F` by maximality of `oddCoreIn`.
* `F ⊓ E ≤ Z(E)`: `F ≤ C_G(E)` (`Case2Pre.F_cent`). -/
theorem A3U_F_subgroupOf_E_eq_center (I : Work.GW2.C4Inputs) : ∀ (G : Type) [Group G] [Finite G]
    (B : Work.GW2.BenderSetup G) (C : Work.GW2.Case2Ctx6 B),
    Work.GW2.Hyp9 G B C → Work.GW2.A7Facts1 C.D → Work.GW2.A7Facts2 B C.D →
    Work.GW2.oddCoreIn C.D.M = C.D.F →
      C.D.F.subgroupOf (Work.GW2.layerIn C.D.M) = Subgroup.center ↥(Work.GW2.layerIn C.D.M) := by
  intro G _ _ B C hHyp _h1 _h2 hcore
  obtain ⟨hbc, -⟩ := hHyp
  set E : Subgroup G := Work.GW2.layerIn C.D.M with hEdef
  set Z : Subgroup G := (Subgroup.center ↥E).map E.subtype with hZdef
  -- `E ≤ M`
  have hEM : E ≤ C.D.M := by
    rw [hEdef, Work.GW2.layerIn]
    exact Subgroup.map_subtype_le _
  -- `E` is normal in `M`
  have hEn : (E.subgroupOf C.D.M).Normal := by
    have h1 : E.subgroupOf C.D.M = Work.GW2.layer ↥C.D.M := by
      rw [hEdef, Work.GW2.layerIn, Subgroup.subgroupOf]
      exact Subgroup.comap_map_eq_self_of_injective C.D.M.subtype_injective _
    rw [h1, Work.GW2.layer]
    exact Subgroup.sSup_normal _ (fun _ hH => hH.1)
  -- `|Z|` is odd
  have hZodd : Odd (Nat.card Z) := by
    rw [hZdef, Subgroup.card_map_of_injective (f := E.subtype) (Subgroup.subtype_injective E),
      hEdef]
    exact (Work.CORE4.LayerCtx6 I hbc C (Work.CORE4.DihOrCycSub hbc.sylow C.D.M)).2.1
  -- `Z ≤ M`
  have hZM : Z ≤ C.D.M := by
    rw [hZdef]
    exact le_trans (Subgroup.map_subtype_le (Subgroup.center ↥E)) hEM
  -- `Z` is normal in `M`
  have hZnorm : (Z.subgroupOf C.D.M).Normal := by
    rw [hZdef]
    exact center_map_subgroupOf_normal hEM hEn
  -- `Z ≤ F` by maximality of `O(M) = F`
  have hZleF : Z ≤ C.D.F := by
    have h := le_oddCoreIn_of_normal_of_odd_aux (X := Z) (M := C.D.M) hZM hZnorm hZodd
    rwa [hcore] at h
  -- `F ≤ C_G(E)`
  have hFcent : C.D.F ≤ Subgroup.centralizer (E : Set G) := by
    rw [hEdef]
    exact Work.GW2.Case2Pre.F_cent B C.D C.pre
  -- the key identity `F ⊓ E = Z(E)`
  have hFintE : C.D.F ⊓ E = Z := by
    refine le_antisymm ?_ ?_
    · intro x hx
      obtain ⟨hxF, hxE⟩ := Subgroup.mem_inf.mp hx
      rw [hZdef, Subgroup.mem_map]
      refine ⟨⟨x, hxE⟩, ?_, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      show (y : G) * x = x * (y : G)
      exact Subgroup.mem_centralizer_iff.mp (hFcent hxF) (y : G) y.2
    · intro x hx
      rw [hZdef] at hx
      exact ⟨hZleF hx, Subgroup.map_subtype_le (Subgroup.center ↥E) hx⟩
  have hmap : (C.D.F.subgroupOf E).map E.subtype = (Subgroup.center ↥E).map E.subtype := by
    rw [Subgroup.subgroupOf_map_subtype, hFintE, hZdef]
  exact Subgroup.map_injective (Subgroup.subtype_injective E) hmap

end Work.CORE4.NotA7
