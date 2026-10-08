/-
Copyright (c) 2026 gorenstein_walter team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CORE2A area (fundmath3-gorenstein_walter)

# CORE2A: layer facts for `Thm26bOneClass` (Bender 1981 p. 220)

The *vocabulary* (Bender's `zE`, `cE`, `SE`, `torusR`, `kE`, `Lsub`, `mTor`, `kTor`, `PGLData`,
`Thm26bAutProp`) lives in `Submission/Work/CORE2A/TorusDefs.lean` (namespace `Work.GW2`).
This file adds the facts about the **layer** `E(Ĥ)` that every leaf of the proof of
`Work.GW2.Thm26bTorusProp` needs:

* `layerOneInvClass_inst` — involutions of a normal quasisimple subgroup of a `D`-group are all
  conjugate (`Work.DSTR.LayerOneInvClassProp`);
* `exists_normal_quasisimple_of_layerIn_ne_bot`, `exists_layer_eq` — a nontrivial layer is a
  single normal quasisimple subgroup `E` with `layer ↥Ĥ = E`;
* `layerIn_normal` — `E(Ĥ)` is normalized by `Ĥ`;
* `card_zE_eq`, `zE_odd` — `|Z(E(Ĥ))|` is odd (`T.lay`);
* subgroup/coercion bookkeeping.
-/

import Mathlib
import Submission.Work.CORE2A.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE2A.TorusDefs
import Submission.Work.CORE2A.Thm26bPGL
import Submission.Work.L2F.Defs
import Submission.Work.DSTR.dihOrCycHered
import Submission.Work.DSTR.dihedralSubgroup
import Submission.Work.DSTR.dihedralQuotient
import Submission.Work.DSTR.quasisimpleSylow
import Submission.Work.DSTR.layerOneInvClass
import Submission.Work.FUS.Fusion

open scoped MatrixGroups
open scoped commutatorElement

namespace Work.CORE2A

open Subgroup
open Work.GW2

variable {G : Type} [Group G] [Finite G]

/-! ## Trivial consequences of the vocabulary -/

section Basic

variable {B : BenderSetup G}

theorem zE_le : zE B ≤ layerIn B.Hhat := Subgroup.map_subtype_le _

theorem SE_le_Hhat : SE B ≤ B.Hhat :=
  sup_le (bSetup_S_le_Hhat B) (Subgroup.map_subtype_le _)

theorem S_le_SE : (B.S : Subgroup G) ≤ SE B := le_sup_left

theorem layerIn_le_SE : layerIn B.Hhat ≤ SE B := le_sup_right

theorem mem_SE_of_mem_layerIn {x : G} (h : x ∈ layerIn B.Hhat) : x ∈ SE B :=
  layerIn_le_SE h

theorem mem_SE_of_mem_S {x : G} (h : x ∈ (B.S : Subgroup G)) : x ∈ SE B :=
  S_le_SE h

theorem cE_le : cE B ≤ B.Hhat := inf_le_left

end Basic

/-! ## Shared facts about the layer of `Ĥ` -/

section Layer

/-- `LayerOneInvClassProp` from the area `DSTR`. -/
theorem layerOneInvClass_inst : LayerOneInvClassProp :=
  Work.DSTR.layerOneInvClass
    (Work.DSTR.dihOrCycHered Work.DSTR.dihedralSubgroup Work.DSTR.dihedralQuotient)
    Work.DSTR.quasisimpleSylow Work.FUS.involutionFusionProp

/-- A nontrivial layer contains a normal quasisimple subgroup. -/
theorem exists_normal_quasisimple_of_layerIn_ne_bot {K : Subgroup G} (h : layerIn K ≠ ⊥) :
    ∃ E : Subgroup ↥K, E.Normal ∧ IsQuasisimple E := by
  by_contra hcon
  have hempty : {E : Subgroup ↥K | E.Normal ∧ IsQuasisimple E} = ∅ := by
    ext E
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨h1, h2⟩
    exact hcon ⟨E, h1, h2⟩
  refine h ?_
  show (layer ↥K).map K.subtype = ⊥
  rw [layer, hempty, sSup_empty, Subgroup.map_bot]

/-- The image of a subgroup of `↥K` under `K.subtype`, intersected with `K`, is itself. -/
theorem subgroupOf_map_subtype_eq (K : Subgroup G) (E : Subgroup ↥K) :
    ((E.map K.subtype).subgroupOf K) = E := by
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_subgroupOf] at hx
    obtain ⟨e, he, hex⟩ := Subgroup.mem_map.mp hx
    have h1 : e = x := Subtype.ext hex
    rwa [h1] at he
  · intro hx
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩

/-- The order of an element of a subgroup, computed in the ambient group. -/
theorem orderOf_coe_subtype_eq (K : Subgroup G) (x : ↥K) :
    orderOf x = orderOf ((x : G)) :=
  Subgroup.orderOf_mk (H := K) (a := (x : G)) x.2

/-- `Ĥ` is a `D`-group, and `layer (↥Ĥ) = E` for any normal quasisimple `E ≤ ↥Ĥ`. -/
theorem exists_layer_eq (T : LocalToolkit) (hFT : FeitThompsonProp) (hbc : BenderCtx G)
    (B : BenderSetup G) (hE : layerIn B.Hhat ≠ ⊥) :
    ∃ E : Subgroup ↥B.Hhat, E.Normal ∧ IsQuasisimple E ∧ layer ↥B.Hhat = E ∧
      Odd (Nat.card ↥(Subgroup.center ↥E)) ∧ layerIn B.Hhat = E.map B.Hhat.subtype := by
  obtain ⟨E, hEnorm, hEquasi⟩ := exists_normal_quasisimple_of_layerIn_ne_bot (K := B.Hhat) hE
  have hhat_lt : Nat.card ↥B.Hhat < Nat.card G := by
    have hdvd : Nat.card ↥B.Hhat ∣ Nat.card G := Subgroup.card_subgroup_dvd_card _
    have hle : Nat.card ↥B.Hhat ≤ Nat.card G := Nat.le_of_dvd Nat.card_pos hdvd
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exact absurd (Subgroup.eq_top_of_card_eq B.Hhat h) B.Hhat_coatom.ne_top
  have hhered : DihOrCycHeredProp :=
    Work.DSTR.dihOrCycHered Work.DSTR.dihedralSubgroup Work.DSTR.dihedralQuotient
  have hsyHhat : DihOrCycSylow ↥B.Hhat := (hhered G hbc.sylow).1 B.Hhat
  have hDGHat : IsDGroup ↥B.Hhat := hbc.ih ↥B.Hhat hhat_lt hsyHhat
  obtain ⟨hlayer, hZodd, -⟩ := T.lay ↥B.Hhat hFT hsyHhat hDGHat E hEnorm hEquasi
  exact ⟨E, hEnorm, hEquasi, hlayer, hZodd, by rw [layerIn, hlayer]⟩

/-- The centre of the layer, computed from a chosen normal quasisimple `E` with `layer = E`. -/
theorem card_zE_eq (B : BenderSetup G) (E : Subgroup ↥B.Hhat) (h : layer ↥B.Hhat = E) :
    Nat.card (zE B) = Nat.card ↥(Subgroup.center ↥E) := by
  have hf : Function.Injective B.Hhat.subtype := Subtype.coe_injective
  have hlayerIn : layerIn B.Hhat = E.map B.Hhat.subtype := by rw [layerIn, h]
  set e := Subgroup.equivMapOfInjective E B.Hhat.subtype hf with he
  have h1 : Subgroup.center ↥(E.map B.Hhat.subtype) =
      (Subgroup.center ↥E).map e.toMonoidHom :=
    (Subgroup.map_center_eq e).symm
  show Nat.card ↥((Subgroup.center ↥(layerIn B.Hhat)).map (layerIn B.Hhat).subtype) =
    Nat.card ↥(Subgroup.center ↥E)
  rw [hlayerIn, h1]
  rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective (E.map B.Hhat.subtype))]
  exact Subgroup.card_map_of_injective e.injective

theorem zE_odd (T : LocalToolkit) (hFT : FeitThompsonProp) (hbc : BenderCtx G)
    (B : BenderSetup G) (hE : layerIn B.Hhat ≠ ⊥) : Odd (Nat.card (zE B)) := by
  obtain ⟨E, -, -, hlayer, hZodd, -⟩ := exists_layer_eq T hFT hbc B hE
  rw [card_zE_eq B E hlayer]
  exact hZodd

/-- `layerIn B.Hhat = E(Ĥ)` is normalized by `Ĥ`. -/
theorem layerIn_normal (T : LocalToolkit) (hFT : FeitThompsonProp) (hbc : BenderCtx G)
    (B : BenderSetup G) (hE : layerIn B.Hhat ≠ ⊥) :
    ∀ h ∈ B.Hhat, ∀ x ∈ layerIn B.Hhat, h * x * h⁻¹ ∈ layerIn B.Hhat := by
  obtain ⟨E, hEnorm, -, -, -, hlayerIn⟩ := exists_layer_eq T hFT hbc B hE
  haveI : E.Normal := hEnorm
  intro h hh x hx
  rw [hlayerIn] at hx ⊢
  obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.mp hx
  refine Subgroup.mem_map.mpr ⟨⟨h, hh⟩ * e * ⟨h, hh⟩⁻¹, ?_, rfl⟩
  exact hEnorm.conj_mem e he ⟨h, hh⟩

end Layer

end Work.CORE2A
