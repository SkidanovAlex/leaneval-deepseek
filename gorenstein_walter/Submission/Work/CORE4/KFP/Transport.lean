/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area CORE4, `Work.CORE4`)

# CORE4 — transport of `F_{π}` along surjective homomorphisms

This is the CORE4 (self-contained vocabulary) copy of the transport results for the
`π`-part `F_π(G) = O_π(F(G))` of the Fitting subgroup.  Area CORE4 keeps its own copies of
the `Work.GW2` vocabulary (`Submission.Work.CORE4.Defs`), so the modules of the other areas
(which all re-export `Submission.Work.ASM.Defs`) cannot be imported here; the results are
therefore restated and reproved in this area's vocabulary.

For a surjective homomorphism `f : G →* H` of finite groups and a subgroup `K ≤ G`, the image
of `F_{2'}(K)` (realised inside `G`) lies in `F_{2'}` of the image of `K`.

The mathematics is identical to `Submission.Work.DSTR.map_fittingPiIn_le`:

* `O_π(-)` is characteristic and is a `π`-subgroup (read off from the odd-order library's
  `oPiCore` via `piCore_eq_oPiCore`);
* the image of a `π`-subgroup is a `π`-subgroup;
* a normal `π`-subgroup of a group `M` that lies in a subgroup `K ≤ M` lies in the image of
  `O_π(K)`;
* `F(-)` is transported by surjective homomorphisms.
-/
import Mathlib
import Submission.Work.CORE4.Defs
import Submission.OddOrder.Isaacs.Ch03_SplitExtensions.Theorem315

open scoped MatrixGroups

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.CORE4.KFP

open Subgroup

/-! ## 1. Local vocabulary bridges -/

/-- `F(G)` in the contract's sense is Isaacs' Fitting subgroup. -/
theorem fitting_eq_isaacsFitting {G : Type*} [Group G] [Finite G] :
    Work.GW2.fitting G = OddOrder.Isaacs.Ch01.fitting G := by
  have hS : sSup {N : Subgroup G | N.Normal ∧ Group.IsNilpotent N}
      = OddOrder.Isaacs.Ch01.fitting G := by
    refine le_antisymm (sSup_le ?_) (le_sSup ?_)
    · rintro N ⟨hN, hnil⟩
      haveI : N.Normal := hN
      haveI : Group.IsNilpotent ↥N := hnil
      exact OddOrder.Isaacs.Ch01.nilpotent_normal_le_fitting
    · exact ⟨OddOrder.Isaacs.Ch01.fitting.normal G,
        OddOrder.Isaacs.Ch01.fitting.isNilpotent⟩
  rw [Work.GW2.fitting, hS]
  exact Subgroup.normalCore_eq_self _

/-- `O_π(G)` in the contract's sense is the library's `oPiCore`. -/
theorem piCore_eq_oPiCore {G : Type*} [Group G] (π : Set ℕ) :
    Work.GW2.piCore π G = OddOrder.Isaacs.Ch03.oPiCore π G := by
  apply le_antisymm
  · refine (Subgroup.normalCore_le _).trans ?_
    refine sSup_le ?_
    rintro N ⟨hN, hpi⟩
    exact le_iSup (fun H : {H : Subgroup G // H.Normal ∧
      OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup π H} => (H.val : Subgroup G)) ⟨N, hN, hpi⟩
  · refine Subgroup.normal_le_normalCore.mpr ?_
    exact iSup_le fun H => le_sSup H.property

/-- `O_π(G)` is characteristic in `G`. -/
theorem piCore_characteristic {G : Type*} [Group G] (π : Set ℕ) :
    (Work.GW2.piCore π G).Characteristic := by
  rw [piCore_eq_oPiCore π]
  infer_instance

/-- `O_π(G)` is a `π`-subgroup. -/
theorem isPiSubgroup_piCore {G : Type*} [Group G] [Finite G] (π : Set ℕ) :
    Subgroup.IsPiSubgroup π (Work.GW2.piCore π G) := by
  rw [piCore_eq_oPiCore π]
  exact OddOrder.Isaacs.Ch03.oPiCore.isPiGroup (G := G) π

/-- The image of a `π`-subgroup under any homomorphism is a `π`-subgroup. -/
theorem isPiSubgroup_map {G H : Type*} [Group G] [Finite G] [Group H] {f : G →* H} {π : Set ℕ}
    {N : Subgroup G} (h : Subgroup.IsPiSubgroup π N) :
    Subgroup.IsPiSubgroup π (N.map f) := fun p hp =>
  h p (Nat.primeFactors_mono (Subgroup.card_map_dvd N f) Nat.card_pos.ne' hp)

/-- **Universal property of `O_π(G)`.** Every normal `π`-subgroup lies in `piCore π G`. -/
theorem le_piCore_of_normal_isPiSubgroup {G : Type*} [Group G] {π : Set ℕ} {N : Subgroup G}
    [N.Normal] (hN : Subgroup.IsPiSubgroup π N) : N ≤ Work.GW2.piCore π G :=
  Subgroup.normal_le_normalCore.mpr (le_sSup ⟨‹N.Normal›, hN⟩)

/-- If a normal `π`-subgroup `N` of a group `M` lies in a subgroup `K ≤ M`, then `N` lies in
the image of `O_π(K)` in `M`. -/
theorem le_map_piCore_of_le_of_normal {M : Type*} [Group M] (π : Set ℕ) {K N : Subgroup M}
    (hNK : N ≤ K) [N.Normal] (hNpi : Subgroup.IsPiSubgroup π N) :
    N ≤ (Work.GW2.piCore π K).map K.subtype := by
  intro x hx
  refine ⟨⟨x, hNK hx⟩, ?_, rfl⟩
  haveI hNn : N.Normal := inferInstance
  haveI : (N.comap K.subtype).Normal := hNn.comap K.subtype
  have hcard : Nat.card ↥(N.comap K.subtype) = Nat.card ↥N := by
    have h1 : Nat.card ↥((N.comap K.subtype).map K.subtype) = Nat.card ↥(N.comap K.subtype) :=
      Subgroup.card_map_of_injective K.subtype_injective
    have h2 : (N.comap K.subtype).map K.subtype = N :=
      Subgroup.map_comap_eq_self (by rw [Subgroup.range_subtype]; exact hNK)
    rw [h2] at h1
    exact h1.symm
  have hpi : Subgroup.IsPiSubgroup π (N.comap K.subtype) := fun p hp => hNpi p (hcard ▸ hp)
  exact le_piCore_of_normal_isPiSubgroup hpi (Subgroup.mem_comap.mpr hx)

/-! ## 2. Two images: `F(-)` and the `π`-part of `F(-)` -/

/-- The range of `φ` restricted to a subgroup `A` is the image of `A`. -/
theorem range_comp_subtype {K L : Type*} [Group K] [Group L] (φ : K →* L) (A : Subgroup K) :
    (φ.comp A.subtype).range = A.map φ := by
  rw [MonoidHom.range_eq_map, ← Subgroup.map_map, Subgroup.map_top, Subgroup.range_subtype]

/-- The image of the Fitting subgroup of a finite group under a surjective homomorphism lies
in the Fitting subgroup of the image. -/
theorem fitting_map_le_of_surjective {K L : Type*} [Group K] [Finite K] [Group L] [Finite L]
    (φ : K →* L) (hφ : Function.Surjective φ) :
    (Work.GW2.fitting K).map φ ≤ Work.GW2.fitting L := by
  rw [fitting_eq_isaacsFitting (G := K), fitting_eq_isaacsFitting (G := L)]
  haveI hnil : Group.IsNilpotent
      ↥((φ.comp (OddOrder.Isaacs.Ch01.fitting K).subtype).range) :=
    Group.nilpotent_of_mulEquiv
      (QuotientGroup.quotientKerEquivRange (φ.comp (OddOrder.Isaacs.Ch01.fitting K).subtype))
  haveI hnorm : ((φ.comp (OddOrder.Isaacs.Ch01.fitting K).subtype).range).Normal := by
    rw [range_comp_subtype]
    exact (OddOrder.Isaacs.Ch01.fitting.normal K).map φ hφ
  rw [← range_comp_subtype φ (OddOrder.Isaacs.Ch01.fitting K)]
  exact OddOrder.Isaacs.Ch01.nilpotent_normal_le_fitting

/-- **Group-level form.** For a surjective homomorphism `φ : K →* L` of finite groups and any
set of primes `π`, the image of `F_π(K) = O_π(F(K))` lies in `F_π(L)`. -/
theorem fittingPi_map_le_of_surjective {K L : Type*} [Group K] [Finite K] [Group L] [Finite L]
    (φ : K →* L) (hφ : Function.Surjective φ) (π : Set ℕ) :
    (Work.GW2.fittingPi π K).map φ ≤ Work.GW2.fittingPi π L := by
  show Subgroup.map φ (Subgroup.map (Work.GW2.fitting K).subtype
        (Work.GW2.piCore π ↥(Work.GW2.fitting K)))
      ≤ Subgroup.map (Work.GW2.fitting L).subtype
        (Work.GW2.piCore π ↥(Work.GW2.fitting L))
  rw [Subgroup.map_map]
  haveI hchar : (Work.GW2.piCore π ↥(Work.GW2.fitting K)).Characteristic :=
    piCore_characteristic (G := ↥(Work.GW2.fitting K)) π
  haveI hAnorm : (Work.GW2.fitting K).Normal := by
    rw [fitting_eq_isaacsFitting (G := K)]
    exact OddOrder.Isaacs.Ch01.fitting.normal K
  have hcoreNormal : (Subgroup.map (Work.GW2.fitting K).subtype
      (Work.GW2.piCore π ↥(Work.GW2.fitting K))).Normal :=
    ConjAct.normal_of_characteristic_of_normal
  haveI hNnorm : (Subgroup.map (φ.comp (Work.GW2.fitting K).subtype)
      (Work.GW2.piCore π ↥(Work.GW2.fitting K))).Normal := by
    rw [← Subgroup.map_map]
    exact hcoreNormal.map φ hφ
  have hlea : Subgroup.map (φ.comp (Work.GW2.fitting K).subtype)
      (Work.GW2.piCore π ↥(Work.GW2.fitting K)) ≤ Work.GW2.fitting L := by
    rintro x ⟨a, -, rfl⟩
    exact fitting_map_le_of_surjective φ hφ (Subgroup.mem_map_of_mem φ a.2)
  have hNpi : Subgroup.IsPiSubgroup π (Subgroup.map (φ.comp (Work.GW2.fitting K).subtype)
      (Work.GW2.piCore π ↥(Work.GW2.fitting K))) :=
    isPiSubgroup_map (isPiSubgroup_piCore (G := ↥(Work.GW2.fitting K)) π)
  exact le_map_piCore_of_le_of_normal π hlea hNpi

/-! ## 3. The `2'`-part, for a subgroup -/

/-- For a surjective homomorphism of finite groups, the image of `F_{2'}(K)` is contained in
`F_{2'}` of the image of `K`. -/
theorem map_fittingPiIn_le {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (f : G →* H) (hf : Function.Surjective f) (K : Subgroup G) :
    (Work.GW2.fittingPiIn {n : ℕ | n ≠ 2} K).map f
      ≤ Work.GW2.fittingPiIn {n : ℕ | n ≠ 2} (K.map f) := by
  let φ : ↥K →* ↥(K.map f) :=
    (f.comp K.subtype).codRestrict (K.map f) (fun x => Subgroup.mem_map_of_mem f x.2)
  have hφ : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, Subtype.ext rfl⟩
  have hcomp : f.comp K.subtype = (K.map f).subtype.comp φ := by
    ext x
    rfl
  have hstep : (Work.GW2.fittingPiIn {n : ℕ | n ≠ 2} K).map f
      = ((Work.GW2.fittingPi {n : ℕ | n ≠ 2} ↥K).map φ).map (K.map f).subtype := by
    show Subgroup.map f (Subgroup.map K.subtype
          (Work.GW2.fittingPi {n : ℕ | n ≠ 2} ↥K))
        = Subgroup.map (K.map f).subtype
          (Subgroup.map φ (Work.GW2.fittingPi {n : ℕ | n ≠ 2} ↥K))
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map]
  rw [hstep]
  show Subgroup.map (K.map f).subtype
        (Subgroup.map φ (Work.GW2.fittingPi {n : ℕ | n ≠ 2} ↥K))
      ≤ Subgroup.map (K.map f).subtype
        (Work.GW2.fittingPi {n : ℕ | n ≠ 2} ↥(K.map f))
  exact Subgroup.map_mono (fittingPi_map_le_of_surjective φ hφ {n : ℕ | n ≠ 2})

end Work.CORE4.KFP
