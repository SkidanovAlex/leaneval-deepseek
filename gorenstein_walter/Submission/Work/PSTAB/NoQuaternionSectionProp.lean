/-
Copyright (c) 2026 gorenstein_walter team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PSTAB area (fundmath3-gorenstein_walter)
-/
import Mathlib
import Submission.Work.PSTAB.NoQuatBase

set_option autoImplicit false

open scoped MatrixGroups
open Subgroup

/-!
# `Work.GW2.NoQuaternionSectionProp`

A finite group whose Sylow `2`-subgroups are cyclic or dihedral has no section that is a
noncyclic `2`-group with a unique involution.

Section bookkeeping: a `2`-subgroup `Q` of a section `K/N` is contained in a Sylow
`2`-subgroup of `K/N`, which is the image of a Sylow `2`-subgroup `S` of `K`; `S` lies in a
Sylow `2`-subgroup `S₀` of `X`, to which `Work.GW2.DihOrCycSylow` applies.  The image
`S.map (mk' N)` then has the weak shape `Work.PSTAB.DihCycShape`, and the `2`-subgroup
computation `Work.PSTAB.noUniqueInv_of_dihCycShape` finishes.
-/

namespace Work.PSTAB

end Work.PSTAB

namespace Work.GW2

open Work.PSTAB

/-- **`NoQuaternionSectionProp`** (design2 §3 Step 1). -/
theorem noQuaternionSectionProp : NoQuaternionSectionProp := by
  intro X _ _ hD K N _ Q hQ2 hQnc huniq
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- a Sylow 2-subgroup of the section `K ⧸ N` containing `Q`
  obtain ⟨P, hQP⟩ := IsPGroup.exists_le_sylow (P := Q) hQ2
  -- any Sylow of `K ⧸ N` is the image of a Sylow of `K`
  obtain ⟨S, hSP⟩ := Sylow.mapSurjective_surjective (f := QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective N) 2 P
  have hPcoe : (P : Subgroup (↥K ⧸ N)) = (S : Subgroup ↥K).map (QuotientGroup.mk' N) := by
    rw [← hSP, Sylow.coe_mapSurjective]
  -- `S` lies in a Sylow of `X`
  obtain ⟨S₀, hS₀⟩ := IsPGroup.exists_le_sylow (S.isPGroup'.map K.subtype)
  -- the shape of that Sylow, descending to `S` and then to its image in `K ⧸ N`
  have hshape₀ : DihCycShape ↥((S₀ : Subgroup X)) :=
    dihCycShape_of_isCyclicOrDihedral (hD S₀)
  have hsub : DihCycShape ↥(((S : Subgroup ↥K).map K.subtype).subgroupOf (S₀ : Subgroup X)) :=
    DihCycShapeSubgroup hshape₀ _
  have hshape₁ : DihCycShape ↥((S : Subgroup ↥K).map K.subtype) :=
    dihCycShape_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hS₀) hsub
  have hshape₂ : DihCycShape ↥(S : Subgroup ↥K) :=
    dihCycShape_of_mulEquiv
      (Subgroup.equivMapOfInjective (S : Subgroup ↥K) K.subtype
        (Subgroup.subtype_injective K)).symm hshape₁
  let ψ : ↥(S : Subgroup ↥K) →* ↥((S : Subgroup ↥K).map (QuotientGroup.mk' N)) :=
    ((QuotientGroup.mk' N).comp (S : Subgroup ↥K).subtype).codRestrict
      ((S : Subgroup ↥K).map (QuotientGroup.mk' N))
      (fun x => Subgroup.mem_map_of_mem _ x.2)
  have hψsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨x, hx, hxy⟩ := y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hshape₃ : DihCycShape ↥((S : Subgroup ↥K).map (QuotientGroup.mk' N)) :=
    DihCycShapeSurjective hshape₂ ψ hψsurj
  rw [hPcoe] at hQP
  -- `Q` as a subgroup of `↥P`, transported along `Q.subgroupOf P ≃* Q`
  let e : ↥(Q.subgroupOf ((S : Subgroup ↥K).map (QuotientGroup.mk' N))) ≃*
      ↥Q := Subgroup.subgroupOfEquivOfLe hQP
  have hQp : IsPGroup 2 ↥(Q.subgroupOf ((S : Subgroup ↥K).map (QuotientGroup.mk' N))) :=
    hQ2.of_equiv e.symm
  have hQc : ¬ IsCyclic ↥(Q.subgroupOf ((S : Subgroup ↥K).map (QuotientGroup.mk' N))) := by
    intro hc
    exact hQnc (isCyclic_of_surjective e.toMonoidHom e.surjective)
  have hQu : ∃! z : Q.subgroupOf ((S : Subgroup ↥K).map (QuotientGroup.mk' N)),
      orderOf z = 2 := by
    obtain ⟨w, hw, hwu⟩ := huniq
    refine ⟨e.symm w, ?_, ?_⟩
    · show orderOf (e.symm w) = 2
      have h1 : orderOf (e (e.symm w)) = orderOf (e.symm w) :=
        orderOf_injective e.toMonoidHom e.injective (e.symm w)
      rw [show e (e.symm w) = w from by simp] at h1
      rw [← h1]; exact hw
    · intro y hy
      have hy' : orderOf (e y) = 2 := by
        have h1 : orderOf (e y) = orderOf y := orderOf_injective e.toMonoidHom e.injective y
        rw [h1]; exact hy
      have h2 : e.symm (e y) = e.symm w := congrArg e.symm (hwu (e y) hy')
      rwa [show e.symm (e y) = y from by simp] at h2
  exact noUniqueInv_of_dihCycShape hshape₃ _ hQp hQc hQu

/-- Convenience form of `noQuaternionSectionProp`: `DihOrCycSylow` implies the predicate
`Work.PSTAB.NoBadSection`. -/
theorem noBadSection_of_dihOrCycSylow (X : Type) [Group X] [Finite X]
    (hD : DihOrCycSylow X) : Work.PSTAB.NoBadSection X :=
  noQuaternionSectionProp X hD

end Work.GW2
