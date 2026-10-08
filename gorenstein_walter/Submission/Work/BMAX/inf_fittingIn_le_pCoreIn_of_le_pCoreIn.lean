/-
Copyright (c) 2026 gorenstein_walter team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BMAX area (fundmath3-gorenstein_walter)
-/
import Mathlib
import Submission.Work.BMAX.Defs
import Submission.Work.CORE2A.thm26_aux
import Submission.OddOrder.Isaacs.Ch02_Subnormality.Basic
import Submission.OddOrder.GroupTheory.SubgroupInAmbient

set_option linter.style.haveILetI false

/-!
# `Q ⊓ F(A) ≤ O_q(A)` for `Q` a `q`-subgroup of `A`

The target of this file is

`Work.BMAX.inf_fittingIn_le_pCoreIn_of_le_pCoreIn`:

if `Q ≤ O_q(B)` and `Q ≤ A` for a prime `q`, then `Q ⊓ F(A) ≤ O_q(A)`.

Mathematically: `Q ≤ O_q(B)` forces `Q` to be a `q`-group, hence every element `x ∈ Q` has
`q`-power order.  For such an `x` lying in the Fitting subgroup `F(A)` (which is nilpotent),
the cyclic subgroup `⟨x⟩` is a `q`-subgroup of the nilpotent group `F(A)`, hence subnormal in
`F(A)`; `F(A) ⊴ A` then makes `⟨x⟩` subnormal in `A`, and a subnormal `q`-subgroup of `A`
lies in `O_q(A)`.  So `x ∈ O_q(A)`, as required.

The only ingredient beyond the vocabulary of the area is the general lemma

`mem_pCore_of_mem_normal_isNilpotent_of_isPGroup`

(an element of a normal nilpotent subgroup that generates a `q`-subgroup lies in `O_q`), which
generalises `Work.CORE3.mem_pCore_of_mem_normal_isNilpotent` from elements of order exactly
`q` to arbitrary `q`-elements.
-/

open scoped MatrixGroups

namespace Work.BMAX

open Subgroup

/-! ## 1. `q`-elements of a normal nilpotent subgroup lie in `O_q` -/

/-- **An element generating a `q`-subgroup of a normal nilpotent subgroup `F ⊴ H` lies in
`O_q(H)`.**

Indeed `⟨x⟩ ≤ F` is a `q`-subgroup; `F` nilpotent makes every subgroup of `F` subnormal in `F`,
and `F ⊴ H` makes it subnormal in `H`; a subnormal `q`-subgroup lies in `O_{q}(H)`
(`le_oPiCore_of_isSubnormal`), and `O_{q}(H)` is a normal `q`-subgroup of `H`, hence contained
in `pCore q H` by the universal property of the `q`-core. -/
theorem mem_pCore_of_mem_normal_isNilpotent_of_isPGroup {H : Type*} [Group H] [Finite H]
    {F : Subgroup H} (hFn : F.Normal) (hFnil : Group.IsNilpotent ↥F) {q : ℕ} [Fact q.Prime]
    {x : H} (hxF : x ∈ F) (hx : IsPGroup q ↥(Subgroup.zpowers x)) :
    x ∈ Work.GW2.pCore q H := by
  haveI := hFn
  haveI := hFnil
  -- `⟨x⟩ ≤ F` and `⟨x⟩` is subnormal in `H` (`F` is normal and `F` is nilpotent)
  have hPF : Subgroup.zpowers x ≤ F := Subgroup.zpowers_le.mpr hxF
  have hsub : (Subgroup.zpowers x).IsSubnormal :=
    Subgroup.IsSubnormal.trans hPF
      (OddOrder.Isaacs.Ch02.isSubnormal_of_isNilpotent_finite
        ((Subgroup.zpowers x).subgroupOf F))
      (Subgroup.Normal.isSubnormal hFn)
  -- `⟨x⟩` is a `{q}`-subgroup
  have hpi : Subgroup.IsPiSubgroup ({q} : Set ℕ) (Subgroup.zpowers x) :=
    OddOrder.GroupTheory.isPiSubgroup_singleton_of_isPGroup hx
  -- a subnormal `q`-subgroup lies in `O_{q}(H)`
  have hle : Subgroup.zpowers x ≤ OddOrder.Isaacs.Ch03.oPiCore ({q} : Set ℕ) H :=
    OddOrder.GroupTheory.le_oPiCore_of_isSubnormal hsub hpi
  -- and `O_{q}(H) ≤ O_q(H)` (`O_{q}(H)` is a normal `q`-subgroup of `H`)
  have hPG : IsPGroup q ↥(OddOrder.Isaacs.Ch03.oPiCore ({q} : Set ℕ) H) :=
    OddOrder.GroupTheory.isPGroup_of_isPiSubgroup_singleton
      (OddOrder.Isaacs.Ch03.oPiCore.isPiGroup ({q} : Set ℕ))
  haveI : (OddOrder.Isaacs.Ch03.oPiCore ({q} : Set ℕ) H).Normal := inferInstance
  have hle2 : OddOrder.Isaacs.Ch03.oPiCore ({q} : Set ℕ) H ≤ Work.GW2.pCore q H :=
    Subgroup.normal_le_normalCore.mpr (le_sSup ⟨inferInstance, hPG⟩)
  exact hle2 (hle (Subgroup.mem_zpowers x))

/-! ## 2. The same for the Fitting subgroup of a subgroup -/

/-- **Transport of `IsPGroup` along an injective homomorphism sending `y` to `x`.**

If `f y = x` for an injective `f` and `⟨x⟩` is a `q`-group then so is `⟨y⟩`. -/
theorem isPGroup_zpowers_of_map_eq {H G : Type*} [Group H] [Group G] (f : H →* G)
    (hf : Function.Injective f) {y : H} {x : G} (hyx : f y = x) {q : ℕ}
    (hx : IsPGroup q ↥(Subgroup.zpowers x)) : IsPGroup q ↥(Subgroup.zpowers y) := by
  have hcomap : (Subgroup.zpowers x).comap f = Subgroup.zpowers y := by
    ext z
    rw [Subgroup.mem_comap, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, hf (by rw [map_zpow, hyx, hk])⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, by rw [← hyx, ← map_zpow, hk]⟩
  rw [← hcomap]
  exact hx.comap_of_injective f hf

/-- **`O_q(A)` contains every `q`-element of the Fitting subgroup `F(A)`** (in the ambient
group `G`).

`x ∈ F(A)` is the image under `A.subtype` of some `y ∈ F(↥A)`; `y` generates a `q`-subgroup of
the normal nilpotent subgroup `F(↥A) ⊴ ↥A`, so `y ∈ O_q(↥A)` by
`mem_pCore_of_mem_normal_isNilpotent_of_isPGroup`, and mapping back down gives the claim. -/
theorem pCoreIn_of_isPGroup_zpowers_of_mem_fittingIn {G : Type} [Group G] [Finite G]
    (K : Subgroup G) (q : ℕ) [Fact q.Prime] {x : G}
    (hx : x ∈ Work.GW2.fittingIn K) (hxq : IsPGroup q ↥(Subgroup.zpowers x)) :
    x ∈ Work.GW2.pCoreIn q K := by
  rw [Work.GW2.fittingIn] at hx
  obtain ⟨y, hyfit, hyx⟩ := Subgroup.mem_map.mp hx
  -- `F(↥K)` is normal and nilpotent
  have hnil : Group.IsNilpotent ↥(Work.GW2.fitting ↥K) := by
    rw [Work.CORE2A.fitting_eq_isaacsFitting (G := ↥K)]
    exact OddOrder.Isaacs.Ch01.fitting.isNilpotent
  have hnorm : (Work.GW2.fitting ↥K).Normal := by
    rw [Work.CORE2A.fitting_eq_isaacsFitting (G := ↥K)]
    exact OddOrder.Isaacs.Ch01.fitting.normal ↥K
  -- transport the `q`-group hypothesis along `K.subtype`
  have hyq : IsPGroup q ↥(Subgroup.zpowers y) :=
    isPGroup_zpowers_of_map_eq K.subtype K.subtype_injective hyx hxq
  rw [Work.GW2.pCoreIn]
  exact Subgroup.mem_map.mpr
    ⟨y, mem_pCore_of_mem_normal_isNilpotent_of_isPGroup hnorm hnil hyfit hyq, hyx⟩

/-! ## 3. The target -/

theorem inf_fittingIn_le_pCoreIn_of_le_pCoreIn {G : Type} [Group G] [Finite G]
    (A B Q : Subgroup G) (q : ℕ) (hq : q.Prime)
    (hQ : Q ≤ Work.GW2.pCoreIn q B) (hQA : Q ≤ A) :
    Q ⊓ Work.GW2.fittingIn A ≤ Work.GW2.pCoreIn q A := by
  haveI : Fact q.Prime := ⟨hq⟩
  -- `O_q(B)` is a `q`-group, hence so is `Q` and so is `⟨x⟩` for `x ∈ Q`
  have hPcoreInP : IsPGroup q ↥(Work.GW2.pCoreIn q B) := by
    rw [Work.GW2.pCoreIn]
    exact IsPGroup.map
      (by
        rw [Work.CORE2A.pCore_eq_opCore (G := ↥B) (p := q)]
        exact OddOrder.Isaacs.Ch01.opCore_isPGroup q ↥B)
      B.subtype
  intro x hx
  obtain ⟨hxQ, hxF⟩ := Subgroup.mem_inf.mp hx
  have hxq : IsPGroup q ↥(Subgroup.zpowers x) :=
    hPcoreInP.to_le (Subgroup.zpowers_le.mpr (hQ hxQ))
  exact pCoreIn_of_isPGroup_zpowers_of_mem_fittingIn A q hxF hxq

end Work.BMAX
