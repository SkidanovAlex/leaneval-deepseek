/-
Copyright (c) 2026 gorenstein_walter team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CORE3 area (fundmath3-gorenstein_walter)
-/
import Mathlib
import Submission.Work.CORE2A.thm26_aux
import Submission.Work.CORE2A.thm26_of_steps
import Submission.Work.CORE2A.fstar_eq_pCore_of_isPGroup
import Submission.Work.CORE3.Case1aFrattiniApi
import Submission.OddOrder.Isaacs.Ch02_Subnormality.Basic
import Submission.OddOrder.GroupTheory.SubgroupInAmbient

/-!
# Prime-order elements of the Fitting subgroup lie in the `p`-core

The target of this file is

`Work.GW2.pCoreIn_of_pow_eq_one_of_mem_fittingIn`:

if `K ≤ G` is a subgroup of a finite group and `x ∈ F(K)` (the image of the Fitting subgroup
`F(K)` in `G`) satisfies `x ^ p = 1` for a prime `p`, then `x ∈ O_p(K)`.

Mathematically: `F(K)` is nilpotent, so an element of `p`-power order in `F(K)` lies in the
unique Sylow `p`-subgroup `O_p(F(K))` of `F(K)`, which is characteristic in `F(K)` and hence —
`F(K)` being normal in `K` — a normal `p`-subgroup of `K`; therefore it lies in `O_p(K)`.  The
formalisation uses the equivalent subnormality formulation: `⟨x⟩ ≤ F(K)` is `p`-subnormal in
`K` (a subgroup of a nilpotent group is subnormal, and `F(K) ⊴ K`), and a subnormal
`{p}`-subgroup lies in `O_p(K)`.

The auxiliary lemma `mem_pCore_of_mem_normal_isNilpotent` below is the same one recorded in
`Submission.Work.BMAX.Bender17ii`; it is reproduced here because that module imports both
`Submission.Work.ASM.Defs` and `Submission.Work.GLUE.Defs`, which re-declare the same
`Work.GW2.BenderSetup` structure and therefore cannot be combined in one environment
(see the header of `Submission.Work.CORE2A.thm26_aux`).  We keep the vocabulary of
`Submission.Work.ASM.Defs`, which is what `Work.GW2.fittingIn`/`pCoreIn` below use.
-/

set_option linter.style.haveILetI false

namespace Work.CORE3

open Subgroup

/-- **An element of prime order `q` of a normal nilpotent subgroup `F` of a finite group `H`
lies in `O_q(H)`.**

Indeed `⟨x⟩ ≤ F` is a `q`-subgroup; `F` nilpotent makes every subgroup of `F` subnormal in
`F`, and `F ⊴ H` makes it subnormal in `H`; a subnormal `q`-subgroup lies in `O_q(H)`
(`le_oPiCore_of_isSubnormal`), and `O_q(H)` is a normal `q`-subgroup of `H`, hence contained
in `pCore q H` by the universal property of the `q`-core. -/
theorem mem_pCore_of_mem_normal_isNilpotent {H : Type*} [Group H] [Finite H]
    {F : Subgroup H} (hFn : F.Normal) (hFnil : Group.IsNilpotent ↥F) {q : ℕ} [Fact q.Prime]
    {x : H} (hxF : x ∈ F) (hx : orderOf x = q) : x ∈ Work.GW2.pCore q H := by
  haveI := hFn
  haveI := hFnil
  -- `⟨x⟩ ≤ F` and `⟨x⟩` is subnormal in `H` (`F` is normal and `F` is nilpotent)
  have hPF : Subgroup.zpowers x ≤ F := Subgroup.zpowers_le.mpr hxF
  have hsub : (Subgroup.zpowers x).IsSubnormal :=
    Subgroup.IsSubnormal.trans hPF
      (OddOrder.Isaacs.Ch02.isSubnormal_of_isNilpotent_finite ((Subgroup.zpowers x).subgroupOf F))
      (Subgroup.Normal.isSubnormal hFn)
  -- `⟨x⟩` is a `{q}`-subgroup
  have hpi : Subgroup.IsPiSubgroup ({q} : Set ℕ) (Subgroup.zpowers x) :=
    OddOrder.GroupTheory.isPiSubgroup_singleton_of_isPGroup
      (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one]))
  -- a subnormal `q`-subgroup lies in `O_q(H)`
  have hle : Subgroup.zpowers x ≤ OddOrder.Isaacs.Ch03.oPiCore ({q} : Set ℕ) H :=
    OddOrder.GroupTheory.le_oPiCore_of_isSubnormal hsub hpi
  -- and `O_{q}(H) ≤ O_q(H)` (`O_{q}(H)` is a normal `q`-subgroup)
  have hPG : IsPGroup q ↥(OddOrder.Isaacs.Ch03.oPiCore ({q} : Set ℕ) H) :=
    OddOrder.GroupTheory.isPGroup_of_isPiSubgroup_singleton
      (OddOrder.Isaacs.Ch03.oPiCore.isPiGroup ({q} : Set ℕ))
  haveI : (OddOrder.Isaacs.Ch03.oPiCore ({q} : Set ℕ) H).Normal := inferInstance
  have hle2 : OddOrder.Isaacs.Ch03.oPiCore ({q} : Set ℕ) H ≤ Work.GW2.pCore q H :=
    Subgroup.normal_le_normalCore.mpr (le_sSup ⟨inferInstance, hPG⟩)
  exact hle2 (hle (Subgroup.mem_zpowers x))

/-- **`O_p(K)` contains every element of `p`-power order of the Fitting subgroup `F(K)`.**

`x ∈ F(K)` is the image of some `y ∈ F(↥K)`; `y` has order dividing `p`, so either `y = 1`
and we are done, or `orderOf y = p` and the auxiliary lemma above puts `y` in
`Work.GW2.pCore p ↥K`, whose image in `G` is exactly `Work.GW2.pCoreIn p K`. -/
theorem pCoreIn_of_pow_eq_one_of_mem_fittingIn {G : Type} [Group G] [Finite G]
    (K : Subgroup G) (p : ℕ) [Fact p.Prime] {x : G}
    (hx : x ∈ Work.GW2.fittingIn K) (hxp : x ^ p = 1) : x ∈ Work.GW2.pCoreIn p K := by
  rw [Work.GW2.fittingIn] at hx
  obtain ⟨y, hyfit, hyx⟩ := Subgroup.mem_map.mp hx
  -- `y ^ p = 1`, transported along the injective homomorphism `↥K → G`
  have hyp : y ^ p = 1 := by
    apply K.subtype_injective
    rw [map_pow, hyx, hxp, map_one]
  -- `F(↥K)` is normal and nilpotent
  have hnil : Group.IsNilpotent ↥(Work.GW2.fitting ↥K) := by
    rw [Work.CORE2A.fitting_eq_isaacsFitting (G := ↥K)]
    exact OddOrder.Isaacs.Ch01.fitting.isNilpotent
  have hnorm : (Work.GW2.fitting ↥K).Normal := by
    rw [Work.CORE2A.fitting_eq_isaacsFitting (G := ↥K)]
    exact OddOrder.Isaacs.Ch01.fitting.normal ↥K
  by_cases h1 : y = 1
  · -- `x = 1` lies in every subgroup
    rw [h1, map_one] at hyx
    rw [← hyx]
    exact Subgroup.one_mem _
  · -- otherwise `y` has order exactly `p`, and the auxiliary lemma applies
    have hord : orderOf y = p := by
      have hdvd : orderOf y ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hyp
      rcases (Fact.out : p.Prime).eq_one_or_self_of_dvd (orderOf y) hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) h1
      · exact h
    rw [Work.GW2.pCoreIn]
    exact Subgroup.mem_map.mpr
      ⟨y, mem_pCore_of_mem_normal_isNilpotent hnorm hnil hyfit hord, hyx⟩

end Work.CORE3
