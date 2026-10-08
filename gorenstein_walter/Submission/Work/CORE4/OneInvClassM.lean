/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area CORE4, `Work.CORE4`)

# CORE4 — `M` has one class of involutions

Bender 1981, p. 227, uses *"As `N_G(X) = M^g` has only one class of involutions, we can choose `g`
subject to `t^g = t`."*  The input is §4 (1)–(9): `E(M)` has one class of involutions
(`Case2Pre.oneClass`), `S ≤ E(M)` (§4 (9), `Case2Ctx.nine`) and `S` is a Sylow 2-subgroup of `M`.
Hence every involution of `M` lies in `E(M)` (odd index) and the single class of `E(M)` transports.

The two transport lemmas are the CORE2A ones; they are re-proved here because importing
`Submission.Work.CORE2A.Defs` clashes with `Submission.Work.CORE4.Defs` (both declare the namespace
`Work.GW2`).
-/
import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2CountSetup

namespace Work.CORE4

open Subgroup

/-- **Odd index from a Sylow containment**: if `S : Sylow 2 G` lies in `E ≤ K`, then `2 ∤ |K : E|`. -/
theorem not_two_dvd_relIndex_of_sylow_le_c4 {G : Type} [Group G] [Finite G] (S : Sylow 2 G)
    {E K : Subgroup G} (hSK : (S : Subgroup G) ≤ K) (hEK : E ≤ K) (hSE : (S : Subgroup G) ≤ E) :
    ¬ 2 ∣ E.relIndex K := by
  have hnotdvd : ¬ 2 ∣ (S : Subgroup G).index := Sylow.not_dvd_index S
  have hrel : (S : Subgroup G).relIndex K ∣ (S : Subgroup G).index :=
    Subgroup.relIndex_dvd_index_of_le hSK
  have hdiv : E.relIndex K ∣ (S : Subgroup G).relIndex K :=
    ⟨(S : Subgroup G).relIndex E, by
      have h := Subgroup.relIndex_mul_relIndex (H := (S : Subgroup G)) (K := E) (L := K) hSE hEK
      rw [mul_comm]
      exact h.symm⟩
  exact fun h => hnotdvd ((Dvd.dvd.trans h hdiv).trans hrel)

/-- **Involutions lie in a normal subgroup of odd index**: if `E ⊴ K` and `2 ∤ |K : E|`, then every
element of `K` of order `2` lies in `E`. -/
theorem mem_of_orderOf_eq_two_of_not_two_dvd_relIndex_c4 {G : Type} [Group G]
    {E K : Subgroup G} (hEn : (E.subgroupOf K).Normal) (h2 : ¬ 2 ∣ E.relIndex K)
    {z : G} (hzK : z ∈ K) (hz2 : orderOf z = 2) : z ∈ E := by
  let zK : ↥K := ⟨z, hzK⟩
  have hz2G : z * z = 1 := by
    have h := pow_orderOf_eq_one z
    rw [hz2] at h
    simpa [pow_two] using h
  have hzK2 : zK ^ 2 = 1 := by
    apply Subtype.ext
    show ((zK : ↥K) : G) ^ 2 = ((1 : ↥K) : G)
    rw [pow_two]
    exact hz2G
  have hq2 : (QuotientGroup.mk' (E.subgroupOf K)) zK ^ 2 = 1 := by
    rw [← map_pow, hzK2, map_one]
  have hdvd2 : orderOf ((QuotientGroup.mk' (E.subgroupOf K)) zK) ∣ 2 :=
    orderOf_dvd_iff_pow_eq_one.mpr hq2
  have hdvdN : orderOf ((QuotientGroup.mk' (E.subgroupOf K)) zK) ∣ (E.subgroupOf K).index :=
    orderOf_dvd_natCard _
  have hne2 : orderOf ((QuotientGroup.mk' (E.subgroupOf K)) zK) ≠ 2 := by
    intro hh
    exact h2 (hh ▸ hdvdN)
  have h1 : orderOf ((QuotientGroup.mk' (E.subgroupOf K)) zK) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with hh | hh
    · exact hh
    · exact absurd hh hne2
  have hker : zK ∈ (QuotientGroup.mk' (E.subgroupOf K)).ker := by
    rw [MonoidHom.mem_ker]
    exact orderOf_eq_one_iff.mp h1
  rw [QuotientGroup.ker_mk'] at hker
  exact Subgroup.mem_subgroupOf.mp hker

/-- **`M` has one class of involutions**: for the §4 configuration `h : Case2Ctx B`, any two
involutions of the coatom `M = h.D.M` are `M`-conjugate.  (The property is preserved by
conjugation, so this gives `OneInvClassIn (M^g)` for every `g`.) -/
theorem OneInvClassM (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B),
        Work.GW2.OneInvClassIn (h.D.M) := by
  intro G _ _ hbc B h
  obtain ⟨p, k, hp, hpodd, h7, hiso, hSE⟩ := h.nine
  have hnot : ¬ 2 ∣ (Work.GW2.layerIn h.D.M).relIndex h.D.M :=
    not_two_dvd_relIndex_of_sylow_le_c4 (B.S) h.S_le_M (Work.CORE4.layerIn_le h.D.M) hSE
  intro x hx y hy
  have hxE : x ∈ Work.GW2.layerIn h.D.M :=
    mem_of_orderOf_eq_two_of_not_two_dvd_relIndex_c4 h.layerIn_subgroupOf_normal hnot hx.1 hx.2
  have hyE : y ∈ Work.GW2.layerIn h.D.M :=
    mem_of_orderOf_eq_two_of_not_two_dvd_relIndex_c4 h.layerIn_subgroupOf_normal hnot hy.1 hy.2
  obtain ⟨g, hgE, hg⟩ := Work.GW2.Case2Pre.oneClass B h.D h.pre x ⟨hxE, hx.2⟩ y ⟨hyE, hy.2⟩
  exact ⟨g, Work.CORE4.layerIn_le h.D.M hgE, hg⟩

end Work.CORE4
