/-
Copyright (c) 2026 gorenstein_walter team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CORE2A area (fundmath3-gorenstein_walter)
-/
import Mathlib
import Submission.Work.CORE2A.Defs

/-!
# CORE2A: one involution class from one involution class in a normal subgroup of odd index

This file isolates the (elementary) step by which the "one class of involutions" hypothesis is
transported from a normal subgroup `E ≤ K` to its ambient group `K`:

* if `S : Sylow 2 G` satisfies `S ≤ E ≤ K`, then `[K : E]` is odd
  (`not_two_dvd_relIndex_of_sylow_le`);
* consequently every involution of `K` already lies in `E`
  (`mem_of_orderOf_eq_two_of_not_two_dvd_relIndex`) — an element of `K` of order two has an
  image of order dividing `2` in the odd-order quotient `K/E`, hence trivial;
* therefore, whenever the involutions of `E` form a single `E`-class, the involutions of `K`
  form a single `K`-class: `oneInvClassIn_of_sylow_le_of_involutions_conj`.

The oddness of `[K : E]` is the only place where the Sylow hypothesis is used: since `S` is a
Sylow 2-subgroup of `G`, its index in `G` is odd, and `[K : E]` divides
`[E : S] · [K : E] = [K : S]` which divides `[G : S]`.
-/

open scoped MatrixGroups

namespace Work.CORE2A

open Subgroup

/-- **Odd index from a Sylow containment.**  If `S : Sylow 2 G` lies in `E ≤ K`, then `[K : E]`
is odd (i.e. `2 ∤ E.relIndex K`).  The point is that `S` is a 2-subgroup of `G` of maximal order,
so both `[K : S]` and — a fortiori, since `E.relIndex K` divides `E.relIndex K * S.relIndex E =
S.relIndex K` — the index of `E` in `K` are odd. -/
theorem not_two_dvd_relIndex_of_sylow_le {G : Type} [Group G] [Finite G] (S : Sylow 2 G)
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

/-- **Involutions lie in a normal subgroup of odd index.**  Let `E ⊴ K` be a normal subgroup of
odd index.  If `z ∈ K` has order `2`, then `z ∈ E`: the image of `z` in the quotient `K/E` has
order dividing both `2` and the odd number `E.relIndex K`, hence is trivial. -/
theorem mem_of_orderOf_eq_two_of_not_two_dvd_relIndex {G : Type} [Group G]
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
    intro h
    exact h2 (h ▸ hdvdN)
  have h1 : orderOf ((QuotientGroup.mk' (E.subgroupOf K)) zK) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h | h
    · exact h
    · exact absurd h hne2
  have hker : zK ∈ (QuotientGroup.mk' (E.subgroupOf K)).ker := by
    rw [MonoidHom.mem_ker]
    exact orderOf_eq_one_iff.mp h1
  rw [QuotientGroup.ker_mk'] at hker
  exact Subgroup.mem_subgroupOf.mp hker

/-- **Transport of the one-involution-class property across a normal subgroup of odd index.**
Let `S : Sylow 2 G` be contained in `E ≤ K` with `E ⊴ K`.  If the involutions of `E` form a
single class under conjugation by elements of `E`, then the involutions of `K` form a single
class under conjugation by elements of `K`. -/
theorem oneInvClassIn_of_sylow_le_of_involutions_conj {G : Type} [Group G] [Finite G]
    (S : Sylow 2 G) {K E : Subgroup G} (hSK : (S : Subgroup G) ≤ K)
    (hEK : E ≤ K) (hEn : (E.subgroupOf K).Normal) (hSE : (S : Subgroup G) ≤ E)
    (hconj : ∀ x ∈ E, orderOf x = 2 → ∀ y ∈ E, orderOf y = 2 → ∃ g ∈ E, g * x * g⁻¹ = y) :
    Work.GW2.OneInvClassIn K := by
  have h2dvd : ¬ 2 ∣ E.relIndex K := not_two_dvd_relIndex_of_sylow_le S hSK hEK hSE
  have key : ∀ z ∈ K, orderOf z = 2 → z ∈ E :=
    fun z hzK hz2 => mem_of_orderOf_eq_two_of_not_two_dvd_relIndex hEn h2dvd hzK hz2
  intro x hx y hy
  obtain ⟨g, hgE, hg⟩ := hconj x (key x hx.1 hx.2) hx.2 y (key y hy.1 hy.2) hy.2
  exact ⟨g, hEK hgE, hg⟩

end Work.CORE2A
