import Mathlib
import Submission.Work.CORE2B.Defs
import Submission.Work.CORE2B.oddCore_odd

/-!
# A Klein four-subgroup of `N` meets `O₂(N)` when `[N : O₂(N)O(N)] ∣ 6`

If `A ◁ K` and `B ◁ K` with `|B|` odd, `V ≤ K` is a Klein four-group and
`[(A ⊔ B) : K] ∣ 6`, then `V ⊓ A ≠ ⊥`.  Applied with `K = ↥N`, `A = O₂(N)`,
`B = O(N)` this is the statement of `four_subgroup_meets_pCore_two`, the `O₂`-half of
Bender's Lemma 2.9.

The proof has two steps.

* Counting: `V ⊓ (A ⊔ B) ≠ ⊥`.  Indeed `M := A ⊔ B` is normal, so the index of `M` in
  `V ⊔ M` equals `M.relIndex V`, which divides both `|V| = 4` and `M.index ∣ 6`, hence
  divides `2`; therefore `|M ⊓ V| ≥ 2`.
* Containment: every element of `V ⊓ M` has order `≤ 2`, while its image in `K ⧸ A` lies in
  the image of `M`, which is a homomorphic image of `B` and so has odd order.  Hence the image
  is trivial, i.e. `V ⊓ M ≤ A`.
-/

namespace Work.CORE2B

open Subgroup

set_option linter.style.haveILetI false

/-- **Counting/containment lemma.**  Let `A ◁ K` and `B ◁ K` with `|B|` odd, and let
`V ≤ K` satisfy `|V| = 4` with every element an involution.  If `[(A ⊔ B) : K] ∣ 6`, then
`V ⊓ A ≠ ⊥`. -/
private theorem four_meets_twoCore_aux {K : Type*} [Group K] [Finite K]
    (A B V : Subgroup K) (hA : A.Normal) (hB : B.Normal)
    (hBodd : Odd (Nat.card B)) (hV4 : Nat.card V = 4) (hVsq : ∀ v ∈ V, v ^ 2 = 1)
    (hix : (A ⊔ B).index ∣ 6) : V ⊓ A ≠ ⊥ := by
  haveI : A.Normal := hA
  haveI : B.Normal := hB
  haveI : (A ⊔ B).Normal := Subgroup.sup_normal A B
  -- `V ⊓ (A ⊔ B)` is nontrivial.
  have hcard : 2 ≤ Nat.card ↥((A ⊔ B) ⊓ V) := by
    have h := Subgroup.relIndex_mul_card (A ⊔ B) V
    rw [hV4] at h
    have h4 : (A ⊔ B).relIndex V ∣ 4 := dvd_of_mul_right_eq _ h
    have h6 : (A ⊔ B).relIndex V ∣ 6 := by
      have h' := Subgroup.relIndex_mul_index (le_sup_right : (A ⊔ B) ≤ V ⊔ (A ⊔ B))
      rw [Subgroup.relIndex_sup_right V (A ⊔ B)] at h'
      exact (dvd_of_mul_right_eq _ h').trans hix
    have h2 : (A ⊔ B).relIndex V ∣ 2 := by
      simpa using Nat.dvd_gcd h4 h6
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h1 | h2'
    · rw [h1, one_mul] at h; omega
    · rw [h2'] at h; omega
  have hne : V ⊓ (A ⊔ B) ≠ ⊥ := by
    rw [inf_comm]
    intro hc
    rw [hc, Subgroup.card_bot] at hcard
    omega
  -- Every element of `V ⊓ (A ⊔ B)` lies in `A`.
  have hMA : (A ⊔ B) ⊓ V ≤ A := by
    have hφker : (QuotientGroup.mk' A).ker = A := QuotientGroup.ker_mk' A
    have hMmap : (A ⊔ B).map (QuotientGroup.mk' A) = B.map (QuotientGroup.mk' A) := by
      rw [Subgroup.map_sup]
      have hAbot : A.map (QuotientGroup.mk' A) = ⊥ := by
        rw [Subgroup.map_eq_bot_iff]
        intro y hy
        rw [hφker]
        exact hy
      rw [hAbot, bot_sup_eq]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxM, hxV⟩ := hx
    have hx2 : x ^ 2 = 1 := hVsq x hxV
    have hx2' : (QuotientGroup.mk' A x) ^ 2 = 1 := by
      rw [← map_pow, hx2, map_one]
    -- the image of `x` lies in the image of `B`, of odd order
    have hmem : QuotientGroup.mk' A x ∈ B.map (QuotientGroup.mk' A) := by
      rw [← hMmap]
      exact Subgroup.mem_map_of_mem _ hxM
    obtain ⟨b, hbB, hb⟩ := Subgroup.mem_map.mp hmem
    have hb_ord : orderOf b ∣ Nat.card ↥B := by
      rw [← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hbB)
    have hodd : Odd (orderOf (QuotientGroup.mk' A x)) := by
      rw [← hb]
      exact hBodd.of_dvd_nat
        ((orderOf_map_dvd (QuotientGroup.mk' A) b).trans hb_ord)
    have hdiv2 : orderOf (QuotientGroup.mk' A x) ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one]
      exact hx2'
    have hone : orderOf (QuotientGroup.mk' A x) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdiv2 with h | h
      · exact h
      · rw [h] at hodd
        exact absurd hodd (by norm_num)
    have hx1 : QuotientGroup.mk' A x = 1 := orderOf_eq_one_iff.mp hone
    have hmemker : x ∈ (QuotientGroup.mk' A).ker := by
      rw [MonoidHom.mem_ker]
      exact hx1
    rwa [hφker] at hmemker
  -- Conclude.
  intro hbot
  refine hne ?_
  have hle : V ⊓ (A ⊔ B) ≤ V ⊓ A := by
    rw [inf_comm V (A ⊔ B)]
    exact le_inf inf_le_right hMA
  rw [hbot] at hle
  exact le_bot_iff.mp hle

theorem four_subgroup_meets_pCore_two {G : Type} [Group G] [Finite G]
    (N V : Subgroup G) (hVN : V ≤ N) (hV : Work.GW2.IsFourGroup V)
    (hix : (Work.GW2.pCoreIn 2 N ⊔ Work.GW2.oddCoreIn N).relIndex N ∣ 6) :
    V ⊓ Work.GW2.pCoreIn 2 N ≠ ⊥ := by
  -- Translate the index hypothesis into `↥N`.
  have hsup : Work.GW2.pCoreIn 2 N ⊔ Work.GW2.oddCoreIn N =
      (Work.GW2.pCore 2 N ⊔ Work.GW2.oddCore N).map N.subtype := by
    rw [Work.GW2.pCoreIn, Work.GW2.oddCoreIn, Subgroup.map_sup]
  have hix' : (Work.GW2.pCore 2 N ⊔ Work.GW2.oddCore N).index ∣ 6 := by
    have h3 : (⊤ : Subgroup ↥N).map N.subtype = N := by
      rw [Subgroup.map_top, Subgroup.range_subtype]
    have h4 : (Subgroup.map N.subtype
          (Work.GW2.pCore 2 ↥N ⊔ Work.GW2.oddCore ↥N)).relIndex
          (Subgroup.map N.subtype (⊤ : Subgroup ↥N))
        = (Work.GW2.pCore 2 ↥N ⊔ Work.GW2.oddCore ↥N).relIndex (⊤ : Subgroup ↥N) :=
      Subgroup.relIndex_map_map_of_injective _ _ N.subtype_injective
    rw [h3, Subgroup.relIndex_top_right] at h4
    have hrel : (Work.GW2.pCoreIn 2 N ⊔ Work.GW2.oddCoreIn N).relIndex N =
        (Work.GW2.pCore 2 ↥N ⊔ Work.GW2.oddCore ↥N).index := by
      rw [hsup]
      exact h4
    exact hrel ▸ hix
  -- `V` as a subgroup of `↥N` is a Klein four-group.
  have hV₀card : Nat.card ↥(V.subgroupOf N) = 4 := by
    have hmap : (V.subgroupOf N).map N.subtype = V := by
      rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hVN]
    rw [← Subgroup.card_map_of_injective N.subtype_injective (K := V.subgroupOf N), hmap]
    exact hV.1
  have hV₀sq : ∀ v ∈ V.subgroupOf N, v ^ 2 = 1 := by
    intro v hv
    rw [Subgroup.mem_subgroupOf] at hv
    have hv2 : (v : G) ^ 2 = 1 := hV.2 (v : G) hv
    exact Subtype.ext (by simpa using hv2)
  have hkey : V.subgroupOf N ⊓ Work.GW2.pCore 2 N ≠ ⊥ :=
    four_meets_twoCore_aux (Work.GW2.pCore 2 N) (Work.GW2.oddCore N) (V.subgroupOf N)
      (Work.GW2.pCore_normal 2 N) (Work.GW2.oddCore_normal N)
      (oddCore_odd (G := ↥N)) hV₀card hV₀sq hix'
  -- Translate the conclusion back to `G`.
  have h1 : (V.subgroupOf N).map N.subtype = V := by
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hVN]
  have hmapinf : (V.subgroupOf N ⊓ Work.GW2.pCore 2 N).map N.subtype =
      V ⊓ Work.GW2.pCoreIn 2 N := by
    rw [Subgroup.map_inf _ _ N.subtype N.subtype_injective, h1, Work.GW2.pCoreIn]
  intro hbot
  have hcard1 : Nat.card ↥(V.subgroupOf N ⊓ Work.GW2.pCore 2 N) = 1 := by
    rw [← Subgroup.card_map_of_injective N.subtype_injective
        (K := V.subgroupOf N ⊓ Work.GW2.pCore 2 N), hmapinf, hbot]
    exact Subgroup.card_bot
  exact hkey (Subgroup.card_eq_one.mp hcard1)

end Work.CORE2B
