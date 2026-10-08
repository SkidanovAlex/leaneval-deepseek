import Mathlib
import Submission.Work.BSHallW.PGroup.inf_center_ne_bot_of_normal_isPGroup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.BSHallW.PGroup.exists_pow_mem_of_normal_not_le`

Let `P` be a finite `p`-group and let `A, K ⊴ P` with `A ⊄ K`.  Then there is an element
`z ∈ A \ K` with `z ^ p ∈ K` and `⁅u, z⁆ ∈ K` for every `u : P`.

The content is the standard "a nontrivial normal subgroup of a finite `p`-group meets the
centre nontrivially" argument, transported to the quotient `P ⧸ K`:

* the image `Ā = A.map (QuotientGroup.mk' K)` is a nontrivial normal subgroup of the finite
  `p`-group `P ⧸ K` (nontriviality is exactly `¬ A ≤ K`, since `ker (mk' K) = K`);
* it therefore meets the centre of `P ⧸ K` nontrivially, and (being a `p`-group) contains an
  element `v` of order `p`;
* a preimage `z ∈ A` of `v` satisfies `z ∉ K`, `z ^ p ∈ K` and `⁅u, z⁆ ∈ K` for all `u`,
  the last two because `v` has order `p` and is central.

The "meets the centre" input is the verified sibling lemma
`Work.BSHallW.PGroup.inf_center_ne_bot_of_normal_isPGroup`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.BSHallW.PGroup

open scoped commutatorElement

theorem exists_pow_mem_of_normal_not_le {P : Type*} [Group P] [Finite P] {p : ℕ} (hp : p.Prime)
    (hP : IsPGroup p P) {K A : Subgroup P} (hKn : K.Normal) (hAn : A.Normal) (hnot : ¬ A ≤ K) :
    ∃ z : P, z ∈ A ∧ z ∉ K ∧ z ^ p ∈ K ∧ ∀ u : P, ⁅u, z⁆ ∈ K := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : K.Normal := hKn
  -- The image of `A` in `P ⧸ K` is a nontrivial normal subgroup.
  have hNn : (A.map (QuotientGroup.mk' K)).Normal :=
    hAn.map (QuotientGroup.mk' K) (QuotientGroup.mk'_surjective K)
  have hNne : A.map (QuotientGroup.mk' K) ≠ ⊥ := by
    rw [ne_eq, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hnot
  have hG : IsPGroup p (P ⧸ K) := hP.to_quotient K
  -- It meets the centre of the finite `p`-group `P ⧸ K` nontrivially.
  have hint : A.map (QuotientGroup.mk' K) ⊓ Subgroup.center (P ⧸ K) ≠ ⊥ :=
    inf_center_ne_bot_of_normal_isPGroup hG hNn hNne
  -- An element of order `p` in that intersection.
  obtain ⟨v₀, hv₀⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hint
  have hv0ne : (v₀ : P ⧸ K) ≠ 1 := fun h => hv₀ (Subtype.ext h)
  have hp_dvd :
      p ∣ Nat.card ↥(A.map (QuotientGroup.mk' K) ⊓ Subgroup.center (P ⧸ K)) := by
    refine (hG.dvd_orderOf hv0ne).trans ?_
    rw [Subgroup.orderOf_coe]
    exact orderOf_dvd_natCard _
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' p hp_dvd
  have hvne : v ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hv
    exact hp.ne_one hv.symm
  have hvN : (v : P ⧸ K) ∈ A.map (QuotientGroup.mk' K) := (Subgroup.mem_inf.mp v.2).1
  have hvC : (v : P ⧸ K) ∈ Subgroup.center (P ⧸ K) := (Subgroup.mem_inf.mp v.2).2
  obtain ⟨z, hzA, hzv⟩ := Subgroup.mem_map.mp hvN
  have hvpow : (v : P ⧸ K) ^ p = 1 := by
    have h1 : orderOf (v : P ⧸ K) = p := by rw [Subgroup.orderOf_coe v, hv]
    rw [← h1, pow_orderOf_eq_one]
  refine ⟨z, hzA, ?_, ?_, ?_⟩
  · -- `z ∉ K`
    intro hz
    have h1 : (v : P ⧸ K) = 1 := by
      rw [← hzv, QuotientGroup.mk'_apply]
      exact (QuotientGroup.eq_one_iff z).mpr hz
    exact hvne (Subtype.ext h1)
  · -- `z ^ p ∈ K`
    have hzp : ((z ^ p : P) : P ⧸ K) = 1 := by
      rw [show ((z ^ p : P) : P ⧸ K) = QuotientGroup.mk' K (z ^ p) from
            (QuotientGroup.mk'_apply K (z ^ p)).symm]
      rw [map_pow, hzv, hvpow]
    exact (QuotientGroup.eq_one_iff (z ^ p)).mp hzp
  · -- `⁅u, z⁆ ∈ K` for every `u`
    intro u
    have hc : ((⁅u, z⁆ : P) : P ⧸ K) = 1 := by
      rw [show ((⁅u, z⁆ : P) : P ⧸ K) = QuotientGroup.mk' K ⁅u, z⁆ from
            (QuotientGroup.mk'_apply K ⁅u, z⁆).symm]
      rw [map_commutatorElement (QuotientGroup.mk' K) u z, hzv]
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        (Subgroup.mem_center_iff.mp hvC (QuotientGroup.mk' K u))
    exact (QuotientGroup.eq_one_iff ⁅u, z⁆).mp hc

end Work.BSHallW.PGroup
