import Mathlib
import Submission.Work.A7.Defs

namespace Work.AUTA7.A7

/-- An element `t` of `A₇` of order `3` has cycle type `{3}` (a 3-cycle) or `{3,3}` (a product of
two disjoint 3-cycles): every cycle length divides `3` and is at least `2`, hence is `3`, and at
most two `3`-cycles fit into seven points. -/
lemma cycleType_eq_three_or_three_three {t : alternatingGroup (Fin 7)} (ht : orderOf t = 3) :
    (t : Equiv.Perm (Fin 7)).cycleType = ({3} : Multiset ℕ) ∨
      (t : Equiv.Perm (Fin 7)).cycleType = ({3,3} : Multiset ℕ) := by
  have hord : orderOf (t : Equiv.Perm (Fin 7)) = 3 :=
    (orderOf_injective (Subgroup.subtype (alternatingGroup (Fin 7)))
      Subtype.val_injective t).trans ht
  have hdiv : ∀ n ∈ (t : Equiv.Perm (Fin 7)).cycleType, n = 3 := by
    intro n hn
    have h1 : n ∣ orderOf (t : Equiv.Perm (Fin 7)) := Equiv.Perm.dvd_of_mem_cycleType hn
    have h2 : 2 ≤ n := Equiv.Perm.two_le_of_mem_cycleType hn
    rw [hord] at h1
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp h1 with h | h
    · omega
    · exact h
  have hrep : (t : Equiv.Perm (Fin 7)).cycleType =
      Multiset.replicate ((t : Equiv.Perm (Fin 7)).cycleType.card) 3 :=
    Multiset.eq_replicate_card.mpr hdiv
  have hsum : (t : Equiv.Perm (Fin 7)).cycleType.sum =
      3 * (t : Equiv.Perm (Fin 7)).cycleType.card := by
    rw [hrep, Multiset.sum_replicate, Multiset.card_replicate, smul_eq_mul, mul_comm]
  have hle := Equiv.Perm.sum_cycleType_le (t : Equiv.Perm (Fin 7))
  rw [hsum, Fintype.card_fin] at hle
  have hcard2 : (t : Equiv.Perm (Fin 7)).cycleType.card ≤ 2 := by omega
  have hne : (t : Equiv.Perm (Fin 7)) ≠ 1 := by
    intro h; rw [h] at hord; simp at hord
  have hpos : 0 < (t : Equiv.Perm (Fin 7)).cycleType.card := by
    rw [Nat.pos_iff_ne_zero]
    intro h
    rw [Multiset.card_eq_zero] at h
    exact hne ((Equiv.Perm.cycleType_eq_zero).mp h)
  have hcard : (t : Equiv.Perm (Fin 7)).cycleType.card = 1 ∨
      (t : Equiv.Perm (Fin 7)).cycleType.card = 2 := by omega
  rcases hcard with h | h
  · left;  rw [hrep, h]; decide
  · right; rw [hrep, h]; decide

/-- The centralizer of `t ∈ A₇` inside `A₇` has the cardinality of the intersection with `A₇` of
its centralizer inside the symmetric group: it is the preimage of `C_{S₇}(t)` under the inclusion
`A₇ ↪ S₇`. -/
lemma nat_card_centralizer_coe (t : alternatingGroup (Fin 7)) :
    Nat.card (Subgroup.centralizer ({t} : Set (alternatingGroup (Fin 7)))) =
      Nat.card ↥((alternatingGroup (Fin 7) : Subgroup (Equiv.Perm (Fin 7))) ⊓
        Subgroup.centralizer ({(t : Equiv.Perm (Fin 7))} : Set (Equiv.Perm (Fin 7)))) := by
  classical
  have hcomap : Subgroup.comap (Subgroup.subtype (alternatingGroup (Fin 7)))
        (Subgroup.centralizer ({(t : Equiv.Perm (Fin 7))} : Set (Equiv.Perm (Fin 7)))) =
      Subgroup.centralizer ({t} : Set (alternatingGroup (Fin 7))) := by
    ext x
    simp only [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h; exact Subtype.ext h
    · intro h; exact congrArg Subtype.val h
  have hmap := Subgroup.map_comap_eq (Subgroup.subtype (alternatingGroup (Fin 7)))
    (Subgroup.centralizer ({(t : Equiv.Perm (Fin 7))} : Set (Equiv.Perm (Fin 7))))
  rw [hcomap, Subgroup.range_subtype] at hmap
  rw [← hmap]
  exact Nat.card_congr (Subgroup.equivMapOfInjective
    (Subgroup.centralizer ({t} : Set (alternatingGroup (Fin 7))))
    (Subgroup.subtype (alternatingGroup (Fin 7))) Subtype.val_injective).toEquiv

/-- Any element of order `3` of `A₇` has an odd element of `S₇` in its centralizer, so its
`A₇`-centralizer has half the order of its `S₇`-centralizer.  Consequently the order is `36` for
a 3-cycle (whose `S₇`-centralizer has order `72`) and `9` for a product of two disjoint 3-cycles
(whose `S₇`-centralizer has order `18`). -/
theorem CentralizerOrderThree {t : alternatingGroup (Fin 7)} (ht : orderOf t = 3) :
    Nat.card (Subgroup.centralizer ({t} : Set (alternatingGroup (Fin 7)))) = 36 ∨
      Nat.card (Subgroup.centralizer ({t} : Set (alternatingGroup (Fin 7)))) = 9 := by
  classical
  set CS : Subgroup (Equiv.Perm (Fin 7)) :=
    Subgroup.centralizer ({(t : Equiv.Perm (Fin 7))} : Set (Equiv.Perm (Fin 7))) with hCS
  have hcyc := cycleType_eq_three_or_three_three ht
  have hcardS : Nat.card CS = 72 ∨ Nat.card CS = 18 := by
    rcases hcyc with h | h
    · left; rw [hCS, Equiv.Perm.nat_card_centralizer, h]; norm_num
    · right; rw [hCS, Equiv.Perm.nat_card_centralizer, h]; norm_num
  -- the `S₇`-centralizer is not contained in `A₇`
  have hnotle : ¬ (CS ≤ alternatingGroup (Fin 7)) := by
    rw [hCS, Equiv.Perm.centralizer_le_alternating_iff]
    rintro ⟨hodd, hcard, hcount⟩
    rcases hcyc with h | h
    · rw [h] at hcard; norm_num at hcard
    · rw [h] at hcount; have := hcount 3; norm_num at this
  obtain ⟨x, hxCS, hxA⟩ := Set.not_subset.mp hnotle
  have hxsign : Equiv.Perm.sign x ≠ 1 := by
    simpa [Equiv.Perm.mem_alternatingGroup] using hxA
  -- since `A₇` has index two and there is an odd centralizing element, the relative index is two
  have hrel : (alternatingGroup (Fin 7) : Subgroup (Equiv.Perm (Fin 7))).relIndex CS = 2 := by
    rw [Subgroup.relIndex_eq_two_iff_exists_notMem_and]
    refine ⟨x, hxCS, hxA, fun b hb => ?_⟩
    rw [Subgroup.mul_mem_iff_of_index_two (alternatingGroup.index_eq_two (α := Fin 7))]
    by_cases hb' : b ∈ alternatingGroup (Fin 7)
    · exact Or.inr hb'
    · refine Or.inl ?_
      simp only [hb', false_iff]
      exact hxsign
  have hrelmul := Subgroup.relIndex_mul_card
    (H := (alternatingGroup (Fin 7) : Subgroup (Equiv.Perm (Fin 7)))) (K := CS)
  rw [hrel] at hrelmul
  have hcoe := nat_card_centralizer_coe t
  rw [hCS] at hrelmul
  rw [← hcoe] at hrelmul
  rcases hcardS with h | h
  · left; rw [h] at hrelmul; omega
  · right; rw [h] at hrelmul; omega

end Work.AUTA7.A7
