import Mathlib.Algebra.Torsor.Defs
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace Commons.GroupTheory.Subgroup

/-- In a finite cyclic group `G`, the set of solutions of `x ^ e = 1` has cardinality `e`, for
`e` a divisor of the order of `G`. -/
lemma natCard_pow_eq_one_of_dvd {G : Type*} [Group G] [Finite G] [IsCyclic G]
    {e : ℕ} (he : e ∣ Nat.card G) : Nat.card {x : G // x ^ e = 1} = e := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  have hepos : 0 < e := Nat.pos_of_dvd_of_pos he Nat.card_pos
  refine le_antisymm ?_ ?_
  · rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact IsCyclic.card_pow_eq_one_le (α := G) (n := e) hepos
  · obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
    have hgord : orderOf g = Nat.card G := orderOf_eq_card_of_forall_mem_zpowers hg
    have hgnz : orderOf g ≠ 0 := by rw [hgord]; exact Nat.card_pos.ne'
    have hdvd : e ∣ orderOf g := by rw [hgord]; exact he
    let y : G := g ^ (orderOf g / e)
    have hyord : orderOf y = e := orderOf_pow_orderOf_div hgnz hdvd
    have hcard : Nat.card ↥(Subgroup.zpowers y) = e := by rw [Nat.card_zpowers, hyord]
    have hmaps : ∀ z : ↥(Subgroup.zpowers y), (z : G) ^ e = 1 := by
      intro z
      have h1 : orderOf z ∣ e := by
        have := orderOf_dvd_natCard z
        rwa [hcard] at this
      have h2 : z ^ e = 1 := (orderOf_dvd_iff_pow_eq_one).mp h1
      rw [← Subgroup.coe_pow, h2]; rfl
    have hinj : Function.Injective
        (fun z : ↥(Subgroup.zpowers y) => (⟨(z : G), hmaps z⟩ : {x : G // x ^ e = 1})) := by
      intro a b hab
      have h : (a : G) = (b : G) := congrArg (fun w : {x : G // x ^ e = 1} => (w : G)) hab
      exact Subtype.ext h
    calc e = Nat.card ↥(Subgroup.zpowers y) := hcard.symm
      _ ≤ Nat.card {x : G // x ^ e = 1} := Nat.card_le_card_of_injective _ hinj

/-- In a finite cyclic group `G`, an element `x` lies in a subgroup `H` if and only if
`x ^ Nat.card H = 1`. -/
lemma mem_iff_pow_card_eq_one {G : Type*} [Group G] [Finite G] [IsCyclic G]
    (H : Subgroup G) (x : G) : x ∈ H ↔ x ^ Nat.card ↥H = 1 := by
  classical
  refine ⟨?_, ?_⟩
  · intro hx
    have h1 : orderOf x ∣ Nat.card ↥H := by
      have h0 : orderOf (⟨x, hx⟩ : ↥H) ∣ Nat.card ↥H := orderOf_dvd_natCard _
      rwa [← Subgroup.orderOf_coe (a := (⟨x, hx⟩ : ↥H))] at h0
    exact (orderOf_dvd_iff_pow_eq_one).mp h1
  · intro hx
    set u := Nat.card ↥H with hu
    have hsub : (H : Set G) ⊆ {y : G | y ^ u = 1} := by
      intro y hy
      have h1 : orderOf y ∣ Nat.card ↥H := by
        have h0 : orderOf (⟨y, hy⟩ : ↥H) ∣ Nat.card ↥H := orderOf_dvd_natCard _
        rwa [← Subgroup.orderOf_coe (a := (⟨y, hy⟩ : ↥H))] at h0
      rw [Set.mem_ofPred_eq, hu]
      exact (orderOf_dvd_iff_pow_eq_one).mp h1
    have hu_dvd : u ∣ Nat.card G := by rw [hu]; exact Subgroup.card_subgroup_dvd_card H
    have hcnt : Nat.card {y : G // y ^ u = 1} = u := natCard_pow_eq_one_of_dvd hu_dvd
    have heq : (H : Set G) = {y : G | y ^ u = 1} := by
      apply Set.eq_of_subset_of_ncard_le hsub
      have hEq : ({y : G | y ^ u = 1} : Set G).ncard = (H : Set G).ncard :=
        calc ({y : G | y ^ u = 1} : Set G).ncard
            = Nat.card {y : G // y ^ u = 1} := (Nat.card_coe_set_eq _).symm
          _ = u := hcnt
          _ = Nat.card ↥H := hu
          _ = (H : Set G).ncard := Nat.card_coe_set_eq _
      exact hEq.le
    have hxS : x ∈ ({y : G | y ^ u = 1} : Set G) := by
      rw [Set.mem_ofPred_eq, hu]; exact hx
    rwa [← heq] at hxS

/-- **Bender–Suzuki auxiliary.**  In a finite cyclic group, the order of the intersection of two
subgroups is the gcd of their orders. -/
theorem card_inf_eq_gcd_of_isCyclic {G : Type*} [Group G] [Finite G] [IsCyclic G]
    (H K : Subgroup G) :
    Nat.card ↥(H ⊓ K) = Nat.gcd (Nat.card ↥H) (Nat.card ↥K) := by
  classical
  set d := Nat.gcd (Nat.card ↥H) (Nat.card ↥K) with hd
  have hmem : ∀ x : G, x ∈ H ⊓ K ↔ x ^ d = 1 := by
    intro x
    rw [Subgroup.mem_inf, mem_iff_pow_card_eq_one H x, mem_iff_pow_card_eq_one K x]
    constructor
    · rintro ⟨h1, h2⟩
      have h1' : orderOf x ∣ Nat.card ↥H := (orderOf_dvd_iff_pow_eq_one).mpr h1
      have h2' : orderOf x ∣ Nat.card ↥K := (orderOf_dvd_iff_pow_eq_one).mpr h2
      exact (orderOf_dvd_iff_pow_eq_one).mp (Nat.dvd_gcd h1' h2')
    · intro h1
      have h1' : orderOf x ∣ d := (orderOf_dvd_iff_pow_eq_one).mpr h1
      have h2 : orderOf x ∣ Nat.card ↥H ∧ orderOf x ∣ Nat.card ↥K := by
        rw [hd] at h1'
        exact Nat.dvd_gcd_iff.mp h1'
      exact ⟨(orderOf_dvd_iff_pow_eq_one).mp h2.1, (orderOf_dvd_iff_pow_eq_one).mp h2.2⟩
  have hdvd : d ∣ Nat.card G := by
    rw [hd]
    exact (Nat.gcd_dvd_left _ _).trans (Subgroup.card_subgroup_dvd_card H)
  have hcard : Nat.card ↥(H ⊓ K) = Nat.card {x : G // x ^ d = 1} :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun x => hmem x))
  rw [hcard]
  exact (natCard_pow_eq_one_of_dvd hdvd).trans hd

end Commons.GroupTheory.Subgroup