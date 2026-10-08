import Mathlib
import Submission.Work.BSW.Cases.K4.case1Aux
import Submission.Work.BSW.Cases.K4.cosetInvCount_eq_of_mk_eq
import Submission.Work.BSW.Cases.K4.cosetInvCount_rightCount

namespace Work.BSW.Cases.K4

open Subgroup

/-!
# Counting the involutions `u ∉ H` with `|C_G(u) ∩ H| = 2`

`Work.GW2.bCount H 2` counts the nontrivial cosets of `H` containing exactly two involutions.
The main result of this file is the general, hypothesis-free counting identity

`|{u : G | orderOf u = 2 ∧ u ∉ H ∧ cosetInvCount H u = 2}| = 2 * bCount H 2`,

which says that the involutions lying in those cosets can be counted either "one coset at a time"
(each such coset contributing exactly two involutions) or by `bCount`.  The group-theoretic count

`|{u : G | u ∉ H ∧ orderOf u = 2 ∧ |C_G(u) ∩ H| = 2}| = 2 * bCount H 2`

of Bender's Case 1 then follows, because for an involution `u` the shape of `C_G(u) ∩ H` is the
number of involutions in the coset `H u` (the hypothesis `hcoset`), which in turn equals
`cosetInvCount H u`.
-/

/-- Decompose a set into the fibres of a map, counted with `Set.ncard`. -/
theorem ncard_eq_sum_ncard_fiber {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (p : α → Prop) :
    ({x : α | p x} : Set α).ncard =
      ∑ c : β, ({x : α | p x ∧ f x = c} : Set α).ncard := by
  classical
  have h1 : ({x : α | p x} : Set α).ncard = (Finset.univ.filter p).card := by
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]
  rw [h1]
  rw [Finset.card_eq_sum_card_fiberwise (f := f) (s := Finset.univ.filter p)
    (t := Finset.univ) (by intro a _; exact Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro c _
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]
  rw [Finset.filter_filter]

/-- The involutions lying in a fixed coset `c` of `H` number exactly `cosetInvCount H (out c)`. -/
theorem fiber_ncard_eq_cosetInvCount {G : Type} [Group G] [Finite G] (H : Subgroup G)
    (c : G ⧸ H) :
    ({x : G | orderOf x = 2 ∧ (x : G ⧸ H) = c} : Set G).ncard =
      Work.GW2.cosetInvCount H (Quotient.out c) := by
  have hout : ((Quotient.out c : G) : G ⧸ H) = c := Quotient.out_eq c
  have hset : ({x : G | orderOf x = 2 ∧ (x : G ⧸ H) = c} : Set G)
      = {x : G | orderOf x = 2 ∧ (Quotient.out c)⁻¹ * x ∈ H} := by
    ext x
    constructor
    · rintro ⟨hx, hxc⟩
      exact ⟨hx, QuotientGroup.eq.mp (hout.trans hxc.symm)⟩
    · rintro ⟨hx, hmem⟩
      exact ⟨hx, (QuotientGroup.eq.mpr hmem).symm.trans hout⟩
  rw [Work.GW2.cosetInvCount]
  exact congrArg Set.ncard hset

/-- **The counting identity.**  The involutions `u` outside `H` whose coset `u H` contains exactly
two involutions number twice the number of such cosets. -/
theorem ncard_cosetInvCount_eq_two {G : Type} [Group G] [Finite G] (H : Subgroup G) :
    ({u : G | orderOf u = 2 ∧ u ∉ H ∧ Work.GW2.cosetInvCount H u = 2} : Set G).ncard
      = 2 * Work.GW2.bCount H 2 := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  let P : G ⧸ H → Prop := fun c =>
    c ≠ ((1 : G) : G ⧸ H) ∧ Work.GW2.cosetInvCount H (Quotient.out c) = 2
  have hfiber_pos : ∀ c ∈ Finset.univ.filter P,
      ({u : G | (orderOf u = 2 ∧ u ∉ H ∧ Work.GW2.cosetInvCount H u = 2)
        ∧ (u : G ⧸ H) = c} : Set G).ncard =
        Work.GW2.cosetInvCount H (Quotient.out c) := by
    intro c hc
    have hcP : P c := (Finset.mem_filter.mp hc).2
    have hc1 : c ≠ ((1 : G) : G ⧸ H) := hcP.1
    have hc2 : Work.GW2.cosetInvCount H (Quotient.out c) = 2 := hcP.2
    have hout : ((Quotient.out c : G) : G ⧸ H) = c := Quotient.out_eq c
    have hset : ({u : G | (orderOf u = 2 ∧ u ∉ H ∧ Work.GW2.cosetInvCount H u = 2)
          ∧ (u : G ⧸ H) = c} : Set G)
        = {u : G | orderOf u = 2 ∧ (u : G ⧸ H) = c} := by
      ext u
      constructor
      · rintro ⟨⟨hu2, -, -⟩, huc⟩
        exact ⟨hu2, huc⟩
      · rintro ⟨hu2, huc⟩
        have huH : u ∉ H := by
          intro hmem
          have h1 : (u : G ⧸ H) = ((1 : G) : G ⧸ H) :=
            QuotientGroup.eq.mpr (by simpa using H.inv_mem hmem)
          exact hc1 (huc.symm.trans h1)
        have hcnt : Work.GW2.cosetInvCount H u = 2 := by
          rw [Work.BSW.Cases.K4.cosetInvCount_eq_of_mk_eq H (huc.trans hout.symm)]
          exact hc2
        exact ⟨⟨hu2, huH, hcnt⟩, huc⟩
    rw [hset]
    exact fiber_ncard_eq_cosetInvCount H c
  have hfiber_zero : ∀ c ∈ Finset.univ, c ∉ Finset.univ.filter P →
      ({u : G | (orderOf u = 2 ∧ u ∉ H ∧ Work.GW2.cosetInvCount H u = 2)
        ∧ (u : G ⧸ H) = c} : Set G).ncard = 0 := by
    intro c _ hc
    have hnc : ¬ (c ≠ ((1 : G) : G ⧸ H) ∧
        Work.GW2.cosetInvCount H (Quotient.out c) = 2) :=
      fun h => hc (Finset.mem_filter.mpr ⟨Finset.mem_univ c, h⟩)
    have hempty : ({u : G | (orderOf u = 2 ∧ u ∉ H ∧ Work.GW2.cosetInvCount H u = 2)
        ∧ (u : G ⧸ H) = c} : Set G) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro u ⟨⟨hu2, huH, hcnt⟩, huc⟩
      have hout : ((Quotient.out c : G) : G ⧸ H) = c := Quotient.out_eq c
      rcases not_and_or.mp hnc with h1 | h2
      · have hc1 : c = ((1 : G) : G ⧸ H) := not_not.mp h1
        have h1' : (u : G ⧸ H) = ((1 : G) : G ⧸ H) := huc.trans hc1
        have hmem : u⁻¹ ∈ H := by
          have := QuotientGroup.eq.mp h1'
          simpa using this
        exact huH (inv_mem_iff.mp hmem)
      · have heq : Work.GW2.cosetInvCount H u = Work.GW2.cosetInvCount H (Quotient.out c) :=
          Work.BSW.Cases.K4.cosetInvCount_eq_of_mk_eq H (huc.trans hout.symm)
        exact h2 (heq ▸ hcnt)
    rw [hempty, Set.ncard_empty]
  rw [ncard_eq_sum_ncard_fiber (fun u : G => (u : G ⧸ H))
    (fun u : G => orderOf u = 2 ∧ u ∉ H ∧ Work.GW2.cosetInvCount H u = 2)]
  have hstep : (∑ c : G ⧸ H,
        ({u : G | (orderOf u = 2 ∧ u ∉ H ∧ Work.GW2.cosetInvCount H u = 2)
          ∧ (u : G ⧸ H) = c} : Set G).ncard)
      = ∑ c ∈ Finset.univ.filter P,
        ({u : G | (orderOf u = 2 ∧ u ∉ H ∧ Work.GW2.cosetInvCount H u = 2)
          ∧ (u : G ⧸ H) = c} : Set G).ncard :=
    (Finset.sum_subset (Finset.filter_subset (p := P) Finset.univ)
      (fun c _ hc => hfiber_zero c (Finset.mem_univ c) hc)).symm
  rw [hstep]
  rw [Finset.sum_congr rfl (fun c hc => hfiber_pos c hc)]
  -- every remaining term equals `2`
  rw [Finset.sum_congr rfl (fun c hc => (Finset.mem_filter.mp hc).2.2)]
  have hconst : (∑ c ∈ Finset.univ.filter P, (2 : ℕ)) = (Finset.univ.filter P).card * 2 :=
    Finset.sum_const_nat (fun c _ => rfl)
  rw [hconst]
  have hK2 : (Finset.univ.filter P).card = Work.GW2.bCount H 2 := by
    show (Finset.univ.filter P).card =
      ({c : G ⧸ H | c ≠ ((1 : G) : G ⧸ H) ∧
        Work.GW2.cosetInvCount H (Quotient.out c) = 2} : Set (G ⧸ H)).ncard
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]
  rw [hK2, Nat.mul_comm]

theorem case1H_U2_card {G : Type} [Group G] [Finite G] (H : Subgroup G)
    (hcoset : ∀ u : G, orderOf u = 2 → u ∉ H →
      ({y : G | orderOf y = 2 ∧ ∃ h ∈ H, y = h * u} : Set G).ncard =
        Nat.card ↥(Subgroup.centralizer ({u} : Set G) ⊓ H)) :
    ({u : G | u ∉ H ∧ orderOf u = 2 ∧
        Nat.card ↥(Subgroup.centralizer ({u} : Set G) ⊓ H) = 2} : Set G).ncard
      = 2 * Work.GW2.bCount H 2 := by
  have hset : ({u : G | u ∉ H ∧ orderOf u = 2 ∧
        Nat.card ↥(Subgroup.centralizer ({u} : Set G) ⊓ H) = 2} : Set G)
      = {u : G | orderOf u = 2 ∧ u ∉ H ∧ Work.GW2.cosetInvCount H u = 2} := by
    ext u
    constructor
    · rintro ⟨huH, hu2, hc⟩
      exact ⟨hu2, huH, by
        rw [cosetInvCount_rightCount H u, hcoset u hu2 huH]
        exact hc⟩
    · rintro ⟨hu2, huH, hc⟩
      exact ⟨huH, hu2, by
        rw [← hcoset u hu2 huH, ← cosetInvCount_rightCount H u]
        exact hc⟩
  rw [hset, ncard_cosetInvCount_eq_two]

end Work.BSW.Cases.K4
