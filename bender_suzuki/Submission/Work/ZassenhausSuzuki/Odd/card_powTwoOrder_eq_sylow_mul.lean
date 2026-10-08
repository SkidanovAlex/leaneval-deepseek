import Mathlib
import Submission.Work.ZassenhausSuzuki.Odd.OddDefs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Counting the non-identity elements of `2`-power order

Let `G` be a finite group whose Sylow `2`-subgroups intersect trivially away from the identity
(`huniq`: two Sylow `2`-subgroups sharing a non-identity element coincide) and such that every
element of `2`-power order lies in some Sylow `2`-subgroup (`hex`).  Then the non-identity
elements of `2`-power order are partitioned by the Sylow `2`-subgroups, and each Sylow
`2`-subgroup contributes exactly `|P₀| - 1` of them:

`#{x : G | x ≠ 1 ∧ orderOf x = 2^k} = #(Sylow 2 G) · (|P₀| - 1)`.

This is the elementary counting step in the proof of the Bender–Suzuki theorem: in a group
with a strongly embedded subgroup (in particular in a Suzuki group) the Sylow `2`-subgroups
intersect trivially away from the identity.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace Work.ZassenhausSuzuki.Odd

variable {G : Type} [Group G] [Finite G]

/-- Every element of a Sylow `2`-subgroup has `2`-power order. -/
private theorem powTwoOrder_of_mem_sylow (P : Sylow 2 G) (x : ↥P) : PowTwoOrder (x : G) := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf).mp P.isPGroup' x
  exact ⟨k, by rw [Subgroup.orderOf_coe]; exact hk⟩

/-- All Sylow `2`-subgroups of a finite group have the same order: they are conjugate, and
`Sylow.equiv` exhibits an explicit multiplicative equivalence between any two of them. -/
private theorem sylow_card_eq (P P' : Sylow 2 G) :
    Nat.card ↥(P : Subgroup G) = Nat.card ↥(P' : Subgroup G) :=
  Nat.card_congr (Sylow.equiv P P').toEquiv

/-- A finite group has exactly `|H| - 1` non-identity elements. -/
private theorem card_ne_one_eq (H : Type) [Group H] [Finite H] :
    Nat.card {x : H // x ≠ 1} = Nat.card H - 1 := by
  letI : Fintype H := Fintype.ofFinite H
  have h1 : Nat.card {x : H // x ≠ 1} =
      (Finset.univ.filter (fun x : H => x ≠ 1)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [h1, Nat.card_eq_fintype_card, ← Finset.card_univ (α := H),
    ← Finset.card_erase_of_mem (Finset.mem_univ (1 : H))]
  congr 1
  ext x
  simp [Finset.mem_erase, and_comm]

/-- The non-identity elements of a subgroup, counted inside the ambient group: mapping
`x ∈ H`, `x ≠ 1` to `⟨x, _⟩ ∈ H` identifies `{x : G // x ∈ H ∧ x ≠ 1}` with the non-identity
elements of the group `H`. -/
private theorem card_mem_ne_one (H : Subgroup G) :
    Nat.card {x : G // x ∈ H ∧ x ≠ 1} = Nat.card ↥H - 1 := by
  have h2 : Nat.card {x : G // x ∈ H ∧ x ≠ 1} = Nat.card {y : ↥H // (y : G) ≠ 1} :=
    Nat.card_congr
      { toFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
        invFun := fun y => ⟨y.1.1, y.1.2, y.2⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
  have h3 : Nat.card {y : ↥H // (y : G) ≠ 1} = Nat.card {y : ↥H // y ≠ 1} :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun y => by
      rw [ne_eq, ne_eq, OneMemClass.coe_eq_one]))
  rw [h2, h3, card_ne_one_eq ↥H]

/-- **Counting the non-identity elements of `2`-power order.**  If the Sylow `2`-subgroups of a
finite group `G` intersect trivially away from `1` and every element of `2`-power order lies in
a Sylow `2`-subgroup, then the number of non-identity elements of `2`-power order equals
`#(Sylow 2 G) · (|P₀| - 1)`. -/
theorem card_powTwoOrder_eq_sylow_mul {G : Type} [Group G] [Finite G]
    (huniq : ∀ (P P' : Sylow 2 G) (x : G), x ∈ P → x ∈ P' → x ≠ 1 → P = P')
    (hex : ∀ x : G, x ≠ 1 → Work.ZassenhausSuzuki.Odd.PowTwoOrder x → ∃ P : Sylow 2 G, x ∈ P)
    (P₀ : Sylow 2 G) :
    Nat.card {x : G // x ≠ 1 ∧ Work.ZassenhausSuzuki.Odd.PowTwoOrder x}
      = Nat.card (Sylow 2 G) * (Nat.card ↥P₀ - 1) := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  letI : Fintype (Sylow 2 G) := Fintype.ofFinite (Sylow 2 G)
  have hS : Nat.card {x : G // x ≠ 1 ∧ PowTwoOrder x} =
      (Finset.univ.filter (fun x : G => x ≠ 1 ∧ PowTwoOrder x)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hUnion : (Finset.univ.filter (fun x : G => x ≠ 1 ∧ PowTwoOrder x)) =
      (Finset.univ : Finset (Sylow 2 G)).biUnion
        (fun P => Finset.univ.filter (fun x : G => x ∈ (P : Subgroup G) ∧ x ≠ 1)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
    constructor
    · rintro ⟨hx1, hx2⟩
      obtain ⟨P, hxP⟩ := hex x hx1 hx2
      exact ⟨P, hxP, hx1⟩
    · rintro ⟨P, hxP, hx1⟩
      exact ⟨hx1, powTwoOrder_of_mem_sylow P ⟨x, hxP⟩⟩
  have hDisj : ((Finset.univ : Finset (Sylow 2 G)) : Set (Sylow 2 G)).PairwiseDisjoint
      (fun P => Finset.univ.filter (fun x : G => x ∈ (P : Subgroup G) ∧ x ≠ 1)) := by
    intro P _ P' _ hne
    show Disjoint (Finset.univ.filter (fun x : G => x ∈ (P : Subgroup G) ∧ x ≠ 1))
      (Finset.univ.filter (fun x : G => x ∈ (P' : Subgroup G) ∧ x ≠ 1))
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hx'
    exact hne (huniq P P' x hx.1 hx'.1 hx.2)
  have hcard : (Finset.univ.filter (fun x : G => x ≠ 1 ∧ PowTwoOrder x)).card =
      ∑ P : Sylow 2 G,
        (Finset.univ.filter (fun x : G => x ∈ (P : Subgroup G) ∧ x ≠ 1)).card := by
    rw [hUnion, Finset.card_biUnion hDisj]
  have hterm : ∀ P : Sylow 2 G,
      (Finset.univ.filter (fun x : G => x ∈ (P : Subgroup G) ∧ x ≠ 1)).card =
        Nat.card ↥P₀ - 1 := by
    intro P
    have h1 : Nat.card {x : G // x ∈ (P : Subgroup G) ∧ x ≠ 1} =
        (Finset.univ.filter (fun x : G => x ∈ (P : Subgroup G) ∧ x ≠ 1)).card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [← h1, card_mem_ne_one (P : Subgroup G)]
    exact congrArg (fun n => n - 1) (sylow_card_eq P P₀)
  have hsum : (∑ P : Sylow 2 G,
        (Finset.univ.filter (fun x : G => x ∈ (P : Subgroup G) ∧ x ≠ 1)).card) =
      ∑ _P : Sylow 2 G, (Nat.card ↥P₀ - 1) :=
    Finset.sum_congr rfl (fun P _ => hterm P)
  rw [hS, hcard, hsum, Finset.sum_const_nat (fun _ _ => rfl), Finset.card_univ,
    ← Nat.card_eq_fintype_card]

end Work.ZassenhausSuzuki.Odd
