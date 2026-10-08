import Mathlib
import Submission.Work.AUTA7.A7.CentralizerOrderThree
import Submission.Work.AUTA7.A7.A7KNoOrderFour
import Submission.Work.CORE4.NotA7.InvolutionFixesCycleSupport
import Submission.Work.CORE4.NotA7.CommutingInvolutionsLeThree

namespace Work.CORE4.NotA7

open Equiv

/-!
# Uniqueness of the subgroup of order `4` in the `A₇`-centralizer of an order-`3` element

Let `x ∈ A₇` have order `3`.  As a permutation of `Fin 7` its cycle type is `{3}` (a `3`-cycle)
or `{3,3}` (a product of two disjoint `3`-cycles, see
`Work.AUTA7.A7.cycleType_eq_three_or_three_three`).

* If `x` is a `3`-cycle then `C_{A₇}(x)` contains no element of order `4`
  (`noOrderFourInCentralizer`: `x` and an element of order `4` commute with coprime orders, so their
  product would have order `12`, which is impossible in `A₇` by
  `Work.AUTA7.A7.no_dvd_twelve_orderOf_alternatingGroup`), and the number of involutions commuting
  with `x` is at most `3` (`CommutingInvolutionsLeThree`).  Hence any subgroup `W ≤ C_{A₇}(x)` of
  order `4` consists of `1` together with *all* involutions of `C_{A₇}(x)`, so it is unique.

* If `x` has cycle type `{3,3}` then `Nat.card (C_{A₇}(x))` divides `18`
  (`card_centralizer_dvd_18`), so `4` cannot divide the order of a subgroup of `C_{A₇}(x)`; there
  is no subgroup of order `4` at all.

The group-theoretic assembly of the first case is isolated in
`eq_of_card_four_of_centralizer`.
-/

/-- **No element of the `A₇`-centralizer of an order-`3` element has order `4`.**

If `y ∈ C_{A₇}(x)` had order `4`, then `x` and `y` commute with coprime orders `3` and `4`, so
`x * y` would have order `12`, which is impossible in `A₇`. -/
theorem noOrderFourInCentralizer (x : alternatingGroup (Fin 7)) (hx : orderOf x = 3) :
    ∀ y ∈ Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 7))), orderOf y ≠ 4 := by
  intro y hy hy4
  have hcomm : Commute x y := Subgroup.mem_centralizer_iff.mp hy x (Set.mem_singleton x)
  have h12 : orderOf (x * y) = 12 := by
    rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hx, hy4]; norm_num), hx, hy4]
  exact Work.AUTA7.A7.no_dvd_twelve_orderOf_alternatingGroup (x * y) ⟨1, by simp [h12]⟩

/-- **The `A₇`-centralizer of an element of cycle type `{3,3}` has order dividing `18`.**

Such an element is the product of two disjoint `3`-cycles; its centralizer in `S₇` has order
`(7 - 6)! · 3² · 2! = 18` (`Equiv.Perm.nat_card_centralizer`), and the centralizer in `A₇` is the
intersection with the index-`2` subgroup `A₇` (`Work.AUTA7.A7.nat_card_centralizer_coe`), hence a
subgroup of a group of order `18`. -/
theorem card_centralizer_dvd_18 (x : alternatingGroup (Fin 7)) (_hx : orderOf x = 3)
    (hcyc : (x : Equiv.Perm (Fin 7)).cycleType = ({3, 3} : Multiset ℕ)) :
    Nat.card ↥(Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 7)))) ∣ 18 := by
  classical
  rw [Work.AUTA7.A7.nat_card_centralizer_coe x]
  have hcardS : Nat.card ↥(Subgroup.centralizer
      ({(x : Equiv.Perm (Fin 7))} : Set (Equiv.Perm (Fin 7)))) = 18 := by
    rw [Equiv.Perm.nat_card_centralizer, hcyc]
    norm_num
  calc Nat.card ↥((alternatingGroup (Fin 7) : Subgroup (Equiv.Perm (Fin 7))) ⊓
          Subgroup.centralizer ({(x : Equiv.Perm (Fin 7))} : Set (Equiv.Perm (Fin 7))))
      ∣ Nat.card ↥(Subgroup.centralizer
          ({(x : Equiv.Perm (Fin 7))} : Set (Equiv.Perm (Fin 7)))) :=
        Subgroup.card_dvd_of_le inf_le_right
    _ = 18 := hcardS

/-- **Group-theoretic assembly.**  Let `x` be an element of a finite group `G` such that
`C_G(x)` has no element of order `4` and at most three involutions.  Then `C_G(x)` contains at
most one subgroup of order `4`.

Indeed, every element of a subgroup `W ≤ C_G(x)` of order `4` is `1` or an involution of `C_G(x)`,
so `W ⊆ {1} ∪ Inv` where `Inv` is the set of involutions of `C_G(x)`; the right-hand side is a set
with at most `4` elements, so `W` equals it. -/
theorem eq_of_card_four_of_centralizer {G : Type*} [Group G] [Finite G] (x : G)
    (hno4 : ∀ y ∈ Subgroup.centralizer ({x} : Set G), orderOf y ≠ 4)
    (hcount : Nat.card {y : G // y ∈ Subgroup.centralizer ({x} : Set G) ∧ orderOf y = 2} ≤ 3)
    (W₁ W₂ : Subgroup G)
    (h₁ : W₁ ≤ Subgroup.centralizer ({x} : Set G))
    (h₂ : W₂ ≤ Subgroup.centralizer ({x} : Set G))
    (hc₁ : Nat.card ↥W₁ = 4) (hc₂ : Nat.card ↥W₂ = 4) : W₁ = W₂ := by
  classical
  have hInv : {y : G | y ∈ Subgroup.centralizer ({x} : Set G) ∧ orderOf y = 2}.ncard ≤ 3 := by
    rw [← Nat.card_coe_set_eq]
    exact hcount
  have hone : (1 : G) ∉ {y : G | y ∈ Subgroup.centralizer ({x} : Set G) ∧ orderOf y = 2} := by
    simp [orderOf_one]
  have hU : ({1} ∪ {y : G | y ∈ Subgroup.centralizer ({x} : Set G) ∧ orderOf y = 2} : Set G).ncard
      ≤ 4 := by
    rw [Set.singleton_union, Set.ncard_insert_of_notMem hone]
    omega
  have hmem : ∀ (W : Subgroup G), W ≤ Subgroup.centralizer ({x} : Set G) → Nat.card ↥W = 4 →
      (W : Set G) ⊆
        ({1} ∪ {y : G | y ∈ Subgroup.centralizer ({x} : Set G) ∧ orderOf y = 2}) := by
    intro W hW hcW w hw
    rcases eq_or_ne w 1 with hw1 | hw1
    · exact Or.inl (by simpa using hw1)
    · refine Or.inr ⟨hW hw, ?_⟩
      have hdvd : orderOf w ∣ 4 := by
        have h := orderOf_dvd_natCard (⟨w, hw⟩ : ↥W)
        have h2 : orderOf (⟨w, hw⟩ : ↥W) = orderOf w := (Subgroup.orderOf_coe ⟨w, hw⟩).symm
        rw [h2, hcW] at h
        exact h
      have hle : orderOf w ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
      have hpos : 0 < orderOf w := Nat.pos_of_dvd_of_pos hdvd (by norm_num)
      have hcases : orderOf w = 1 ∨ orderOf w = 2 ∨ orderOf w = 3 ∨ orderOf w = 4 := by omega
      rcases hcases with h | h | h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hw1
      · exact h
      · rw [h] at hdvd; exact absurd hdvd (by norm_num)
      · exact absurd h (hno4 w (hW hw))
  have hcard : ∀ (W : Subgroup G), Nat.card ↥W = 4 → (W : Set G).ncard = 4 := by
    intro W h
    rw [← Nat.card_coe_set_eq]
    exact h
  have e₁ : (W₁ : Set G) =
      ({1} ∪ {y : G | y ∈ Subgroup.centralizer ({x} : Set G) ∧ orderOf y = 2}) :=
    Set.eq_of_subset_of_ncard_le (hmem W₁ h₁ hc₁) (by rw [hcard W₁ hc₁]; exact hU)
  have e₂ : (W₂ : Set G) =
      ({1} ∪ {y : G | y ∈ Subgroup.centralizer ({x} : Set G) ∧ orderOf y = 2}) :=
    Set.eq_of_subset_of_ncard_le (hmem W₂ h₂ hc₂) (by rw [hcard W₂ hc₂]; exact hU)
  exact SetLike.ext' (e₁.trans e₂.symm)

/-- **Uniqueness of the subgroup of order `4` in the centralizer of an order-`3` element of
`A₇`.** -/
theorem A7CentralizerUniqueFour :
    ∀ x : alternatingGroup (Fin 7), orderOf x = 3 →
      ∀ W₁ W₂ : Subgroup (alternatingGroup (Fin 7)),
        W₁ ≤ Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 7))) →
        W₂ ≤ Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 7))) →
        Nat.card ↥W₁ = 4 → Nat.card ↥W₂ = 4 → W₁ = W₂ := by
  intro x hx W₁ W₂ h₁ h₂ hc₁ hc₂
  rcases Work.AUTA7.A7.cycleType_eq_three_or_three_three hx with hcyc | hcyc
  · -- `x` is a `3`-cycle
    apply eq_of_card_four_of_centralizer x (noOrderFourInCentralizer x hx) _ W₁ W₂ h₁ h₂ hc₁ hc₂
    have hIsCycle : (x : Equiv.Perm (Fin 7)).IsCycle := by
      rw [← Equiv.Perm.card_cycleType_eq_one, hcyc]; decide
    have hsupp : (x : Equiv.Perm (Fin 7)).support.card = 3 := by
      rw [← Equiv.Perm.sum_cycleType, hcyc]; decide
    exact CommutingInvolutionsLeThree hsupp
      (fun y hy hy2 => InvolutionFixesCycleSupport hIsCycle hy hy2)
  · -- `x` is a product of two disjoint `3`-cycles: `4 ∤ |C_{A₇}(x)|`
    exfalso
    have hdvd := card_centralizer_dvd_18 x hx hcyc
    have h4 : 4 ∣ Nat.card ↥(Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 7)))) := by
      rw [← hc₁]
      exact Subgroup.card_dvd_of_le h₁
    have : (4 : ℕ) ∣ 18 := h4.trans hdvd
    norm_num at this

end Work.CORE4.NotA7
