import Mathlib

/-!
# `Work.CORE4.L2PAux.le_centralizer_of_odd_le_normalizer_of_card_two_mul`

Let `Y` be a subgroup of a finite group `G`, and let `C = C_G(Y)` and `N = N_G(Y)` be its
centralizer and normalizer.  The hypothesis `Nat.card N = 2 * Nat.card C` says that `C` has index
two in `N`.  Then any subgroup `T ≤ N` of odd order lies in `C`.

This is the elementary group-theoretic core used throughout the Gorenstein–Walter argument: in a
group `N` with a subgroup `C` of index two every element squares into `C`
(`Subgroup.sq_mem_of_index_two`, which needs no normality of `C`), and an element of odd order is a
power of its own square, hence lies in `C`.

The two ingredients are:

* `Subgroup.sq_mem_of_index_two` — the square of any element lies in a subgroup of index two;
* the arithmetic identity `g = (g ^ 2) ^ (m + 1)` when `orderOf g = 2 * m + 1`.
-/

namespace Work.CORE4.L2PAux

/-! ## Two elementary lemmas -/

/-- An odd order divisor of an odd number is odd.  Only the `ℕ` instance is needed here. -/
private lemma odd_of_dvd_odd {n m : ℕ} (h : n ∣ m) (hm : Odd m) : Odd n :=
  Nat.not_even_iff_odd.mp fun hn => hm.not_two_dvd_nat ((even_iff_two_dvd.mp hn).trans h)

/-- An element of odd order lies in every subgroup of index two.

If `orderOf g = 2 * m + 1` then `g = g ^ (2 * m + 2) = (g ^ 2) ^ (m + 1)`, and `g ^ 2 ∈ H` because
`H` has index two (`Subgroup.sq_mem_of_index_two`). -/
private lemma mem_of_odd_orderOf_of_index_two {G : Type*} [Group G] (H : Subgroup G)
    (hidx : H.index = 2) (g : G) (hodd : Odd (orderOf g)) : g ∈ H := by
  obtain ⟨m, hm⟩ := hodd
  have hpow : g ^ (2 * m + 1) = 1 := by rw [← hm]; exact pow_orderOf_eq_one g
  have hsq : g ^ 2 ∈ H := Subgroup.sq_mem_of_index_two hidx g
  have h2 : (g ^ 2) ^ (m + 1) = g := by
    rw [← pow_mul, show 2 * (m + 1) = 2 * m + 1 + 1 by ring, pow_succ, hpow, one_mul]
  rw [← h2]
  exact H.pow_mem hsq (m + 1)

/-! ## The main theorem -/

/-- **Odd-order subgroups of a subgroup of index two.**  Let `Y ≤ G`, `C = C_G(Y)`, `N = N_G(Y)`
with `|N| = 2 |C|`.  Then any subgroup `T ≤ N` of odd order is contained in `C`.

Proof: `C ≤ N` (`Subgroup.centralizer_le_normalizer`), so `C.subgroupOf N` has index two in `N`.
Every element `u ∈ T` lies in `N` and has odd order (dividing the odd number `|T|`), so by
`mem_of_odd_orderOf_of_index_two` it lies in `C.subgroupOf N`, i.e. in `C`. -/
theorem le_centralizer_of_odd_le_normalizer_of_card_two_mul {G : Type*} [Group G] [Finite G] {Y T : Subgroup G} (hTN : T ≤ Subgroup.normalizer (Y : Set G)) (hodd : Odd (Nat.card T)) (hcard : Nat.card (Subgroup.normalizer (Y : Set G)) = 2 * Nat.card (Subgroup.centralizer (Y : Set G))) : T ≤ Subgroup.centralizer (Y : Set G) := by
  classical
  let N : Subgroup G := Subgroup.normalizer (Y : Set G)
  let C : Subgroup G := Subgroup.centralizer (Y : Set G)
  -- `C ≤ N`, so we may view `C` as a subgroup of `N`.
  have hCN : C ≤ N := Subgroup.centralizer_le_normalizer (Y : Set G)
  have hcardN : Nat.card N = 2 * Nat.card C := hcard
  have hDcard : Nat.card ↥(C.subgroupOf N) = Nat.card C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCN).toEquiv
  -- hence `C.subgroupOf N` has index two in `N`.
  have hidx : (C.subgroupOf N).index = 2 := by
    have h1 := Subgroup.card_mul_index (C.subgroupOf N)
    rw [hDcard, hcardN] at h1
    exact Nat.mul_left_cancel (Nat.card_pos (α := ↥C)) (by rw [h1, mul_comm])
  intro u hu
  have huN : u ∈ N := hTN hu
  -- `u ∈ T` has odd order, since it divides `|T|` which is odd.
  have hdiv : orderOf u ∣ Nat.card T := by
    have h := orderOf_dvd_natCard (⟨u, hu⟩ : ↥T)
    rw [← Subgroup.orderOf_coe (⟨u, hu⟩ : ↥T)] at h
    exact h
  have hodd_u : Odd (orderOf u) := odd_of_dvd_odd hdiv hodd
  -- so `u ∈ C.subgroupOf N`, hence `u ∈ C`.
  have hmem : (⟨u, huN⟩ : ↥N) ∈ C.subgroupOf N := by
    apply mem_of_odd_orderOf_of_index_two _ hidx
    rw [← Subgroup.orderOf_coe (⟨u, huN⟩ : ↥N)]
    exact hodd_u
  exact Subgroup.mem_subgroupOf.mp hmem

end Work.CORE4.L2PAux
