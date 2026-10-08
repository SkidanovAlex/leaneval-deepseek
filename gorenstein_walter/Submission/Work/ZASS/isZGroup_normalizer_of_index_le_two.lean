import Mathlib

/-!
# The normalizer of an odd Z-group of index at most two is a Z-group

A *Z-group* (Mathlib class `IsZGroup`) is a group all of whose Sylow subgroups are cyclic.
The main result of this file, `Work.ZASS.isZGroup_normalizer_of_index_le_two`, says that if
`H ≤ G` is a Z-group of **odd** order whose index in its normalizer is at most `2`, then the
normalizer of `H` is again a Z-group.

The mathematical content is a case analysis on a prime `p` and a Sylow `p`-subgroup `P` of
`N = N_G(H)`.  Since `[N : H] ≤ 2`:

* for `p` odd, `p ∤ [N : H]`, so the `p`-part of `|N|` is the `p`-part of `|H|`; hence `P` is
  isomorphic to a subgroup of the Z-group `H` and is cyclic;
* for `p = 2`, `|P|` is the `2`-part of `|N| = |H| · [N : H]`, and since `|H|` is odd this
  divides `[N : H] ∣ 2`; so `|P| ≤ 2` and `P` is cyclic.

Formally the whole argument is packaged using the Mathlib lemma `isZGroup_of_coprime` ("an
extension of coprime Z-groups is a Z-group"): `N` is an extension of its normal subgroup
`Q = H.subgroupOf N ≅ H` (odd, a Z-group) by the quotient `N ⧸ Q`, which has order at most `2`
and is therefore cyclic — whence a Z-group — of order coprime to `|H|`.

The oddness hypothesis is essential: `H = C₄ ≤ Q₈` has `[Q₈ : H] = 2` and `H` a Z-group, but
`Q₈` is not a Z-group.
-/

namespace Work.ZASS

/-- A finite group of cardinality at most `2` is cyclic. -/
theorem isCyclic_of_natCard_le_two {K : Type} [Group K] [Finite K] (h : Nat.card K ≤ 2) :
    IsCyclic K := by
  have hpos : 0 < Nat.card K := Nat.card_pos
  have hcases : Nat.card K = 1 ∨ Nat.card K = 2 := by omega
  have hdvd : Nat.card K ∣ 2 := by
    rcases hcases with h1 | h1
    · rw [h1]; norm_num
    · rw [h1]
  exact isCyclic_of_card_dvd_prime (p := 2) hdvd

/-- If `H` is a Z-group of odd order whose index in its normalizer `N_G(H)` is at most `2`, then
`N_G(H)` is a Z-group. -/
theorem isZGroup_normalizer_of_index_le_two {G : Type} [Group G] [Finite G] {H : Subgroup G} (hH : IsZGroup ↥H) (hodd : Odd (Nat.card H)) (hidx : (H.subgroupOf (Subgroup.normalizer (H : Set G))).index ≤ 2) : IsZGroup ↥(Subgroup.normalizer (H : Set G)) := by
  -- `N` is the normalizer of `H`, and `Q = H.subgroupOf N` is a normal subgroup of `N`
  -- isomorphic to `H`.
  let N : Subgroup G := Subgroup.normalizer (H : Set G)
  have hHN : H ≤ N := Subgroup.le_normalizer
  let Q : Subgroup ↥N := H.subgroupOf N
  have hidxQ : Q.index ≤ 2 := hidx
  have hQnormal : Q.Normal := Subgroup.normal_subgroupOf_of_le_normalizer le_rfl
  -- `Q` is a Z-group, being isomorphic to `H`
  have hZQ : IsZGroup ↥Q :=
    IsZGroup.of_injective (f := (Subgroup.subgroupOfEquivOfLe hHN).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hHN).injective
  -- the quotient `N ⧸ Q ≅ N / H`, of order `[N : H] ≤ 2`, is cyclic, hence a Z-group
  have hcyc : IsCyclic (↥N ⧸ Q) := by
    refine isCyclic_of_natCard_le_two ?_
    rw [← Subgroup.index_eq_card]
    exact hidxQ
  have hQuotZ : IsZGroup (↥N ⧸ Q) := by
    have := hcyc
    infer_instance
  -- `|Q| = |H|` is odd, hence coprime to the order `[N : H] ≤ 2` of the quotient
  have hQcard : Nat.card ↥Q = Nat.card ↥H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHN).toEquiv
  have hcop : (Nat.card ↥Q).Coprime (Nat.card (↥N ⧸ Q)) := by
    rw [hQcard, ← Subgroup.index_eq_card]
    have hne : Q.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hcases : Q.index = 1 ∨ Q.index = 2 := by omega
    rcases hcases with h1 | h1
    · rw [h1]; exact Nat.coprime_one_right _
    · rw [h1]; exact Nat.coprime_two_right.mpr hodd
  -- the coprime extension `Q ◁ N` of Z-groups is a Z-group
  exact isZGroup_of_coprime (f := Q.subtype) (f' := QuotientGroup.mk' Q)
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype]) hcop

end Work.ZASS
