import Mathlib
import Submission.Work.ThreePoints.Basic
import Submission.Work.Reductions.stronglyEmbedded_subgroupOf

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Strong embeddedness passes to a normal subgroup of odd index

`Work.ThreePoints.isStronglyEmbedded_inf_subgroupOf`: if `H` is strongly embedded in `G` and
`L ◁ G` is a normal subgroup of *odd* index which is not contained in `H`, then
`(H ⊓ L).subgroupOf L` is strongly embedded in `L`.

The whole content is the evenness of the order of `H ⊓ L`, and this is a purely arithmetic
consequence of two index computations.

* `Odd ((H ⊓ L).relIndex H)`: the index of `H ⊓ L` in `H`.  Since `L ◁ G` we have
  `L.relIndex H = (H ⊓ L).relIndex H` (`inf_relIndex_right`) and `L.relIndex H ∣ L.index`
  (`relIndex_dvd_index_of_normal`); a divisor of the odd number `L.index` is odd.
* `Nat.card ↥H = (H ⊓ L).relIndex H * Nat.card ↥(H ⊓ L)`: `Subgroup.index_mul_card` applied
  inside the group `H`, together with the fact that `(H ⊓ L).subgroupOf H` and `H ⊓ L` have
  the same cardinality (they correspond under the inclusion `H ↪ G`).
  So `|H| = odd · |H ⊓ L|` is even, and the odd factor may be cancelled.

Once `H ⊓ L` has even order, the transfer of strong embeddedness from `H` to `(H ⊓ L).subgroupOf L`
is the general lemma `Work.Reductions.stronglyEmbedded_subgroupOf` (it only uses that
conjugating an element of `L \ H` by an element of `L` is conjugation by an element of `G \ H`,
so that the relevant intersections have odd order).
-/

set_option autoImplicit false

open LeanEval.GroupTheory.Defs

namespace Work.ThreePoints

/-- For a normal `L ◁ G` of odd index, the index of `H ⊓ L` in `H` is odd: by
`Subgroup.inf_relIndex_right` this index is `L.relIndex H`, which divides `L.index`
(`Subgroup.relIndex_dvd_index_of_normal`), an odd number. -/
theorem odd_relIndex_inf_of_normal_of_odd_index {G : Type} [Group G] {H L : Subgroup G}
    (hL : L.Normal) (hidx : Odd L.index) : Odd ((H ⊓ L).relIndex H) := by
  have hdvd : L.relIndex H ∣ L.index := Subgroup.relIndex_dvd_index_of_normal (H := L) (K := H)
  obtain ⟨k, hk⟩ := hdvd
  have h1 : Odd (L.relIndex H * k) := hk ▸ hidx
  have h2 : Odd (L.relIndex H) := Nat.Odd.of_mul_left h1
  rwa [inf_comm, Subgroup.inf_relIndex_right]

/-- If `H` has even order and the index of `H ⊓ L` in `H` is odd, then `H ⊓ L` has even order:
`|H| = [H : H ⊓ L] · |H ⊓ L|` and an even product with an odd factor has an even other
factor. -/
theorem even_card_inf_of_odd_relIndex {G : Type} [Group G] {H L : Subgroup G}
    (hH : Even (Nat.card ↥H)) (hodd : Odd ((H ⊓ L).relIndex H)) :
    Even (Nat.card ↥(H ⊓ L)) := by
  -- `(H ⊓ L).subgroupOf H` and `H ⊓ L` are the two sides of `H ≤ G` of one another.
  have hcard : Nat.card ↥((H ⊓ L).subgroupOf H) = Nat.card ↥(H ⊓ L) := by
    rw [← Subgroup.card_map_of_injective (K := (H ⊓ L).subgroupOf H) (f := H.subtype)
        H.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le inf_le_left]
  -- Lagrange inside the group `H`.
  have hmain : (H ⊓ L).relIndex H * Nat.card ↥(H ⊓ L) = Nat.card ↥H := by
    have h := Subgroup.index_mul_card ((H ⊓ L).subgroupOf H)
    rw [hcard] at h
    exact h
  have hprod : Even ((H ⊓ L).relIndex H * Nat.card ↥(H ⊓ L)) := hmain ▸ hH
  rcases Nat.even_mul.mp hprod with h | h
  · exact absurd h (Nat.not_even_iff_odd.mpr hodd)
  · exact h

theorem isStronglyEmbedded_inf_subgroupOf {G : Type} [Group G] {H L : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) (hL : L.Normal) (hidx : Odd L.index)
    (hnotle : ¬ L ≤ H) : LeanEval.GroupTheory.Defs.IsStronglyEmbedded ((H ⊓ L).subgroupOf L) := by
  -- `H ⊓ L ≠ L`, because `H ⊓ L = L` says exactly `L ≤ H`.
  have hne : H ⊓ L ≠ L := fun h => hnotle (h ▸ inf_le_left)
  have heven : Even (Nat.card ↥(H ⊓ L)) :=
    even_card_inf_of_odd_relIndex hH.2.1 (odd_relIndex_inf_of_normal_of_odd_index hL hidx)
  exact Work.Reductions.stronglyEmbedded_subgroupOf hH hne heven

end Work.ThreePoints
