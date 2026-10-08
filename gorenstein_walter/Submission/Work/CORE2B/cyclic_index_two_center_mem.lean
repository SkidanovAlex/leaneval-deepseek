import Mathlib

set_option linter.unusedVariables false

namespace Work.CORE2B

/-- In a finite `2`-group `S` with a cyclic subgroup `S0` of index two, the unique involution `t`
of `S0` lies in every subgroup of `S` of cardinality at least `4`.

`S0` has index two in `S`, so any `Q ≤ S` satisfies `|Q : Q ⊓ S0| ≤ 2`; for `|Q| ≥ 4` the
intersection `Q ⊓ S0` therefore has at least two elements.  As `S0` is a `2`-group, `Q ⊓ S0` has
even order and hence contains an involution, which must be `t` by uniqueness. -/
theorem cyclic_index_two_center_mem {G : Type*} [Group G] [Finite G]
    (S S0 : Subgroup G) (hS : IsPGroup 2 S) (hS0 : S0 ≤ S) (hcyc : IsCyclic ↥S0)
    (hidx : S0.relIndex S = 2) {t : G} (ht : t ∈ S0) (ht2 : orderOf t = 2)
    (huniq : ∀ x ∈ S0, orderOf x = 2 → x = t) :
    ∀ Q : Subgroup G, Q ≤ S → 4 ≤ Nat.card Q → t ∈ Q := by
  intro Q hQS hQ
  -- The relative index of `S0` inside `Q` is at most the relative index in `S`, i.e. `2`.
  have hrel : S0.relIndex Q ≤ 2 := by
    rw [← hidx]
    exact Subgroup.relIndex_le_of_le_right hQS (by rw [hidx]; norm_num)
  have hmul := Subgroup.relIndex_mul_card S0 Q
  -- Consequently `|Q| ≤ 2 * |Q ⊓ S0|`, and `|Q| ≥ 4` forces `|Q ⊓ S0| ≥ 2`.
  have hcard : 2 ≤ Nat.card ↥(S0 ⊓ Q) := by
    have h : Nat.card ↥Q ≤ 2 * Nat.card ↥(S0 ⊓ Q) := by
      rw [← hmul]
      exact Nat.mul_le_mul_right _ hrel
    omega
  -- `Q ⊓ S0` is a `2`-group, so its cardinality is even; Cauchy produces an involution.
  have hpg : IsPGroup 2 ↥(S0 ⊓ Q) := hS.to_le (le_trans inf_le_left hS0)
  have hdvd : 2 ∣ Nat.card ↥(S0 ⊓ Q) := by
    rcases hpg.card_eq_or_dvd with h | h
    · omega
    · exact h
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hgS0 : (g : G) ∈ S0 := (g.2).1
  have hgQ : (g : G) ∈ Q := (g.2).2
  have hord : orderOf (g : G) = 2 := by
    rw [Subgroup.orderOf_coe]; exact hg
  have : (g : G) = t := huniq (g : G) hgS0 hord
  rw [← this]
  exact hgQ

end Work.CORE2B
