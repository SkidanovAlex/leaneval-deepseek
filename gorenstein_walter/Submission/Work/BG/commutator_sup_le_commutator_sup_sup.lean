import Mathlib

set_option linter.style.haveILetI false

namespace Work.BG

/-- **The commutator of a join of elementwise commuting subgroups** is contained in the join
of the commutator subgroups.

If every element of `P` commutes with every element of `Q`, then `P` and `Q` are normal in
`S := P ⊔ Q`, the two commute, and inside the group `S` the commutator of the join is the
join of the commutators:
`⁅P ⊔ Q, P ⊔ Q⁆ = ⁅P, P⁆ ⊔ ⁅Q, Q⁆` (as subgroups of `S`, hence also of `G`). -/
theorem commutator_sup_le_commutator_sup_sup {G : Type*} [Group G] (P Q : Subgroup G)
    (hcomm : ∀ p ∈ P, ∀ q ∈ Q, p * q = q * p) :
    ⁅P ⊔ Q, P ⊔ Q⁆ ≤ ⁅P, P⁆ ⊔ ⁅Q, Q⁆ := by
  -- `Q` normalizes `P` and `P` normalizes `Q`.
  have hQP : Q ≤ Subgroup.normalizer (P : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro q hq p hp
    have : q * p * q⁻¹ = p := by
      rw [← hcomm p hp q hq, mul_assoc, mul_inv_cancel, mul_one]
    rwa [this]
  have hPQ : P ≤ Subgroup.normalizer (Q : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro p hp q hq
    have : p * q * p⁻¹ = q := by
      rw [hcomm p hp q hq, mul_assoc, mul_inv_cancel, mul_one]
    rwa [this]
  -- Thus `P` and `Q` are normal in `S := P ⊔ Q`.
  have hPnorm : (P.subgroupOf (P ⊔ Q)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (H := P ⊔ Q) (N := P)
      (sup_le Subgroup.le_normalizer hQP)
  have hQnorm : (Q.subgroupOf (P ⊔ Q)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (H := P ⊔ Q) (N := Q)
      (sup_le hPQ Subgroup.le_normalizer)
  -- `P` and `Q` together generate all of `S`.
  have hsup : P.subgroupOf (P ⊔ Q) ⊔ Q.subgroupOf (P ⊔ Q) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (le_sup_left : P ≤ P ⊔ Q) (le_sup_right : Q ≤ P ⊔ Q),
      Subgroup.subgroupOf_self]
  -- `P` and `Q` commute, so their mutual commutator is trivial.
  have hPq : ⁅P.subgroupOf (P ⊔ Q), Q.subgroupOf (P ⊔ Q)⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro x hx y hy
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact Subtype.ext (hcomm (x : G) (Subgroup.mem_subgroupOf.mp hx) (y : G)
      (Subgroup.mem_subgroupOf.mp hy))
  haveI := hPnorm
  haveI := hQnorm
  haveI hsupN : (P.subgroupOf (P ⊔ Q) ⊔ Q.subgroupOf (P ⊔ Q)).Normal := by
    rw [hsup]; infer_instance
  -- Inside the group `↥(P ⊔ Q)` the commutator of `⊤` is the join of the commutators.
  have key : ⁅(⊤ : Subgroup ↥(P ⊔ Q)), ⊤⁆
      = ⁅P.subgroupOf (P ⊔ Q), P.subgroupOf (P ⊔ Q)⁆ ⊔
        ⁅Q.subgroupOf (P ⊔ Q), Q.subgroupOf (P ⊔ Q)⁆ := by
    rw [← hsup]
    rw [Subgroup.commutator_sup_right]
    rw [Subgroup.commutator_sup_left, Subgroup.commutator_sup_left]
    rw [hPq, Subgroup.commutator_comm (Q.subgroupOf (P ⊔ Q)) (P.subgroupOf (P ⊔ Q)), hPq]
    simp
  have hmain : ⁅(⊤ : Subgroup ↥(P ⊔ Q)), ⊤⁆
      ≤ ⁅P.subgroupOf (P ⊔ Q), P.subgroupOf (P ⊔ Q)⁆ ⊔
        ⁅Q.subgroupOf (P ⊔ Q), Q.subgroupOf (P ⊔ Q)⁆ := le_of_eq key
  -- Push the statement from `↥(P ⊔ Q)` back to `G` along the subtype.
  have hmap := Subgroup.map_mono (f := Subgroup.subtype (P ⊔ Q)) hmain
  rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype,
      Subgroup.map_sup, Subgroup.map_commutator, Subgroup.map_commutator,
      Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr le_sup_left, inf_eq_left.mpr le_sup_right] at hmap
  exact hmap

end Work.BG
