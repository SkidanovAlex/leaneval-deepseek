import Mathlib
import Submission.Work.PGroup.card_sup_mul_card_inf

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Work.PGroup

/-- For subgroups `H K` of a group `G` with `K` contained in the normalizer of `H`, the join
and the intersection satisfy `|H ⊔ K| * |H ⊓ K| = |H| * |K|`.

Since `K ≤ N_G(H)`, Noether's second isomorphism theorem gives an isomorphism
`K/(K ⊓ H) ≅ (K ⊔ H)/(K ⊓ H)`, whence the relative indices `H.relIndex K` and
`H.relIndex (H ⊔ K)` agree.  Multiplying the two Lagrange identities
`|H ⊔ K| = |H| * H.relIndex (H ⊔ K)` and `|K| = |H ⊓ K| * H.relIndex K` then yields the
claim. -/
theorem card_sup_mul_card_inf_of_le_normalizer {G : Type*} [Group G] {H K : Subgroup G}
    [Finite ↥H] [Finite ↥K] (h : K ≤ Subgroup.normalizer (H : Set G)) :
    Nat.card ↥(H ⊔ K) * Nat.card ↥(H ⊓ K) = Nat.card ↥H * Nat.card ↥K := by
  -- Lagrange in the group `↥(H ⊔ K)`: `|H ⊔ K| = |H| * H.relIndex (H ⊔ K)`.
  have hcard_H : Nat.card ↥(H ⊔ K) = Nat.card ↥H * H.relIndex (H ⊔ K) := by
    have hh := Subgroup.card_mul_index (H.subgroupOf (H ⊔ K))
    rw [← hh]
    have hc : Nat.card ↥(H.subgroupOf (H ⊔ K)) = Nat.card ↥H :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv
    rw [hc]
    rfl
  -- `↥(H.subgroupOf K)` is the intersection `H ⊓ K`.
  have hcard_sub : Nat.card ↥(H.subgroupOf K) = Nat.card ↥(H ⊓ K) := by
    rw [← Subgroup.inf_subgroupOf_right H K]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  -- Lagrange in the group `↥K`: `|K| = |H ⊓ K| * H.relIndex K`.
  have hcard_K : Nat.card ↥K = Nat.card ↥(H ⊓ K) * H.relIndex K := by
    have hh := Subgroup.card_mul_index (H.subgroupOf K)
    rw [← hh, hcard_sub]
    rfl
  -- Noether's second isomorphism theorem identifies the two relative indices.
  have hrel' : H.relIndex (K ⊔ H) = H.relIndex K := by
    haveI hn1 : (H.subgroupOf K).Normal := Subgroup.normal_subgroupOf_of_le_normalizer h
    haveI hn2 : (H.subgroupOf (K ⊔ H)).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer h
    have hc : Nat.card (↥K ⧸ H.subgroupOf K) =
        Nat.card (↥(K ⊔ H) ⧸ H.subgroupOf (K ⊔ H)) :=
      Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient K H h).toEquiv
    rw [Subgroup.relIndex, Subgroup.relIndex, Subgroup.index, Subgroup.index]
    exact hc.symm
  have hrel : H.relIndex (H ⊔ K) = H.relIndex K := by
    rw [sup_comm H K]; exact hrel'
  calc Nat.card ↥(H ⊔ K) * Nat.card ↥(H ⊓ K)
      = (Nat.card ↥H * H.relIndex (H ⊔ K)) * Nat.card ↥(H ⊓ K) := by rw [hcard_H]
    _ = (Nat.card ↥H * H.relIndex K) * Nat.card ↥(H ⊓ K) := by rw [hrel]
    _ = Nat.card ↥H * (Nat.card ↥(H ⊓ K) * H.relIndex K) := by ring
    _ = Nat.card ↥H * Nat.card ↥K := by rw [← hcard_K]

end Work.PGroup
