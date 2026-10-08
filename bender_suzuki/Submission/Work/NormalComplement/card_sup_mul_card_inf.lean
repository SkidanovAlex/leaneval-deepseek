import Mathlib
import Submission.Work.LocalPrelim.relIndex_sup_eq_relIndex_inf

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NormalComplement

/-- For `H ≤ K` in a finite group, the relative index of `H` in `K` times the order of `H` is
the order of `K`.  (This is `Subgroup.index_mul_card` applied to `H.subgroupOf K`.) -/
theorem relIndex_mul_card_of_le' {G : Type*} [Group G] {H K : Subgroup G} (h : H ≤ K) :
    H.relIndex K * Nat.card ↥H = Nat.card ↥K := by
  have h1 := Subgroup.index_mul_card (H.subgroupOf K)
  rw [show (H.subgroupOf K).index = H.relIndex K from rfl] at h1
  have hc : Nat.card ↥(H.subgroupOf K) = Nat.card ↥H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv
  rwa [hc] at h1

/-- The product formula for the join and intersection of two subgroups of a finite group, the
second of which normalizes the first: `|H ⊔ K| * |H ⊓ K| = |H| * |K|`.

Since `K` normalizes `H`, the cosets of `H` in `H ⊔ K` are in bijection with the cosets of
`H ⊓ K` in `K`; equivalently `K.relIndex (H ⊔ K) = (K ⊓ H).relIndex H`.  Multiplying the two
index/cardinality identities `K.relIndex (K ⊔ H) * |K| = |K ⊔ H|` and
`(K ⊓ H).relIndex H * |K ⊓ H| = |H|` yields the claim. -/
theorem card_sup_mul_card_inf {G : Type*} [Group G] [Finite G] {H K : Subgroup G}
    (h : K ≤ Subgroup.normalizer (H : Set G)) :
    Nat.card ↥(H ⊔ K) * Nat.card ↥(H ⊓ K) = Nat.card ↥H * Nat.card ↥K := by
  -- The two coset spaces `(H ⊔ K)/H` and `K/(H ⊓ K)` have the same size.
  have key : K.relIndex (K ⊔ H) = (K ⊓ H).relIndex H :=
    Work.LocalPrelim.relIndex_sup_eq_relIndex_inf_auxL (H := K) (W := H) h
  -- Cardinality identities from the relative index.
  have h1 : K.relIndex (K ⊔ H) * Nat.card ↥K = Nat.card ↥(K ⊔ H) :=
    relIndex_mul_card_of_le' le_sup_left
  have h2 : (K ⊓ H).relIndex H * Nat.card ↥(K ⊓ H) = Nat.card ↥H :=
    relIndex_mul_card_of_le' inf_le_right
  rw [sup_comm H K, inf_comm H K, ← h1, ← h2, key]
  ring

end Work.NormalComplement
