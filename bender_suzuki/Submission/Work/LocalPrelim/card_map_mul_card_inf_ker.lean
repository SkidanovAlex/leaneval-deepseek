import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.LocalPrelim

/-- First isomorphism theorem, cardinality form: for a group homomorphism `f : G →* G'` and a
subgroup `K ≤ G`, the product of the cardinality of the image `K.map f` with the cardinality of
`K ⊓ f.ker` equals the cardinality of `K`. -/
theorem card_map_mul_card_inf_ker {G G' : Type*} [Group G] [Finite G] [Group G']
    (f : G →* G') (K : Subgroup G) :
    Nat.card ↥(K.map f) * Nat.card ↥(K ⊓ f.ker) = Nat.card ↥K := by
  have h1 : Nat.card ↥(f.ker.subgroupOf K) * Nat.card ↥(K.map f) = Nat.card ↥K := by
    have h := Subgroup.card_mul_index (H := f.ker.subgroupOf K)
    rw [show (f.ker.subgroupOf K).index = Nat.card ↥(K.map f)
          from Subgroup.relIndex_ker K f] at h
    exact h
  have h2 : Nat.card ↥(f.ker.subgroupOf K) = Nat.card ↥(K ⊓ f.ker) := by
    rw [← Subgroup.card_subtype K (f.ker.subgroupOf K), Subgroup.subgroupOf_map_subtype,
      inf_comm]
  rw [h2] at h1
  rw [mul_comm]
  exact h1

end Work.LocalPrelim
