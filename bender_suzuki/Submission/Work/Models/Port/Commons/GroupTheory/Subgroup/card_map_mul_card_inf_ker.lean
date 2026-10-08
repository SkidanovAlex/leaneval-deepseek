import Mathlib.GroupTheory.Index

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedVariables false

namespace Commons.GroupTheory.Subgroup

/-- The cardinality of `H.subgroupOf K` equals the cardinality of `K ⊓ H`:
both are the type of elements lying in `H` and in `K`. -/
lemma card_subgroupOf_eq_card_inf {G : Type*} [Group G] (H K : Subgroup G) :
    Nat.card ↥(H.subgroupOf K) = Nat.card ↥(K ⊓ H) := by
  rw [inf_comm (a := K) (b := H)]
  rw [← Subgroup.inf_subgroupOf_right H K]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : H ⊓ K ≤ K)).toEquiv

/-- For a group homomorphism `f : G →* H` (not necessarily surjective) and a subgroup `A ≤ G`,
the product of the cardinalities of the image `A.map f` and of `A ⊓ ker f` equals the
cardinality of `A`. This is the cardinal form of the first isomorphism theorem for the
restriction of `f` to `A`. -/
theorem card_map_mul_card_inf_ker {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Surjective f) (A : Subgroup G) :
    Nat.card ↥(Subgroup.map f A) * Nat.card ↥(A ⊓ f.ker) = Nat.card ↥A := by
  have h1 : (f.ker).relIndex A = Nat.card ↥(Subgroup.map f A) := Subgroup.relIndex_ker A f
  have h2 : ((f.ker).subgroupOf A).index * Nat.card ↥((f.ker).subgroupOf A) = Nat.card ↥A :=
    Subgroup.index_mul_card _
  rw [Subgroup.relIndex] at h1
  rw [h1] at h2
  rw [card_subgroupOf_eq_card_inf f.ker A] at h2
  exact h2

end Commons.GroupTheory.Subgroup