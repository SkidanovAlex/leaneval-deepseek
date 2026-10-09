import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.CohomologicalShrinking.group

open scoped commutatorElement

/-- If `a ^ p` and `b ^ p` lie in a normal subgroup `K`, and the commutator subgroup of
`⟨a⟩` and `⟨b⟩` lies in `K`, then `(a * b) ^ p ∈ K`.

Indeed, in the quotient `P ⧸ K` the images of `a` and `b` commute (as `⁅a,b⁆ ∈ K`), and
they have `p`-th power `1`, so `(a * b) ^ p = a ^ p * b ^ p = 1` there. -/
theorem pow_mul_mem_of_commutator_mem {P : Type*} [Group P] {K : Subgroup P} [K.Normal]
    {p : ℕ} {a b : P} (ha : a ^ p ∈ K) (hb : b ^ p ∈ K)
    (hab : ⁅Subgroup.closure ({a} : Set P), Subgroup.closure ({b} : Set P)⁆ ≤ K) :
    (a * b) ^ p ∈ K := by
  have ha_mem : a ∈ Subgroup.closure ({a} : Set P) := Subgroup.subset_closure (by simp)
  have hb_mem : b ∈ Subgroup.closure ({b} : Set P) := Subgroup.subset_closure (by simp)
  have hcomm : ⁅a, b⁆ ∈ K := (Subgroup.commutator_le.mp hab) a ha_mem b hb_mem
  have h1 : (QuotientGroup.mk' K) (a ^ p) = 1 := (QuotientGroup.eq_one_iff (a ^ p)).mpr ha
  have h2 : (QuotientGroup.mk' K) (b ^ p) = 1 := (QuotientGroup.eq_one_iff (b ^ p)).mpr hb
  have hc : Commute ((QuotientGroup.mk' K) a) ((QuotientGroup.mk' K) b) :=
    commutatorElement_eq_one_iff_mul_comm.mp (by
      rw [← map_commutatorElement (QuotientGroup.mk' K) a b]
      exact (QuotientGroup.eq_one_iff ⁅a, b⁆).mpr hcomm)
  have key : (QuotientGroup.mk' K) ((a * b) ^ p) = 1 := by
    rw [map_pow, map_mul, Commute.mul_pow hc p, ← map_pow, ← map_pow, h1, h2, one_mul]
  exact (QuotientGroup.eq_one_iff ((a * b) ^ p)).mp key

end Work.CohomologicalShrinking.group
