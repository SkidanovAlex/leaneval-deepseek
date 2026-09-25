import Mathlib.GroupTheory.Frattini
import Submission.Commons.GroupTheory.PGroup.index_coatom_eq_prime

namespace Commons.GroupTheory.PGroup

open Subgroup

/-- In a finite `p`-group, every `p`-th power lies in the Frattini subgroup:
every maximal subgroup has index `p`, so the image of any element in the
quotient by a maximal subgroup has order dividing `p`. -/
private lemma pow_mem_frattini_of_isPGroup {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    (hG : IsPGroup p G) (g : G) : g ^ p ∈ frattini G := by
  rw [frattini, Order.radical]
  refine Subgroup.mem_iInf.mpr fun M => Subgroup.mem_iInf.mpr fun hM => ?_
  have : Group.IsNilpotent G := hG.isNilpotent
  have hMn : M.Normal :=
    Subgroup.NormalizerCondition.normal_of_coatom M
      (Group.normalizerCondition_of_isNilpotent (G := G)) hM
  have hcard : Nat.card (G ⧸ M) = p := by
    rw [← Subgroup.index_eq_card]
    exact index_coatom_eq_prime hG hM
  have h1 : ((g : G ⧸ M)) ^ p = 1 := by
    rw [← hcard]
    exact pow_card_eq_one'
  exact (QuotientGroup.eq_one_iff (g ^ p)).mp (by rw [QuotientGroup.mk_pow]; exact h1)

/-- The quotient of a finite `p`-group by its Frattini subgroup has exponent
dividing `p`; equivalently `G ⧸ Φ(G)` is an elementary abelian `p`-group. -/
theorem quotient_frattini_exponent_p {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    (hG : IsPGroup p G) (x : G ⧸ frattini G) : x ^ p = 1 := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (frattini G) x
  rw [← map_pow, QuotientGroup.mk'_apply]
  exact (QuotientGroup.eq_one_iff (g ^ p)).mpr (pow_mem_frattini_of_isPGroup hG g)

end Commons.GroupTheory.PGroup
