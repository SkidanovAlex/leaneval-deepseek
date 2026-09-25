import Mathlib
import Submission.Commons.GroupTheory.PGroup.quotient_frattini_exponent_p

namespace Commons.GroupTheory.PGroup

/-- In a finite `p`-group, every `p`-th power lies in the Frattini subgroup.
This is the element-wise form of the fact that `G ⧸ Φ(G)` has exponent dividing `p`. -/
theorem pow_mem_frattini {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    (hG : IsPGroup p G) (g : G) : g ^ p ∈ frattini G := by
  have h := quotient_frattini_exponent_p hG (QuotientGroup.mk' (frattini G) g)
  rw [← map_pow, QuotientGroup.mk'_apply] at h
  exact (QuotientGroup.eq_one_iff (g ^ p)).mp h

end Commons.GroupTheory.PGroup
