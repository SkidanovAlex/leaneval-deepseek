import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Coherence

theorem inv_eq_conj_of_pow_eq_one {z : ℂ} {n : ℕ} (hn : n ≠ 0) (hz : z ^ n = 1) :
    z⁻¹ = starRingEnd ℂ z := by
  have hnorm : ‖z‖ = 1 := by
    have h1 : ‖z ^ n‖ = 1 := by rw [hz, norm_one]
    rw [norm_pow] at h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg z) hn).mp h1
  exact Complex.inv_eq_conj hnorm

end Work.Coherence
