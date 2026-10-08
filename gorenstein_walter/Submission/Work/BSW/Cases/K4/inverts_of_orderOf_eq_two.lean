import Mathlib

namespace Work.BSW.Cases.K4

theorem inverts_of_orderOf_eq_two {G : Type} [Group G]
    (N Q : Subgroup G) (hQN : Q ≤ N) {z : G} (hzN : z ∈ N) (hzQ : z ∉ Q)
    (hz2 : ∀ w ∈ N, w ∉ Q → orderOf w = 2) :
    ∀ q ∈ Q, z * q * z⁻¹ = q⁻¹ := by
  intro q hq
  -- z lies outside Q, so by hypothesis it is an involution.
  have hzsq : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rw [hz2 z hzN hzQ, pow_two] at this
    exact this
  have hz_inv : z⁻¹ = z := inv_eq_of_mul_eq_one_left hzsq
  -- z * q stays in N and stays outside Q.
  have hzqN : z * q ∈ N := N.mul_mem hzN (hQN hq)
  have hzqQ : z * q ∉ Q := by
    intro h
    apply hzQ
    have : (z * q) * q⁻¹ ∈ Q := Q.mul_mem h (Q.inv_mem hq)
    simpa [mul_assoc] using this
  -- hence z * q is an involution: (z*q)*(z*q) = 1.
  have hsq : (z * q) * (z * q) = 1 := by
    have := pow_orderOf_eq_one (z * q)
    rw [hz2 (z * q) hzqN hzqQ, pow_two] at this
    exact this
  have hzqz : z * q * z = q⁻¹ := by
    have h1 : (z * q * z) * q = 1 := by
      simpa [mul_assoc] using hsq
    exact eq_inv_of_mul_eq_one_left h1
  calc z * q * z⁻¹ = z * q * z := by rw [hz_inv]
    _ = q⁻¹ := hzqz

end Work.BSW.Cases.K4
