import Mathlib

namespace Work.KT

/-- Two idempotents `p q` in a complete normed ring that are close, in the sense
`‖q - p‖ * ‖2 * p - 1‖ < 1`, are conjugate by a unit: there is `u : Aˣ` with
`u * q = p * u`. The conjugating element is `u = p q + (1 - p)(1 - q) = 1 + (2p - 1)(q - p)`,
which is a unit because the second factor has norm `< 1`. -/
theorem idem_close_conj {A : Type*} [NormedRing A] [CompleteSpace A] {p q : A}
    (hp : p * p = p) (hq : q * q = q) (h : ‖q - p‖ * ‖2 * p - 1‖ < 1) :
    ∃ u : Aˣ, (u : A) * q = p * (u : A) := by
  -- The conjugating element is `z = p * q + (1 - p) * (1 - q)`, which equals `1 + (2p-1)(q-p)`.
  have hzw : p * q + (1 - p) * (1 - q) = 1 + (2 * p - 1) * (q - p) := by
    have hR : 1 + (2 * p - 1) * (q - p) = 1 + 2 * (p * q) - 2 * (p * p) - q + p := by
      noncomm_ring
    rw [hR, hp]
    have hL : p * q + (1 - p) * (1 - q) = 1 - p - q + 2 * (p * q) := by noncomm_ring
    rw [hL]
    noncomm_ring
  -- `z` intertwines `q` and `p`.
  have hzq : (p * q + (1 - p) * (1 - q)) * q = p * q := by
    have h1 : (1 - q) * q = 0 := by rw [sub_mul, one_mul, hq, sub_self]
    have h2 : (1 - p) * (1 - q) * q = 0 := by rw [mul_assoc, h1, mul_zero]
    rw [add_mul, mul_assoc p q q, hq, h2, add_zero]
  have hpz : p * (p * q + (1 - p) * (1 - q)) = p * q := by
    have h1 : p * (1 - p) = 0 := by rw [mul_sub, mul_one, hp, sub_self]
    have h2 : p * ((1 - p) * (1 - q)) = 0 := by rw [← mul_assoc, h1, zero_mul]
    rw [mul_add, ← mul_assoc p p q, hp, h2, add_zero]
  -- `1 + (2p-1)(q-p)` is a unit since its perturbation term has norm `< 1`.
  have hw : ‖(2 * p - 1) * (q - p)‖ < 1 := by
    refine lt_of_le_of_lt (norm_mul_le _ _) ?_
    rw [mul_comm]; exact h
  have hu : IsUnit (1 + (2 * p - 1) * (q - p)) := by
    have hneg : ‖-((2 * p - 1) * (q - p))‖ < 1 := by rwa [norm_neg]
    simpa using isUnit_one_sub_of_norm_lt_one hneg
  have hzu : IsUnit (p * q + (1 - p) * (1 - q)) := by rw [hzw]; exact hu
  obtain ⟨u, huval⟩ := hzu
  exact ⟨u, by rw [huval, hzq, hpz]⟩

end Work.KT
