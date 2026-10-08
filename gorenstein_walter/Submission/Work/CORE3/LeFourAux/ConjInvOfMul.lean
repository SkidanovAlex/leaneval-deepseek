import Mathlib

namespace Work.CORE3.LeFourAux

theorem ConjInvOfMul {G : Type} [Group G] {b1 b2 h v : G}
    (hb1 : b1 * b1 = 1) (hb2 : b2 * b2 = 1)
    (hh1 : b1 * h * b1 = h⁻¹) (hh2 : b2 * h * b2 = h⁻¹) (hprod : b1 * b2 = h * v) :
    b1 * v * b1 = h * v⁻¹ * h⁻¹ ∧ b2 * v * b2 = h * v⁻¹ * h⁻¹ := by
  -- b1 and b2 are involutions, so they are their own inverses.
  have hb1inv : b1⁻¹ = b1 := inv_eq_of_mul_eq_one_right hb1
  have hb2inv : b2⁻¹ = b2 := inv_eq_of_mul_eq_one_right hb2
  -- From  b1 * b2 = h * v  we get  v = h⁻¹ * b1 * b2.
  have hv : v = h⁻¹ * b1 * b2 := by
    rw [mul_assoc, hprod, ← mul_assoc, inv_mul_cancel, one_mul]
  -- Consequently  v⁻¹ = b2 * b1 * h  (using that b1, b2 are involutions).
  have hvinv : v⁻¹ = b2 * b1 * h := by
    rw [hv, mul_inv_rev, mul_inv_rev, hb1inv, hb2inv, inv_inv]
    group
  -- Conjugation by b1 (resp. b2) inverts h; since b1, b2 are involutions,
  -- it also carries h⁻¹ back to h.
  have hconj1 : b1 * h⁻¹ * b1 = h := by
    have hh := congrArg Inv.inv hh1
    rw [mul_inv_rev, mul_inv_rev, hb1inv, inv_inv] at hh
    simpa [mul_assoc] using hh
  have hconj2 : b2 * h⁻¹ * b2 = h := by
    have hh := congrArg Inv.inv hh2
    rw [mul_inv_rev, mul_inv_rev, hb2inv, inv_inv] at hh
    simpa [mul_assoc] using hh
  have hconj2' : b2 * h⁻¹ = h * b2 := by
    have hh := congrArg (· * b2) hconj2
    rw [mul_assoc, mul_assoc, hb2, mul_one] at hh
    exact hh
  constructor
  · rw [hvinv, hv]
    rw [show b1 * (h⁻¹ * b1 * b2) * b1 = (b1 * h⁻¹ * b1) * (b2 * b1) by group, hconj1]
    group
  · rw [hvinv, hv]
    rw [show b2 * (h⁻¹ * b1 * b2) * b2 = b2 * h⁻¹ * b1 * (b2 * b2) by group, hb2, mul_one,
        hconj2']
    group

end Work.CORE3.LeFourAux
