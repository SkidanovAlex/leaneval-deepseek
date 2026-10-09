import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.HilbertSymbol

/-- If a prime `p` divides `x + y` and divides neither `x` nor `y`, then `y ≡ -x (mod p)`,
so multiplicativity of the Legendre symbol gives
`legendreSym p x * legendreSym p y = legendreSym p (-1)`. -/
theorem legendreSym_mul_eq_legendreSym_neg_one_of_dvd_add {p : ℕ} [Fact p.Prime] {x y : ℤ}
    (hx : ¬ (p : ℤ) ∣ x) (hy : ¬ (p : ℤ) ∣ y) (h : (p : ℤ) ∣ x + y) :
    legendreSym p x * legendreSym p y = legendreSym p (-1) := by
  -- `x` and `y` are nonzero modulo `p`
  have hx0 : ((x : ℤ) : ZMod p) ≠ 0 :=
    fun h0 => hx ((ZMod.intCast_zmod_eq_zero_iff_dvd x p).mp h0)
  have hy0 : ((y : ℤ) : ZMod p) ≠ 0 :=
    fun h0 => hy ((ZMod.intCast_zmod_eq_zero_iff_dvd y p).mp h0)
  -- `y` and `-x` agree modulo `p`
  have hyx : legendreSym p y = legendreSym p (-x) := by
    have hcast : ((y : ℤ) : ZMod p) = ((-x : ℤ) : ZMod p) := by
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
      have h2 : -x - y = -(x + y) := by ring
      rw [h2]
      exact dvd_neg.mpr h
    exact congrArg (quadraticChar (ZMod p)) hcast
  -- `legendreSym p (-x) = legendreSym p (-1) * legendreSym p x`
  have hneg : legendreSym p (-x) = legendreSym p (-1) * legendreSym p x := by
    rw [show (-x : ℤ) = (-1) * x by ring, legendreSym.mul]
  -- and `legendreSym p x ^ 2 = 1` since `x` is a unit mod `p`
  have hsq : legendreSym p x ^ 2 = 1 := legendreSym.sq_one p hx0
  calc legendreSym p x * legendreSym p y
      = legendreSym p x * legendreSym p (-x) := by rw [hyx]
    _ = legendreSym p x * (legendreSym p (-1) * legendreSym p x) := by rw [hneg]
    _ = legendreSym p (-1) := by
        rw [mul_comm (legendreSym p (-1)) (legendreSym p x), ← mul_assoc, ← sq,
          hsq, one_mul]

end Work.HilbertSymbol
