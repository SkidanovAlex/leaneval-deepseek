import Mathlib

namespace Work.WilVP

theorem natCastMulInvLtInv {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (K₀ N : ℕ) :
    (K₀ : K) * (((K₀ * (N + 1) : ℕ) : K) + 1)⁻¹ < ((N : K) + 1)⁻¹ := by
  have hb : (0 : K) < ((K₀ * (N + 1) : ℕ) : K) + 1 := by positivity
  have hc : (0 : K) < (N : K) + 1 := by positivity
  have hcast : ((K₀ * (N + 1) : ℕ) : K) = (K₀ : K) * ((N : K) + 1) := by
    push_cast; ring
  rw [← div_eq_mul_inv, ← one_div, div_lt_div_iff₀ hb hc, one_mul, hcast]
  exact lt_add_one _

end Work.WilVP
