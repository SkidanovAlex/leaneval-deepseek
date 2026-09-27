import Mathlib

namespace Work.EKLComp

/-- For any pair of integers `(m, n)`, not both zero, the pair can be written as
`(g * p, g * q)` with `g > 0` and `(p, q)` a primitive integer pair, i.e. one for which
Bezout's identity `p * s - q * r = 1` holds for suitable integers `s`, `r`. -/
theorem ekl2_primitive_bezout (m n : ℤ) (h : m ≠ 0 ∨ n ≠ 0) :
    ∃ p q r s g : ℤ, 0 < g ∧ m = g * p ∧ n = g * q ∧ p * s - q * r = 1 := by
  have hgcd : 0 < Int.gcd m n := by
    rcases h with hm | hn
    · exact Int.gcd_pos_of_ne_zero_left n hm
    · exact Int.gcd_pos_of_ne_zero_right m hn
  -- Factor out the gcd: `m = p * g`, `n = q * g`, with `gcd p q = 1` and `g > 0`.
  obtain ⟨g, p, q, hg, hcop, hm, hn⟩ := Int.exists_gcd_one' hgcd
  refine ⟨p, q, -(Int.gcdB p q), Int.gcdA p q, (g : ℤ), ?_, ?_, ?_, ?_⟩
  · exact_mod_cast hg
  · rw [hm]; ring
  · rw [hn]; ring
  -- Bezout's identity for the coprime pair `(p, q)`.
  · have hbez := Int.gcd_eq_gcd_ab p q
    rw [hcop] at hbez
    simp only [Nat.cast_one] at hbez
    nlinarith [hbez]

end Work.EKLComp
