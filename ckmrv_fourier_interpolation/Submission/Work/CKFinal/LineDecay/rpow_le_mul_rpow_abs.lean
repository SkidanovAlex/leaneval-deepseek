import Mathlib

namespace Work.CKFinal.LineDecay

/-- If `0 < a`, `0 < b`, `0 < c` and both `a ≤ b*c` and `b ≤ a*c`, then for any real
exponent `A` we have `a^A ≤ b^A * c^|A|`.

The two hypotheses force `1 ≤ c` (multiply them and divide by `a*b > 0`), so the two
sides differ at most by the factor `c^|A| ≥ 1`.  For `A ≥ 0` the bound follows from
`a ≤ b*c` and monotonicity of `x ↦ x^A`; for `A < 0` it follows from `b ≤ a*c`, i.e.
`b/c ≤ a`, and the antitonicity of `x ↦ x^A` on the positive reals. -/
lemma rpow_le_mul_rpow_abs (a b c A : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a ≤ b * c) (hbac : b ≤ a * c) : a ^ A ≤ b ^ A * c ^ |A| := by
  by_cases hA : 0 ≤ A
  · -- Nonnegative exponent: `x ↦ x^A` is monotone, and `(b*c)^A = b^A * c^A`.
    rw [abs_of_nonneg hA]
    calc a ^ A ≤ (b * c) ^ A := Real.rpow_le_rpow (le_of_lt ha) habc hA
      _ = b ^ A * c ^ A := Real.mul_rpow (le_of_lt hb) (le_of_lt hc)
  · -- Negative exponent: `x ↦ x^A` is antitone on positive reals.
    have hAneg : A < 0 := not_le.mp hA
    rw [abs_of_neg hAneg]
    have hbc : b / c ≤ a := (div_le_iff₀ hc).mpr hbac
    have h1 : a ^ A ≤ (b / c) ^ A :=
      Real.rpow_le_rpow_of_nonpos (div_pos hb hc) hbc (le_of_lt hAneg)
    rwa [Real.div_rpow (le_of_lt hb) (le_of_lt hc), div_eq_mul_inv,
      ← Real.rpow_neg (le_of_lt hc) A] at h1

end Work.CKFinal.LineDecay
