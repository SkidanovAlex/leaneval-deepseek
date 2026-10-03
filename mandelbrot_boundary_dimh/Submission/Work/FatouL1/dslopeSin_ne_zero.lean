import Mathlib

namespace Work.FatouL1

/-- The difference slope `dslope Complex.sin 0 v = sin v / v` (with value `deriv sin 0 = 1` at
`v = 0`) is nonzero for every `v` whose real part lies in the strip `(-π, π)`.

Indeed `dslope sin 0 v = 0` can only happen if `v = 0` (where the value is `1`) or if
`sin v = 0`, i.e. `v = kπ` for some integer `k`; the bound `|v.re| < π` forces `k = 0`,
contradicting `v ≠ 0`. -/
theorem dslopeSin_ne_zero (v : ℂ) (hv : |v.re| < Real.pi) : dslope Complex.sin 0 v ≠ 0 := by
  rcases eq_or_ne v 0 with rfl | hv0
  · rw [dslope_same, Complex.deriv_sin, Complex.cos_zero]
    norm_num
  · have hsin : Complex.sin v ≠ 0 := by
      intro hs
      obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp hs
      rw [hk] at hv
      have hv' : |(k : ℝ) * Real.pi| < Real.pi := by simpa using hv
      have hv'' : |(k : ℝ)| * Real.pi < Real.pi := by
        rwa [abs_mul, abs_of_pos Real.pi_pos] at hv'
      have hk' : |(k : ℝ)| < 1 := by nlinarith [Real.pi_pos, hv'']
      have hk0 : k = 0 := by
        rcases abs_lt.mp hk' with ⟨h1, h2⟩
        have h1' : (-1 : ℤ) < k := by exact_mod_cast h1
        have h2' : k < (1 : ℤ) := by exact_mod_cast h2
        omega
      rw [hk0, Int.cast_zero, zero_mul] at hk
      exact hv0 hk
    rw [dslope_of_ne Complex.sin hv0, slope_def_field]
    apply div_ne_zero
    · simpa using hsin
    · simpa using hv0

end Work.FatouL1
