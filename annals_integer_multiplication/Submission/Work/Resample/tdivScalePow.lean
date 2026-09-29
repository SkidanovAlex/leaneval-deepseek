import Mathlib
import Submission.Work.Resample.auDefs
import Submission.Work.Resample.tdivScale

namespace Work.Resample

/-- Generic truncation error.  For any positive integer modulus `D`, truncating `A` at scale `D`
and rescaling by `2^{-p}` differs from `A/(D·2^p)` by at most `2^{-p}`: the discarded remainder
is `< D`, and it is divided by `D·2^p`. -/
theorem tdiv_scale_general (p : ℕ) (D : ℤ) (hD : 0 < D) (A : ℤ) :
    |(((Int.tdiv A D : ℤ)) : ℝ) / (2 : ℝ) ^ p - (A : ℝ) / ((D : ℝ) * (2 : ℝ) ^ p)|
      ≤ 1 / (2 : ℝ) ^ p := by
  have hb := Work.Fx.tdiv_abs_le_one A D hD
  have hDne : (D : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hD
  have h2p : (0 : ℝ) < (2 : ℝ) ^ p := by positivity
  have hkey : ((Int.tdiv A D : ℤ) : ℝ) / (2 : ℝ) ^ p - (A : ℝ) / ((D : ℝ) * (2 : ℝ) ^ p)
      = (((Int.tdiv A D : ℤ) : ℝ) - (A : ℝ) / (D : ℝ)) / (2 : ℝ) ^ p := by
    field_simp
  rw [hkey, abs_div, abs_of_pos h2p]
  rw [div_le_iff₀ h2p]
  simpa using hb

/-- Truncating `A` at precision `auPrec p - p + c` and then scaling by `2^{-p}` differs from
`A/2^{auPrec p + c}` by at most `2^{-p}`: the discarded remainder is `< 2^{auPrec p - p + c}`,
and the two exponents add up to `auPrec p + c`. -/
theorem tdivScalePow (p c : ℕ) (A : ℤ) :
    |(((Int.tdiv A ((2 : ℤ) ^ (Work.Resample.auPrec p - p + c)) : ℤ)) : ℝ) / (2 : ℝ) ^ p
        - (A : ℝ) / (2 : ℝ) ^ (Work.Resample.auPrec p + c)| ≤ 1 / (2 : ℝ) ^ p := by
  have h := tdiv_scale_general p ((2 : ℤ) ^ (auPrec p - p + c)) (by positivity) A
  have hcast : (((2 : ℤ) ^ (auPrec p - p + c) : ℤ) : ℝ)
      = (2 : ℝ) ^ (auPrec p - p + c) := by push_cast; ring
  rw [hcast] at h
  have hpow : (2 : ℝ) ^ (auPrec p - p + c) * (2 : ℝ) ^ p
      = (2 : ℝ) ^ (auPrec p + c) := by
    rw [← pow_add]; congr 1; simp only [auPrec]; omega
  rw [hpow] at h
  exact h

end Work.Resample
