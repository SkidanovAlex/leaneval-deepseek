import Mathlib
import Submission.Work.CNum.SerUpDefs

namespace Work.CNum

/-- `-(((-a) / s))` is the ceiling of `a / s` for `0 < s`, and the ceiling differs from
`a / s` by less than one; hence the absolute value bound. -/
theorem ceil_div_abs_le (a s : ℤ) (hs : 0 < s) :
    |((( -Int.ediv (-a) s : ℤ)) : ℝ)| ≤ |(a:ℝ)| / (s:ℝ) + 1 := by
  have hsR : (0:ℝ) < (s:ℝ) := by exact_mod_cast hs
  have hsZ : s ≠ 0 := ne_of_gt hs
  -- `q = ⌊(-a)/s⌋`, `r = (-a) % s`, so `q * s + r = -a` with `0 ≤ r < s`.
  set t : ℝ := (a:ℝ)/(s:ℝ) with ht
  set q : ℤ := Int.ediv (-a) s with hq
  set r : ℤ := (-a) % s with hr
  have hid : q * s + r = -a := by rw [hq, hr]; exact Int.ediv_mul_add_emod (-a) s
  have hr0 : 0 ≤ r := by rw [hr]; exact Int.emod_nonneg (-a) hsZ
  have hrs : r < s := by rw [hr]; exact Int.emod_lt_of_pos (-a) hs
  have h1 : q * s ≤ -a := by linarith
  have h2 : -a < q * s + s := by linarith
  have h1R : (q:ℝ) * (s:ℝ) ≤ -(a:ℝ) := by exact_mod_cast h1
  have h2R : -(a:ℝ) < (q:ℝ) * (s:ℝ) + (s:ℝ) := by exact_mod_cast h2
  -- hence `q ≤ -t` and `-t < q + 1`, i.e. `t - 1 < -q ≤ t`
  have hqle : (q:ℝ) ≤ -t := by
    rw [ht, ← neg_div]
    exact (le_div_iff₀ hsR).mpr h1R
  have hlt : -t < (q:ℝ) + 1 := by
    rw [ht, ← neg_div, div_lt_iff₀ hsR]
    linarith
  set m : ℤ := -q with hm
  have hmR : (m:ℝ) = -(q:ℝ) := by simp [hm]
  have key : |(m:ℝ) - t| ≤ 1 := by
    rw [abs_le]
    constructor
    · linarith [hqle, hmR]
    · linarith [hlt, hmR]
  have htri : |(m:ℝ)| ≤ |t| + |(m:ℝ) - t| := by
    have h := abs_add_le t ((m:ℝ) - t)
    have hsum : t + ((m:ℝ) - t) = (m:ℝ) := by ring
    rwa [hsum] at h
  have hfin : |(m:ℝ)| ≤ |(a:ℝ)| / (s:ℝ) + 1 := by
    have h2' : |t| ≤ |(a:ℝ)| / (s:ℝ) := by rw [ht, abs_div, abs_of_pos hsR]
    linarith [htri, h2', key]
  simpa [hm, hq] using hfin

end Work.CNum
