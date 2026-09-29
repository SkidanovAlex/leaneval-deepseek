import Mathlib
import Submission.Work.Resample.auTailDefs

/-!
# The window centre `auK s t k` is within `1/2` of the exact centre `auZeta s t k`

`auK s t k = ⌊(2ks+t)/(2t)⌋ = round (ks/t)` (division rounding *up* at half-integers), while
`auZeta s t k = sk/t` is the exact real centre.  Since `(2ks+t)/(2t) = ks/t + 1/2`, the two
differ by the truncation error of the integer division by `2t`:

  `-1/2 ≤ auK s t k - auZeta s t k ≤ 1/2`,

so `auK_close` gives `|auK s t k - auZeta s t k| ≤ 1/2`, i.e. the fixed-point centre used by the
resampling word is at distance at most half a cell from the ideal centre.
-/

set_option autoImplicit false

namespace Work.Resample

theorem auK_close (s t k : ℕ) (ht : 0 < t) :
    |(auK s t k : ℝ) - auZeta s t k| ≤ 1 / 2 := by
  have htR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hD : 0 < 2 * t := by omega
  -- the two defining inequalities of the truncating division `auK s t k = (2ks+t)/(2t)`
  have h1 : auK s t k * (2 * t) ≤ 2 * k * s + t := by
    rw [auK]; exact Nat.div_mul_le_self _ _
  have h2 : 2 * k * s + t < (auK s t k + 1) * (2 * t) := by
    rw [auK]; exact (Nat.div_lt_iff_lt_mul hD).mp (Nat.lt_succ_self _)
  have h1R : ((auK s t k : ℕ) : ℝ) * (2 * t) ≤ 2 * k * s + t := by exact_mod_cast h1
  have h2R : (2 * k * s + t : ℝ) < ((auK s t k : ℕ) + 1) * (2 * t) := by exact_mod_cast h2
  rw [auZeta, abs_le]
  constructor
  · -- lower bound: `2ks + t < (A+1)·2t` ⟹ `sk/t - 1/2 < A`
    have key : (2 * ((s : ℝ) * (k : ℝ)) + (t : ℝ)) / (2 * (t : ℝ)) - 1 < (auK s t k : ℝ) := by
      rw [sub_lt_iff_lt_add, div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (t : ℝ))]
      nlinarith [h2R]
    have hkey : (2 * ((s : ℝ) * (k : ℝ)) + (t : ℝ)) / (2 * (t : ℝ)) - 1
        = (s : ℝ) * (k : ℝ) / (t : ℝ) - 1 / 2 := by
      field_simp
      try ring
    rw [hkey] at key
    linarith
  · -- upper bound: `A·2t ≤ 2ks + t` ⟹ `A ≤ sk/t + 1/2`
    have key : (auK s t k : ℝ) ≤ (2 * ((s : ℝ) * (k : ℝ)) + (t : ℝ)) / (2 * (t : ℝ)) := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (t : ℝ))]
      nlinarith [h1R]
    have hkey : (2 * ((s : ℝ) * (k : ℝ)) + (t : ℝ)) / (2 * (t : ℝ))
        = (s : ℝ) * (k : ℝ) / (t : ℝ) + 1 / 2 := by
      field_simp
      try ring_nf
    rw [hkey] at key
    linarith

end Work.Resample
