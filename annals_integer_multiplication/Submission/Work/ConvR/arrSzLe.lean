import Mathlib
import Submission.Work.ConvR.pwdefs

namespace Work.ConvR

/-- Crude polynomial upper bound for the encoding size `arrSz` of an array of `M` coefficient
vectors of length `r` in the disc of radius `1`: with `cfxSz p = 2p + 8` and
`cvecSz p r = r * cfxSz p + r + 1` and `arrSz p M r = M * cvecSz p r + M + 1`, we have
`arrSz p M r ≤ 13 * (M * r + 1) * p ^ 2` for `r, p ≥ 1`. -/
theorem arrSzLe (M r p : ℕ) (hr : 1 ≤ r) (hp : 1 ≤ p) :
    Work.ConvR.arrSz p M r ≤ 13 * (M * r + 1) * p ^ 2 := by
  have hring : arrSz p M r = M * r * (2 * p + 8) + (M * r + M + M) + 1 := by
    simp only [arrSz, cvecSz, cfxSz]; ring
  have h8 : 2 * p + 11 ≤ 13 * p ^ 2 := by nlinarith
  have hle : M + M ≤ M * r + M * r := by
    have h := Nat.mul_le_mul_left M hr
    simp at h
    omega
  calc arrSz p M r = M * r * (2 * p + 8) + (M * r + M + M) + 1 := hring
    _ ≤ M * r * (2 * p + 8) + (M * r + M * r + M * r) + 1 := by omega
    _ = M * r * (2 * p + 11) + 1 := by ring
    _ ≤ M * r * (13 * p ^ 2) + 13 * p ^ 2 := by
        have h := Nat.mul_le_mul_left (M * r) h8
        omega
    _ = 13 * (M * r + 1) * p ^ 2 := by ring

end Work.ConvR
