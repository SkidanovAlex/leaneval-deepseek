import Mathlib

namespace Work.BG

/-- **KEY-SMALL, parity leaf.**

An odd integer other than `-1` is either `1` or has absolute value at least `3`.
(Equivalently: the only odd integers with `|x| ≤ 1` are `1` and `-1`.) -/
theorem keySmallOdd (x : ℤ) (hx : Odd x) (h : x ≠ -1) : x = 1 ∨ 3 ≤ |x| := by
  obtain ⟨m, hm⟩ := hx
  rw [hm] at h ⊢
  rcases lt_or_ge m 0 with hm0 | hm0
  · right
    rw [abs_of_nonpos (by omega : 2 * m + 1 ≤ 0)]
    omega
  · rcases eq_or_lt_of_le hm0 with h0 | h0
    · left; omega
    · right
      rw [abs_of_nonneg (by omega : (0 : ℤ) ≤ 2 * m + 1)]
      omega

end Work.BG
