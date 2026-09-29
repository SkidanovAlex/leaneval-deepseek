import Mathlib
import Submission.Work.Resample.auDefs

/-!
# Size of the resampling offset and copy count (paper Lemma 4.9 setup)

The extended input array of the one-dimensional windowed Gaussian resampling
(`Work.Resample.auExt`) consists of `auCop p α s` copies of the input array of length `s`,
dropped by `auOff p α s` cells.  This module bounds those two integers:

* `auOff p α s = s·⌈auM p α/s⌉ − auM p α < s` is the distance from the start of the extended
  array to the first multiple of `s` above `auM p α`; in particular it is `< s < 2^p`.
* `auCop p α s = (auOff + 2s + 2·auM)/s ≤ 4p + 3`: since `auOff ≤ s−1` and `auM p α ≤ 2p`
  (for `α² < p`), the numerator is at most `3s + 4p`, and `3s + 4p ≤ (4p+3)·s`.

These are the size hypotheses `hOff`, `hCop` used by the resampling word.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.Resample

/-- The window half-width is small compared with the truncation exponent:
`auM p α = (⌈√p⌉)·α ≤ 2p` as soon as `α² < p`. -/
theorem auOffCop_aux_auM_le (p α : ℕ) (hαp : α ^ 2 < p) : auM p α ≤ 2 * p := by
  have hαle : α ≤ Nat.sqrt p := by
    rw [Nat.le_sqrt]
    have := hαp
    rw [pow_two] at this
    omega
  simp only [auM]
  have h1 := Nat.sqrt_le p
  have h2 := Nat.sqrt_le_self p
  nlinarith [hαle, h1, h2, Nat.zero_le α, Nat.zero_le (Nat.sqrt p), Nat.zero_le p]

/-- The offset is smaller than one period: `auOff p α s = s·⌈auM/s⌉ − auM ≤ s − 1`. -/
theorem auOffCop_aux_off_le (p α s : ℕ) : auOff p α s ≤ s - 1 := by
  simp only [auOff]
  have := Nat.mul_div_le (auM p α + s - 1) s
  omega

theorem auOffCop (p α s : ℕ) (hα : 2 ≤ α) (hαp : α ^ 2 < p) (hp : 100 ≤ p) (hs : 1 ≤ s)
    (hs2p : s < 2 ^ p) :
    Work.Resample.auOff p α s < 2 ^ p ∧ Work.Resample.auCop p α s ≤ 4 * p + 3 := by
  have hM : auM p α ≤ 2 * p := auOffCop_aux_auM_le p α hαp
  have hOff : auOff p α s ≤ s - 1 := auOffCop_aux_off_le p α s
  have hOff' : auOff p α s < 2 ^ p := by omega
  have hCop : auCop p α s ≤ 4 * p + 3 := by
    rw [auCop]
    apply Nat.div_le_of_le_mul
    have h1 : auOff p α s + 2 * s + 2 * auM p α ≤ 3 * s + 4 * p := by omega
    have h2 : 3 * s + 4 * p ≤ s * (4 * p + 3) := by nlinarith
    exact le_trans h1 h2
  exact ⟨hOff', hCop⟩

end Work.Resample
