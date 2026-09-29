import Mathlib
import Submission.Work.ANum.isqrtDefs

/-! # `isqrt` computes the integer square root

`isqrt n` (see `Submission.Work.ANum.isqrtDefs`) is the kernel-reducible base-4 digit-pair
recursion `isqAux 64 n` for `n < 2 ^ 128`, and `Nat.sqrt n` outside that range.  Here we prove
that this is honest nonsense-free: `isqrt n = Nat.sqrt n` for **every** `n : ℕ`.

The mathematical content is the classical digit-pair identity for the integer square root: with
`s = ⌊√(n/4)⌋` one has `⌊√n⌋ ∈ {2s, 2s+1}`, and `⌊√n⌋ = 2s+1` exactly when `(2s+1)² ≤ n`
(`isqAux` tests precisely this).  Iterating the identity `k` times from the base case `n < 4`
proves `isqAux k n = ⌊√n⌋` whenever `n < 4^k`; taking `k = 64` and `4^64 = 2^128` finishes. -/

namespace Work.ANum

/-- `⌊√3⌋ = 1`. -/
theorem sqrt_three : Nat.sqrt 3 = 1 := by
  have h1 : 1 ≤ Nat.sqrt 3 := by rw [Nat.le_sqrt]; norm_num
  have h2 : Nat.sqrt 3 < 2 := by rw [Nat.sqrt_lt]; norm_num
  omega

/-- On the base range `n < 4` the small-input branch of `isqAux` is already `⌊√n⌋`. -/
theorem sqrt_small {n : ℕ} (hn : n < 4) : Nat.sqrt n = (if n < 2 then n else 1) := by
  interval_cases n <;> simp [Nat.sqrt_zero, Nat.sqrt_one, sqrt_three]

/-- **Digit-pair identity.**  With `s = ⌊√(n/4)⌋`, the integer square root of `n` is `2s` or
`2s + 1`, and it is `2s + 1` exactly when `(2s+1)² ≤ n` — precisely the test performed by the
recursion `isqAux`. -/
theorem sqrt_eq_div4 (n : ℕ) :
    (if (2 * Nat.sqrt (n / 4) + 1) * (2 * Nat.sqrt (n / 4) + 1) ≤ n
        then 2 * Nat.sqrt (n / 4) + 1 else 2 * Nat.sqrt (n / 4)) = Nat.sqrt n := by
  set s := Nat.sqrt (n / 4) with hs
  -- `s² ≤ n/4 < (s+1)²`
  have hle : s * s ≤ n / 4 := by
    have h := Nat.sqrt_le' (n / 4)
    simpa [hs, pow_two] using h
  have hlt : n / 4 < (s + 1) * (s + 1) := by
    have h := Nat.lt_succ_sqrt (n / 4)
    simpa [hs, pow_two, Nat.succ_eq_add_one] using h
  -- `2s ≤ ⌊√n⌋`
  have hlow : 2 * s ≤ Nat.sqrt n := by
    rw [Nat.le_sqrt]
    have hdm := Nat.div_mul_le_self n 4
    nlinarith [hle, hdm]
  -- `⌊√n⌋ ≤ 2s+1` (equivalently `n < (2s+2)²`)
  have hhigh : Nat.sqrt n ≤ 2 * s + 1 := by
    have hkey : Nat.sqrt n < 2 * s + 2 := by
      rw [Nat.sqrt_lt']
      have hdiv4 : n / 4 + 1 ≤ (s + 1) * (s + 1) := by omega
      have h4 : 4 * (n / 4) + 4 ≤ 4 * ((s + 1) * (s + 1)) := by nlinarith [hdiv4]
      have hnn : n < 4 * (n / 4) + 4 := by
        have hdm := Nat.div_add_mod n 4
        have hmod := Nat.mod_lt n (by norm_num : 0 < 4)
        omega
      have hX : n < 4 * ((s + 1) * (s + 1)) := by omega
      nlinarith [hX]
    omega
  by_cases hc : (2 * s + 1) * (2 * s + 1) ≤ n
  · rw [if_pos hc]
    have h3 : 2 * s + 1 ≤ Nat.sqrt n := Nat.le_sqrt.mpr hc
    omega
  · rw [if_neg hc]
    have h3 : Nat.sqrt n < 2 * s + 1 := by
      rw [Nat.sqrt_lt']
      simpa [pow_two] using hc
    omega

/-- The digit-pair recursion computes `⌊√n⌋` as soon as its fuel covers the input, `n < 4^k`. -/
theorem isqAux_eq_sqrt : ∀ k n, n < 4 ^ k → isqAux k n = Nat.sqrt n
  | 0, n, h => by
      have h0 : n < 1 := by simpa using h
      have hn : n = 0 := by omega
      rw [hn]
      simp [Work.ANum.isqAux.eq_1, Nat.sqrt_zero]
  | k + 1, n, h => by
      rw [Work.ANum.isqAux.eq_2]
      by_cases h4 : n < 4
      · rw [if_pos h4]
        exact (sqrt_small h4).symm
      · rw [if_neg h4]
        have hm : n / 4 < 4 ^ k := by
          have hp : 4 ^ (k + 1) = 4 ^ k * 4 := by rw [pow_succ]
          rw [hp] at h
          exact (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 4)).mpr h
        simp only [isqAux_eq_sqrt k (n / 4) hm]
        exact sqrt_eq_div4 n

theorem isqrt_eq_sqrt (n : ℕ) : Work.ANum.isqrt n = Nat.sqrt n := by
  rw [isqrt]
  split
  · rename_i h
    have h4 : (4 : ℕ) ^ 64 = 340282366920938463463374607431768211456 := by norm_num
    exact isqAux_eq_sqrt 64 n (by rw [h4]; exact h)
  · rfl

end Work.ANum
