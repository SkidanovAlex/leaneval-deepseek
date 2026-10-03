import Mathlib
import Submission.Work.Analysis.Variation.DyadicGrid


namespace Work.Analysis.Variation

/-- **The level-`(k+1)` grid increment of `h` at `z` is the difference of the roundings.**

`dyadJump h (k+1) (dyadQ (k+1) z) = h (dyadPt (k+1) z) - h (dyadPt k z)` for every real `z`:
the index `m = ⌊2 ^{k+1} z⌋` is either even, in which case the two roundings agree (both equal
`m / 2^{k+1} = (m/2)/2^k`) and both sides vanish, or odd, in which case `m - 1 = 2 (m/2)` and the
jump is exactly the difference between the level-`(k+1)` and the level-`k` rounding. -/
lemma dyadJump_succ_dyadQ_eq_jump (h : ℝ → ℂ) (k : ℕ) (z : ℝ) :
    dyadJump h (k + 1) (dyadQ (k + 1) z) = h (dyadPt (k + 1) z) - h (dyadPt k z) := by
  set n := dyadQ (k + 1) z with hn
  have hpt_k : dyadPt k z = ((2 * (n / 2) : ℕ) : ℝ) / (2 : ℝ) ^ (k + 1) := by
    rw [dyadPt_eq_two_mul k z, ← dyadQ_succ_div k z, ← hn]
  have hpt_succ : dyadPt (k + 1) z = (n : ℝ) / (2 : ℝ) ^ (k + 1) := rfl
  rcases Nat.even_or_odd n with he | ho
  · rw [dyadJump_eq_zero_of_even h (k + 1) n he, hpt_succ, hpt_k,
      Nat.two_mul_div_two_of_even he]
    ring
  · rw [dyadJump_eq_of_odd h (k + 1) n ho, hpt_succ, hpt_k]
    have h2 : 2 * (n / 2) = n - 1 := by
      have hmod : n % 2 = 1 := by rw [← Nat.odd_iff]; exact ho
      have hdm := Nat.div_add_mod n 2
      omega
    have hcast : ((2 * (n / 2) : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [h2, Nat.cast_sub (by rcases ho with ⟨j, hj⟩; omega : 1 ≤ n), Nat.cast_one]
    rw [hcast]

/-- **The base case of the telescoping.**  For `z ∈ [0,1]` the level-`0` cell index `dyadQ 0 z = ⌊z⌋`
is `0` or `1`, and `dyadJump h 0 (dyadQ 0 z) = h (dyadPt 0 z) - h 0`. -/
lemma dyadJump_zero_dyadQ_eq (h : ℝ → ℂ) {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    dyadJump h 0 (dyadQ 0 z) = h (dyadPt 0 z) - h 0 := by
  have hlt : dyadQ 0 z < 2 := by
    simpa using dyadQ_lt_two_pow_add_one hz0 hz1 0
  have hcases : dyadQ 0 z = 0 ∨ dyadQ 0 z = 1 := by omega
  rcases hcases with h0 | h1
  · rw [h0, dyadJump_eq_zero_of_even h 0 0 (by norm_num : Even 0)]
    have hpt : dyadPt 0 z = 0 := by simp [dyadPt, h0]
    rw [hpt]; ring
  · rw [h1, dyadJump_eq_of_odd h 0 1 (by norm_num : Odd 1)]
    have hpt : dyadPt 0 z = 1 := by simp [dyadPt, h1]
    rw [hpt]; norm_num

/-- **The telescoping of `h` along the dyadic roundings of a single point.**

For `z ∈ [0,1]` and every `L`, `h (dyadPt L z) - h 0` is the sum of the level-`k` jumps
`dyadJump h k (dyadQ k z)` over `k ≤ L`.  Induction on `L`, with the base case
`dyadJump_zero_dyadQ_eq` and the induction step `dyadJump_succ_dyadQ_eq_jump`. -/
lemma sum_dyadJump_eq_sub (h : ℝ → ℂ) {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (L : ℕ) :
    ∑ k ∈ Finset.range (L + 1), dyadJump h k (dyadQ k z) = h (dyadPt L z) - h 0 := by
  induction L with
  | zero => simpa using dyadJump_zero_dyadQ_eq h hz0 hz1
  | succ L ih =>
    rw [Finset.sum_range_succ, ih, dyadJump_succ_dyadQ_eq_jump h L z]
    ring

/-- **The exact dyadic telescoping of `h` on `[0,1]`.**

For `h : ℝ → ℂ` and `x, y ∈ [0,1]`, the difference `h (dyadPt L y) - h (dyadPt L x)` of the
level-`L` dyadic roundings of `y` and `x` is the sum, over the levels `k ≤ L`, of the corresponding
*differences of signed grid increments* `dyadJump h k (dyadQ k ·)`.  This is the identity obtained by
telescoping the level-by-level decomposition

`h (dyadPt (k+1) z) - h (dyadPt k z) = dyadJump h (k+1) (dyadQ (k+1) z)`  (`k ≥ 0`, `z ∈ [0,1]`)

together with the base case `dyadJump h 0 (dyadQ 0 z) = h (dyadPt 0 z) - h 0`; here
`dyadQ l z = ⌊2^l z⌋` and `dyadPt l z = dyadQ l z / 2^l` are the dyadic cell index and the rounding
down of `z` (`DyadicGrid.lean`), and `dyadJump h l m = h (m/2^l) - h ((m-1)/2^l)` when `m` is odd
and `0` when `m` is even.  The hypotheses `x ≤ 1`, `y ≤ 1` are only needed for the base case
(`dyadQ 0 z ∈ {0,1}`).  The file should be in namespace `Work.Analysis.Variation` and import
`Submission.Work.Analysis.Variation.DyadicGrid`. -/
theorem dyadGridTelescope (h : ℝ → ℂ) (L : ℕ) {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    h (dyadPt L y) - h (dyadPt L x)
      = ∑ k ∈ Finset.range (L + 1),
          (dyadJump h k (dyadQ k y) - dyadJump h k (dyadQ k x)) := by
  have hy := sum_dyadJump_eq_sub h hy0 hy1 L
  have hx := sum_dyadJump_eq_sub h hx0 hx1 L
  rw [Finset.sum_sub_distrib, hy, hx]
  ring

end Work.Analysis.Variation
