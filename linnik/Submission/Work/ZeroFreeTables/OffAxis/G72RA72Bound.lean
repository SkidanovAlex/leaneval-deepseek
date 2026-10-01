import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.G72Base

namespace Work.ZeroFreeTables.OffAxis

/-! ## The rational part of `Re G72(-s+iσ)` is bounded by its value at `s = 0`

This is the elementary algebraic input to the large-`σ` estimate for `Isub`: for
`0 ≤ s ≤ 1` and `σ ≥ 18/5` the rational function `RA72 s σ` occurring in
`Re G72(-s+iσ)` (see `G72Base`) is at most its value at `s = 0` (namely
`RA72 0 σ = 4/σ⁴ + 4/σ⁶`, cf. `RA72_zero`), *decreased* by the negative term
`-16 s / (15 (s²+σ²))`:

    RA72 s σ ≤ -16 s/(15 (s²+σ²)) + 4/σ⁴ + 4/σ⁶ .

Equivalently `RA72 s σ + 16 s/(15 (s²+σ²)) ≤ RA72 0 σ`.

The proof is a polynomial certificate.  Writing `D = s²+σ²`, the difference of the
two sides equals `N / (D⁶ σ⁶)` with

    N = -8 σ¹⁴ s - (84σ¹⁰+40σ¹²)s² - (64/3)σ¹² s³ - 100σ¹⁰ s⁴ - 16σ¹⁰ s⁵
        - (84σ⁶+96σ⁸)s⁶ - (60σ⁴+56σ⁶)s⁸ + (8/3)σ⁶ s⁹ - (24σ²+24σ⁴)s¹⁰ - (4+4σ²)s¹²,

and the identity

    N = -(P + (8/3) σ⁶ s⁸ (1-s)),

with `P ≥ 0` the sum of the remaining monomials (all with non-negative coefficients),
makes `N ≤ 0` manifest because `0 ≤ s ≤ 1` forces `s⁸(1-s) ≥ 0`.  The hypothesis
`σ ≥ 18/5` is only used to know `σ > 0` (in fact the inequality holds for all
real `s ∈ [0,1]` and `σ > 0`). -/
theorem G72RA72Bound (s σ : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hσ : (36:ℝ)/10 ≤ σ) :
    Work.ZeroFreeTables.OffAxis.RA72 s σ
      ≤ -16*s/(15*(s^2+σ^2)) + 4/σ^4 + 4/σ^6 := by
  have hσ0 : (0:ℝ) ≤ σ := by linarith
  have hs1' : (0:ℝ) ≤ 1 - s := by linarith
  rw [Work.ZeroFreeTables.OffAxis.RA72, ← sub_nonpos]
  have hmain : (-16*s/(15*(s^2+σ^2)) - (8/3)*(3*s*σ^2 - s^3)/(s^2+σ^2)^3
        + 4*(s^4 - 6*s^2*σ^2 + σ^4)/(s^2+σ^2)^4
        - 4*(s^6 - 15*s^4*σ^2 + 15*s^2*σ^4 - σ^6)/(s^2+σ^2)^6)
        - (-16*s/(15*(s^2+σ^2)) + 4/σ^4 + 4/σ^6)
        = -(8*σ^14*s + (84*σ^10 + 40*σ^12)*s^2 + (64/3)*σ^12*s^3 + 100*σ^10*s^4
            + 16*σ^10*s^5 + (84*σ^6 + 96*σ^8)*s^6 + (60*σ^4 + (160/3)*σ^6)*s^8
            + (24*σ^2 + 24*σ^4)*s^10 + (4 + 4*σ^2)*s^12
            + (8/3)*σ^6*s^8*(1-s))
          / ((s^2+σ^2)^6 * σ^6) := by
    field_simp
    ring
  rw [hmain]
  apply div_nonpos_of_nonpos_of_nonneg
  · rw [neg_nonpos]
    positivity
  · positivity

end Work.ZeroFreeTables.OffAxis
