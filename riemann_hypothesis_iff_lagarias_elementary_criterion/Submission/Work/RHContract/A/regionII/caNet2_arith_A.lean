import Mathlib

namespace Work.RHContract.A.regionII

/-- One-variable arithmetic inequality for the `Net₂ ≥ 0` argument of Region II.

After clearing the (positive) denominators the goal is the polynomial inequality
`P(L) ≤ Q(L)` with
`P(L) = (1/3)(L/2 + 3/20)(9/2000)(L + 941/10000)(L/2 + 1397/10000)` and
`Q(L) = (7075/100000·L + 90181/1000000)(1488/10000·L − 483906/1000000)`.
On `[11.5, 13.8156]` the difference `Q − P` is increasing and concave, hence
bounded below by its value `Q(11.5) − P(11.5) > 0` at the left endpoint.  We
supply the corresponding Positivstellensatz certificate explicitly to
`nlinarith`, writing `t = L − 11.5`, `v = 13.8156 − L` and using the nonnegative
monomials `t`, `v`, `t²`, `t·v`, `t²·v`. -/
theorem caNet2_arith_A (L : ℝ) (h1 : (115 / 10 : ℝ) ≤ L) (h2 : L ≤ 13.8156) :
    (1 / 3) * (L / 2 + 15 / 100) * ((45 / 10000) / L) ≤
      ((7075 / 100000 * L + 90181 / 1000000) / ((L + 941 / 10000) * (L / 2 + 1397 / 10000)))
        * (1488 / 10000 - 483906 / 1000000 / L) := by
  have hL : 0 < L := by linarith
  have hden : 0 < (L + 941 / 10000) * (L / 2 + 1397 / 10000) := by positivity
  field_simp
  have ht : (0 : ℝ) ≤ L - 115 / 10 := by linarith
  have hv : (0 : ℝ) ≤ 138156 / 10000 - L := by linarith
  have ht2 : (0 : ℝ) ≤ (L - 115 / 10) ^ 2 := sq_nonneg _
  have htv : (0 : ℝ) ≤ (L - 115 / 10) ^ 2 * (138156 / 10000 - L) := mul_nonneg ht2 hv
  have htv2 : (0 : ℝ) ≤ (L - 115 / 10) * (138156 / 10000 - L) := mul_nonneg ht hv
  nlinarith [ht, hv, ht2, htv, htv2]

end Work.RHContract.A.regionII
