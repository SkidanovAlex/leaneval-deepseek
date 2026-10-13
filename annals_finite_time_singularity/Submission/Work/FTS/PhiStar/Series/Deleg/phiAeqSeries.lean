/-
# `phiAeqSeries` — `𝒜φ` in its series/powers-of-`1/(1+z)` form

`VocabO.phiA α z = α z² φ''(z) + (5+α) z φ'(z)` with `φ(z) = 2z/(1+z)²`.  Writing
`s = 1 + z` and expanding (`z = s - 1`) gives the polynomial identity in `1/s`

`phiA α z = (2α-10)/s + (30-14α)/s² + (24α-20)/s³ - 12α/s⁴`,

which is exactly the `k = 0` instance of `phiAseries α k` (`phiAseries α 0` is the sum of
the four `phiAcoef α n · (1+z)^{-(n+1)}`; the product over `Finset.range 0` is `1`).

The computation rests on `Work.FTS.PhiStar.phiA_eq` (the explicit rational form of `phiA`)
and is finished by `norm_num` (which evaluates the integer exponents of the `zpow`-terms
and the four coefficient patterns) and `field_simp`.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring.RingNF
import Submission.Work.FTS.PhiStar.Basic
import Submission.Work.FTS.PhiStar.Series.Deleg.phiASeriesDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Series.Deleg

/-- `phiAseries α 0` is the four-term partial-fraction expression of `𝒜φ`. -/
lemma phiAseries_zero (α z : ℝ) :
    phiAseries α 0 z = (2 * α - 10) / (1 + z) + (30 - 14 * α) / (1 + z) ^ 2
      + (24 * α - 20) / (1 + z) ^ 3 + (-12 * α) / (1 + z) ^ 4 := by
  simp only [phiAseries, Finset.prod_range_zero, Finset.sum_range_succ, Finset.sum_range_zero,
    phiAcoef, mul_one]
  norm_num
  field_simp

/-- The explicit rational form of `phiA` (`Work.FTS.PhiStar.phiA_eq`) reassociated as a
sum of the four powers of `1/(1+z)`. -/
lemma phiA_rational_eq (α z : ℝ) :
    4 * α * z ^ 2 * (z - 2) / (1 + z) ^ 4 + 2 * (5 + α) * z * (1 - z) / (1 + z) ^ 3
      = (2 * α - 10) / (1 + z) + (30 - 14 * α) / (1 + z) ^ 2
        + (24 * α - 20) / (1 + z) ^ 3 + (-12 * α) / (1 + z) ^ 4 := by
  field_simp
  ring

theorem phiAeqSeries (α z : ℝ) (hz : z ≠ -1) :
    Work.FTS.VocabO.phiA α z = Work.FTS.PhiStar.Series.Deleg.phiAseries α 0 z := by
  rw [phiAseries_zero, ← phiA_rational_eq, Work.FTS.PhiStar.phiA_eq α z hz]

end Work.FTS.PhiStar.Series.Deleg
