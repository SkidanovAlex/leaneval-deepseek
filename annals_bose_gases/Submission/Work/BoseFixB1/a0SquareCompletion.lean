import Mathlib.Algebra.Order.Star.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1.a0SquareCompletion` — the scalar core of FS's completion of squares

FS's proof of `lm:appinteractionestimate` (`Papers/fournais_solovej/final_v2.tex` l.3726–3740)
factors the number operator exactly,

    n₀ − μV = (n₀^{1/2} + (μV)^{1/2})·(n₀^{1/2} − (μV)^{1/2}) ,

and then applies AM–GM **per eigenvalue** `t` of `n₀` (with `m = μV` and the two vector norms
`x, y`), which reduces the whole step to the elementary scalar inequalities collected here.

The key identity is

    2·x·y·(t − m) + (t + m)·(x² + y²) = t·(x + y)² + m·(x − y)²   ≥ 0     (t, m ≥ 0) ,

and the `√`-weighted forms follow by writing `t − m = (√t+√m)(√t−√m)` and applying the standard
AM–GM (`(a+b)² ≥ 0`, resp. `(2a + b/2)² ≥ 0`).

These are the scalar atoms consumed by any eigenvalue-wise proof of the rung-4 crux
`Work.BoseFixB1S.boxCrossJoint` — see `FINDING_boxCrossJoint_route.md` §2.
-/

noncomputable section

open scoped Real

namespace Work.BoseFixB1

/-- **The square completion, unweighted form.**  For `t, m ≥ 0` and reals `x, y`,
`2xy(t−m) + (t+m)(x²+y²) = t(x+y)² + m(x−y)²`. -/
theorem two_mul_mul_sub_add (t m x y : ℝ) :
    2 * x * y * (t - m) + (t + m) * (x ^ 2 + y ^ 2) = t * (x + y) ^ 2 + m * (x - y) ^ 2 := by
  ring

/-- **FS's square completion in the form used in the proof** (`t, m ≥ 0`):
`2xy(t−m) ≥ −(t+m)(x²+y²)`. -/
theorem two_mul_mul_sub_ge (t m x y : ℝ) (ht : 0 ≤ t) (hm : 0 ≤ m) :
    2 * x * y * (t - m) ≥ -(t + m) * (x ^ 2 + y ^ 2) := by
  have h := two_mul_mul_sub_add t m x y
  nlinarith [h, mul_nonneg ht (sq_nonneg (x + y)), mul_nonneg hm (sq_nonneg (x - y))]

/-- `(√t+√m)(√t−√m) = t − m` for `t, m ≥ 0`. -/
theorem sqrt_add_mul_sqrt_sub (t m : ℝ) (ht : 0 ≤ t) (hm : 0 ≤ m) :
    (Real.sqrt t + Real.sqrt m) * (Real.sqrt t - Real.sqrt m) = t - m := by
  have h1 : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht
  have h2 : Real.sqrt m ^ 2 = m := Real.sq_sqrt hm
  have hexp : (Real.sqrt t + Real.sqrt m) * (Real.sqrt t - Real.sqrt m)
      = Real.sqrt t ^ 2 - Real.sqrt m ^ 2 := by ring
  rw [hexp, h1, h2]

/-- **FS's square completion, `√`-weighted (symmetric) form** (`t, m ≥ 0`):
`2xy(t−m) ≥ −(√t+√m)²x² − (√t−√m)²y²`. -/
theorem two_mul_mul_sub_ge_sqrt (t m x y : ℝ) (ht : 0 ≤ t) (hm : 0 ≤ m) :
    2 * x * y * (t - m)
      ≥ -(Real.sqrt t + Real.sqrt m) ^ 2 * x ^ 2
        - (Real.sqrt t - Real.sqrt m) ^ 2 * y ^ 2 := by
  have hfac := sqrt_add_mul_sqrt_sub t m ht hm
  have hstep : 2 * x * y * (t - m)
      = 2 * ((Real.sqrt t + Real.sqrt m) * x) * ((Real.sqrt t - Real.sqrt m) * y) := by
    rw [← hfac]; ring
  rw [hstep]
  nlinarith [sq_nonneg (((Real.sqrt t + Real.sqrt m) * x)
    + ((Real.sqrt t - Real.sqrt m) * y))]

/-- **FS's square completion in the asymmetric (`λ = 4`) form actually used** (`t, m ≥ 0`):
`2xy(t−m) ≥ −4(√t+√m)²x² − ¼(√t−√m)²y²`.  This is the shape of the two terms of FS l.3730
(the `Q`-side with the coefficient `4|B|⁻¹` and the `P`-side with `¼|B|⁻¹`). -/
theorem two_mul_mul_sub_ge_sqrt_four (t m x y : ℝ) (ht : 0 ≤ t) (hm : 0 ≤ m) :
    2 * x * y * (t - m)
      ≥ -4 * (Real.sqrt t + Real.sqrt m) ^ 2 * x ^ 2
        - (1 / 4) * (Real.sqrt t - Real.sqrt m) ^ 2 * y ^ 2 := by
  have hfac := sqrt_add_mul_sqrt_sub t m ht hm
  have hstep : 2 * x * y * (t - m)
      = 2 * ((Real.sqrt t + Real.sqrt m) * x) * ((Real.sqrt t - Real.sqrt m) * y) := by
    rw [← hfac]; ring
  rw [hstep]
  nlinarith [sq_nonneg (2 * ((Real.sqrt t + Real.sqrt m) * x)
    + (1 / 2) * ((Real.sqrt t - Real.sqrt m) * y))]

end Work.BoseFixB1
