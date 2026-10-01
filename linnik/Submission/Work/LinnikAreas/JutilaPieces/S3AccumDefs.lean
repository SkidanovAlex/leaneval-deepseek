import Mathlib
import Submission.Work.ZeroDensity.Jutila.Bz3Defs
import Submission.Work.LinnikAreas.Density4.BzS3.S3GAuxDefs

/-!
# Shared vocabulary for the elementary `S₃` floor-vs-continuous bound

The target `Work.LinnikAreas.JutilaPieces.S3RouteAccumB` bounds `|s3exact z N − s3cont z N|`
by `C·N`.  The proof is elementary: the pointwise bracket estimate `s3floor_pointwise` controls
each summand difference by `6·(1+log(x/r))·(1+log(x/t))` with `x = N/(q z)`, and the resulting
double sum factors as `(Σ_r (1+log(x/r)))²`, which is `O(x²)`; the `q`-sum of `x² = N²/(q²z²)`
converges, and `N²/z² ≤ N` because `N < z²`.

This file fixes the two summands `s3sumE`, `s3sumC` (verbatim copies of the summands of
`s3exact`/`s3cont`, so the identifications are `rfl`), the cut-off `s3xq z N q = N/(q z)` and the
inner factorisation weight `s3S`.
-/

namespace Work.LinnikAreas.JutilaPieces

open Finset

noncomputable section

/-- The summand of `Work.ZeroDensity.Jutila.s3exact` (verbatim). -/
def s3sumE (z N q r t : ℕ) : ℝ :=
  (if Nat.Coprime r t then
      (ArithmeticFunction.moebius r : ℝ) * (ArithmeticFunction.moebius t : ℝ) else 0) *
    (LinnikAreas.Density4.BzS3.s3c (r * t) * ((N / (q * r * t) : ℕ) : ℝ) *
      ((Real.log (((N / (q * r * t) : ℕ) : ℝ) * (t : ℝ) / (z : ℝ)) - 1) *
          (Real.log (((N / (q * r * t) : ℕ) : ℝ) * (r : ℝ) / (z : ℝ)) - 1) + 1))

/-- The summand of `Work.ZeroDensity.Jutila.s3cont` (verbatim). -/
def s3sumC (z N q r t : ℕ) : ℝ :=
  (if Nat.Coprime r t then
      (ArithmeticFunction.moebius r : ℝ) * (ArithmeticFunction.moebius t : ℝ) else 0) *
    (LinnikAreas.Density4.BzS3.s3c (r * t) * ((N : ℝ) / ((q : ℝ) * (r : ℝ) * (t : ℝ))) *
      ((Real.log (((N : ℝ) / ((q : ℝ) * (r : ℝ) * (t : ℝ))) * (t : ℝ) / (z : ℝ)) - 1) *
          (Real.log (((N : ℝ) / ((q : ℝ) * (r : ℝ) * (t : ℝ))) * (r : ℝ) / (z : ℝ)) - 1) + 1))

/-- `s3exact` is the triple sum of `s3sumE`. -/
lemma s3exact_eq_sum (z N : ℕ) :
    Work.ZeroDensity.Jutila.s3exact z N
      = ∑ q ∈ Finset.Icc 1 (N / z), ∑ r ∈ Finset.Icc 1 (N / (q * z)),
          ∑ t ∈ Finset.Icc 1 (N / (q * z)), s3sumE z N q r t := rfl

/-- `s3cont` is the triple sum of `s3sumC`. -/
lemma s3cont_eq_sum (z N : ℕ) :
    Work.ZeroDensity.Jutila.s3cont z N
      = ∑ q ∈ Finset.Icc 1 (N / z), ∑ r ∈ Finset.Icc 1 (N / (q * z)),
          ∑ t ∈ Finset.Icc 1 (N / (q * z)), s3sumC z N q r t := rfl

/-- The real cut-off `x_q = N/(q z)`. -/
def s3xq (z N q : ℕ) : ℝ := (N : ℝ) / ((q : ℝ) * (z : ℝ))

/-- The inner factorisation weight `Σ_{r ≤ N/(qz)} (1 + log(x_q/r))`. -/
def s3S (z N q : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 (N / (q * z)), (1 + Real.log (s3xq z N q / (r : ℝ)))

end

end Work.LinnikAreas.JutilaPieces
